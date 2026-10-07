//! Directed visibility-pair search through immutable saved decompositions (§3.2).
//!
//! `None` excludes intrinsic sources in the first arc, not arbitrary continuous
//! arc-to-arc visibility. Every split retains exactly one child. Lemma 2.4 is
//! represented by at most two cuts of the full current double-boundary circle;
//! local region arcs are used for shooting, never as a substitute for Lambda.
use crate::arcs::{ArcQueries, ArcQueryError, ArcShot};
use crate::boundary::{Arc, Boundary, BoundaryError, Side, Site, Slot};
use crate::curve::{Curve, LevelSource};
use crate::decomposition::Node;
use crate::geometry::{ray_order, Rational, Route};
use crate::hierarchy::{CutError, Piece, SavedChain};
use crate::input::VertexId;
use crate::submap::{ArcId, ChordId, MapError, RegionId, Submap, VisibleChord};
use crate::work::Work;
use num_traits::{One, Zero};
use std::cmp::Ordering;
use std::fmt;

#[derive(Debug)]
pub enum WitnessError {
    Query(ArcQueryError),
    Boundary(BoundaryError),
    Map(MapError),
    Cut(CutError),
    WrongRegion,
    MissingDecomposition,
    InvalidRepresentative,
    AmbiguousArrival,
    /// The separator ray has no certified parent outside first arrival.
    MissingCutArrival { separator: ChordId, source: Site },
    /// Both separator sides share the target face, contrary to Lemma 2.4.
    Unshielded { separator: ChordId },
    /// A first contact on the saved physical chain is not an old endpoint.
    SeparatorBlockedByAlpha { separator: ChordId },
    CrossingCuts { separator: ChordId },
    /// The target arc straddles a cut instead of lying in one Lambda component.
    TargetCrossesCut { separator: ChordId },
}
impl From<ArcQueryError> for WitnessError { fn from(e: ArcQueryError) -> Self { Self::Query(e) } }
impl From<BoundaryError> for WitnessError { fn from(e: BoundaryError) -> Self { Self::Boundary(e) } }
impl From<MapError> for WitnessError { fn from(e: MapError) -> Self { Self::Map(e) } }
impl From<CutError> for WitnessError { fn from(e: CutError) -> Self { Self::Cut(e) } }
impl fmt::Display for WitnessError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for WitnessError {}

/// Search only the first arc's intrinsic sources. Returned endpoints are in the
/// open interiors of the two named current arcs, in that directed order.
pub fn witness<'c, 'a>(queries: &mut ArcQueries<'c, 'a>, map: &Submap<'a>,
    region: RegionId, first: ArcId, second: ArcId, work: &mut Work)
    -> Result<Option<VisibleChord>, WitnessError>
{
    let boundary = Boundary::new(map.input(), map.chain())?;
    if first == second || map.arc_region(first)? != region || map.arc_region(second)? != region {
        return Err(WitnessError::WrongRegion);
    }
    let (start, end, full) = map.arc_sites(first).ok_or(MapError::InvalidArc)?;
    let (target_start, target_end, target_full) = map.arc_sites(second).ok_or(MapError::InvalidArc)?;
    let search = Search {
        map, boundary, region,
        first: boundary.arc(start, end, full)?,
        second: boundary.arc(target_start, target_end, target_full)?,
    };
    let mut pieces = queries.take_witness_pieces();
    let result = (|| -> Result<Option<VisibleChord>, WitnessError> {
        queries.catalogue().cut_arc(boundary, start, end, full,
            queries.max_saved_grade(), &mut pieces)?;
        for piece in &pieces {
            match piece {
                Piece::Saved { chain, side } => {
                    let saved_map = chain.oracle.map();
                    for vertex in [saved_map.chain().start, saved_map.chain().end] {
                        if let Some(chord) = search.endpoint(queries, vertex, work)? { return Ok(Some(chord)); }
                    }
                    if let Some(chord) = search.saved(queries, chain, *side, work)? { return Ok(Some(chord)); }
                }
                Piece::Edge { edge, start, end, .. } => {
                    // A clipped edge has no intrinsic interior sources. Its closed
                    // ends can still coincide with true parent-scope vertex flags.
                    for parameter in [start, end] {
                        let vertex = if parameter.is_zero() { Some(VertexId(edge.0)) }
                            else if parameter.is_one() { Some(VertexId(edge.0 + 1)) } else { None };
                        if let Some(vertex) = vertex {
                            if let Some(chord) = search.endpoint(queries, vertex, work)? { return Ok(Some(chord)); }
                        }
                    }
                }
            }
        }
        Ok(None)
    })();
    queries.recycle_witness_pieces(pieces);
    result
}

struct Search<'m, 'a> {
    map: &'m Submap<'a>,
    boundary: Boundary<'a>,
    region: RegionId,
    first: Arc<'m>,
    second: Arc<'m>,
}
struct Contact { site: Site, route: Route }

pub(crate) fn open<C: Curve>(boundary: Boundary<'_, C>, arc: &Arc<'_, C::Scalar>, site: &Site<C::Scalar>) -> bool {
    arc.full_circuit || (site != arc.start && site != arc.end && boundary.contains_site(arc, site))
}

impl<'a> Search<'_, 'a> {
    fn endpoint(&self, queries: &mut ArcQueries<'_, 'a>, vertex: VertexId, work: &mut Work)
        -> Result<Option<VisibleChord>, WitnessError>
    {
        let slots: &[Slot] = if self.boundary.is_extremum(vertex) {
            &[Slot::Incoming, Slot::Outgoing]
        } else { &[Slot::Single] };
        // Saved cap companions are not parent companions. Expand the actual
        // parent flags before testing membership or null visibility.
        for side in [Side::Left, Side::Right] {
            for &slot in slots {
                work.retained_visits += 1;
                let source = Site::Vertex { vertex, side, slot };
                if let Some(chord) = self.candidate(queries, source, LevelSource::Vertex(vertex), work)? {
                    return Ok(Some(chord));
                }
            }
        }
        Ok(None)
    }

    fn candidate(&self, queries: &mut ArcQueries<'_, 'a>, source: Site,
        level: LevelSource, work: &mut Work) -> Result<Option<VisibleChord>, WitnessError>
    {
        work.predicates += 1;
        if !open(self.boundary, &self.first, &source) { return Ok(None); }
        let Some(contact) = self.contact(queries, &source, work)? else { return Ok(None); };
        self.result(source, contact, level, work)
    }

    fn result(&self, source: Site, contact: Contact, mut level: LevelSource, work: &mut Work)
        -> Result<Option<VisibleChord>, WitnessError>
    {
        work.predicates += 2;
        if !open(self.boundary, &self.first, &source)
            || !open(self.boundary, &self.second, &contact.site) { return Ok(None); }
        if let Site::Vertex { vertex, .. } = &source { level = LevelSource::Vertex(*vertex); }
        else if let Site::Vertex { vertex, .. } = &contact.site { level = LevelSource::Vertex(*vertex); }
        self.boundary.validate_route(&source, &contact.site,
            self.boundary.direction(&source)?, contact.route)?;
        Ok(Some(VisibleChord { endpoints: [source, contact.site], route: contact.route, level }))
    }

    /// The nearest raw coordinate over ALL arcs of the current face is fixed
    /// before checking its arrival sector. A wrong-sector blocker is negative,
    /// never a reason to continue to a farther coordinate.
    fn contact(&self, queries: &mut ArcQueries<'_, 'a>, source: &Site, work: &mut Work)
        -> Result<Option<Contact>, WitnessError>
    {
        if let Some(site) = self.boundary.null_contact(source)? {
            return Ok(Some(Contact { site, route: Route::Null }));
        }
        let point = self.boundary.point(source)?;
        let direction = self.boundary.direction(source)?;
        let mut best: Option<ArcShot> = None;
        for &arc in self.map.region_arcs(self.region)? {
            work.retained_visits += 1;
            let (start, end, full) = self.map.arc_sites(arc).ok_or(MapError::InvalidArc)?;
            let Some(shot) = queries.shoot(self.boundary, start, end, full, &point, direction, work)? else { continue; };
            work.predicates += 1;
            match best.as_ref().map(|old| ray_order(&point.x, direction, &shot.x, &old.x)) {
                None | Some(Ordering::Less) => best = Some(shot),
                Some(Ordering::Equal) => {
                    let old = best.as_mut().unwrap();
                    for site in shot.into_contacts() { old.push_contact(site); }
                }
                Some(Ordering::Greater) => {}
            }
        }
        let Some(shot) = best else { return Ok(None); };
        let route = shot.route;
        let mut arrival = None;
        for site in shot.into_contacts() {
            work.predicates += 3;
            if &site == source || self.boundary.direction(&site)? != direction.opposite()
                || self.boundary.inside_null_pair(&site)? { continue; }
            if arrival.as_ref().is_some_and(|old| old != &site) { return Err(WitnessError::AmbiguousArrival); }
            arrival = Some(site);
        }
        Ok(arrival.map(|site| Contact { site, route }))
    }

    fn saved(&self, queries: &mut ArcQueries<'_, 'a>, chain: &SavedChain<'a>, side: Side, work: &mut Work)
        -> Result<Option<VisibleChord>, WitnessError>
    {
        let saved = chain.oracle.map();
        let boundary = Boundary::new(saved.input(), saved.chain())?;
        let decomposition = saved.decomposition().ok_or(WitnessError::MissingDecomposition)?;
        let cap = |vertex| Site::Vertex { vertex, side, slot: Slot::Single };
        let (c, d) = if side == Side::Left { (cap(saved.chain().start), cap(saved.chain().end)) }
            else { (cap(saved.chain().end), cap(saved.chain().start)) };
        let alpha = boundary.arc(&c, &d, false)?;
        let parent_c = self.boundary.remap_site(&boundary, &c)?;
        let parent_d = self.boundary.remap_site(&boundary, &d)?;
        let parent_alpha = self.boundary.arc(&parent_c, &parent_d, false)?;
        let mut node = decomposition.root;
        loop {
            work.decomposition_visits += 1;
            match decomposition.nodes[node] {
                Node::Region(region) => {
                    for &arc in saved.region_arcs(RegionId(region))? {
                        work.retained_visits += 1;
                        let Some((start, end, full)) = saved.arc_sites(arc) else {
                            // A chord-free saved map has exactly this one full
                            // leaf arc. Its size is certified by granularity.
                            let leaf_arc = boundary.arc(&c, &c, true)?;
                            for source in boundary.arc_occurrences(&leaf_arc) {
                                work.retained_visits += 1;
                                if !open(boundary, &alpha, &source) { continue; }
                                let parent = self.boundary.remap_site(&boundary, &source)?;
                                let Site::Vertex { vertex, .. } = &parent else { unreachable!() };
                                let level = LevelSource::Vertex(*vertex);
                                if let Some(chord) = self.candidate(queries, parent, level, work)? { return Ok(Some(chord)); }
                            }
                            continue;
                        };
                        let leaf_arc = boundary.arc(start, end, full)?;
                        for source in boundary.arc_occurrences(&leaf_arc) {
                            work.retained_visits += 1;
                            if !open(boundary, &alpha, &source) { continue; }
                            let parent = self.boundary.remap_site(&boundary, &source)?;
                            let Site::Vertex { vertex, .. } = &parent else { unreachable!() };
                            let level = LevelSource::Vertex(*vertex);
                            if let Some(chord) = self.candidate(queries, parent, level, work)? { return Ok(Some(chord)); }
                        }
                    }
                    return Ok(None);
                }
                Node::Split { chord, left, right, .. } => {
                    work.retained_visits += 1;
                    let chord = ChordId(chord);
                    let (ends, route) = saved.chord(chord)?;
                    let [a, b] = ends;
                    let level = saved.chord_level(chord)?;
                    let mut cuts: [Option<Cut>; 2] = [None, None];
                    for (index, (source, target)) in [(a, b), (b, a)].into_iter().enumerate() {
                        work.predicates += 1;
                        // Curve caps were checked in the true parent scope.
                        // They are excluded from the open candidate alpha.
                        if !open(boundary, &alpha, source) { continue; }
                        let source = self.boundary.remap_site(&boundary, source)?;
                        let contact = self.contact(queries, &source, work)?
                            .ok_or_else(|| WitnessError::MissingCutArrival { separator: chord, source: source.clone() })?;
                        work.predicates += 2;
                        if open(self.boundary, &self.first, &source)
                            && open(self.boundary, &self.second, &contact.site) {
                            return self.result(source, contact, level.clone(), work);
                        }
                        if route == Route::Null { continue; }
                        let start_point = self.boundary.point(&source)?;
                        let end_point = boundary.point(target)?;
                        let hit_point = self.boundary.point(&contact.site)?;
                        work.predicates += 1;
                        if ray_order(&start_point.x, self.boundary.direction(&source)?,
                            &hit_point.x, &end_point.x) == Ordering::Greater { continue; }
                        if open(self.boundary, &parent_alpha, &contact.site) {
                            let mapped_target = self.boundary.remap_site(&boundary, target)?;
                            if contact.site != mapped_target && contact.site != source {
                                return Err(WitnessError::SeparatorBlockedByAlpha { separator: chord });
                            }
                            continue;
                        }
                        cuts[index] = Some(Cut { source, hit: contact.site });
                    }
                    let rejected = shield(self.boundary, boundary, &alpha, &self.second,
                        a, b, &cuts, chord, work)?;
                    let child_side = |child: usize, work: &mut Work| -> Result<usize, WitnessError> {
                        work.retained_visits += 1;
                        let representative = RegionId(decomposition.nodes[child].representative());
                        let arc = *saved.region_arcs(representative)?.first()
                            .ok_or(WitnessError::InvalidRepresentative)?;
                        let (start, _, _) = saved.arc_sites(arc).ok_or(WitnessError::InvalidRepresentative)?;
                        Ok(usize::from(!interval(boundary, a, b, Marker::after(start), work)))
                    };
                    let left_side = child_side(left, work)?;
                    let right_side = child_side(right, work)?;
                    if left_side == right_side { return Err(WitnessError::InvalidRepresentative); }
                    node = if left_side == rejected { right } else { left };
                }
            }
        }
    }
}

pub(crate) struct Cut<S = Rational> { pub(crate) source: Site<S>, pub(crate) hit: Site<S> }
/// A true cyclic boundary germ, not a coordinate perturbation or an ID tie.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Germ { Incoming, At, Outgoing }
pub(crate) struct Marker<'s, S = Rational> { site: &'s Site<S>, germ: Germ }
impl<S> Copy for Marker<'_, S> {}
impl<S> Clone for Marker<'_, S> { fn clone(&self) -> Self { *self } }
impl<'s, S> Marker<'s, S> {
    fn before(site: &'s Site<S>) -> Self { Self { site, germ: Germ::Incoming } }
    pub(crate) fn after(site: &'s Site<S>) -> Self { Self { site, germ: Germ::Outgoing } }
    fn at(site: &'s Site<S>) -> Self { Self { site, germ: Germ::At } }
}
fn marker_cmp<C: Curve>(boundary: Boundary<'_, C>, a: Marker<'_, C::Scalar>, b: Marker<'_, C::Scalar>, work: &mut Work) -> Ordering {
    work.predicates += 1;
    boundary.compare_sites(a.site, b.site).then_with(|| a.germ.cmp(&b.germ))
}
/// Membership in the clockwise OPEN interval, including endpoint coincidences
/// only when the marker is its outgoing germ (a-after yes, b-after no).
pub(crate) fn interval<C: Curve>(boundary: Boundary<'_, C>, a: &Site<C::Scalar>, b: &Site<C::Scalar>, marker: Marker<'_, C::Scalar>, work: &mut Work) -> bool {
    let from = marker_cmp(boundary, Marker::at(a), marker, work) == Ordering::Less;
    let to = marker_cmp(boundary, marker, Marker::at(b), work) == Ordering::Less;
    work.predicates += 1;
    if boundary.compare_sites(a, b) == Ordering::Less { from && to } else { from || to }
}
fn signature<C: Curve>(boundary: Boundary<'_, C>, marker: Marker<'_, C::Scalar>, cuts: &[Option<Cut<C::Scalar>>; 2], work: &mut Work) -> u8 {
    let mut bits = 0;
    for (index, cut) in cuts.iter().enumerate() {
        if let Some(cut) = cut {
            if interval(boundary, &cut.source, &cut.hit, marker, work) { bits |= 1 << index; }
        }
    }
    bits
}

pub(crate) fn shield<C: Curve>(parent: Boundary<'_, C>, saved: Boundary<'_, C>, alpha: &Arc<'_, C::Scalar>, second: &Arc<'_, C::Scalar>,
    a: &Site<C::Scalar>, b: &Site<C::Scalar>, cuts: &[Option<Cut<C::Scalar>>; 2], separator: ChordId, work: &mut Work)
    -> Result<usize, WitnessError>
{
    if let [Some(first), Some(second)] = cuts {
        let source_in = interval(parent, &first.source, &first.hit, Marker::at(&second.source), work);
        let hit_in = interval(parent, &first.source, &first.hit, Marker::at(&second.hit), work);
        if first.hit != second.hit && source_in != hit_in {
            return Err(WitnessError::CrossingCuts { separator });
        }
    }
    // Split alpha at the separator endpoints into at most three open spans.
    // Keep boundary order, not numerical chord/region order.
    let mut points: [Option<&Site<C::Scalar>>; 4] = [Some(alpha.start), None, None, None];
    let mut length = 1;
    for endpoint in [a, b] {
        if open(saved, alpha, endpoint) { points[length] = Some(endpoint); length += 1; }
    }
    if length == 3 {
        work.predicates += 1;
        if saved.compare_sites(points[1].unwrap(), points[2].unwrap()) == Ordering::Greater {
            points.swap(1, 2);
        }
    }
    points[length] = Some(alpha.end);
    let target_signature = signature(parent, Marker::after(second.start), cuts, work);
    if signature(parent, Marker::before(second.end), cuts, work) != target_signature {
        return Err(WitnessError::TargetCrossesCut { separator });
    }
    let mut candidates = [false; 2];
    let mut matching = [false; 2];
    for index in 0..length {
        let start = points[index].unwrap();
        let end = points[index + 1].unwrap();
        let span = saved.arc(start, end, false)?;
        // At most the start itself and its first intrinsic successor. This is
        // an O(1) empty-candidate test, including infinitesimal null spans.
        let mut occupied = false;
        for source in saved.arc_occurrences(&span).take(2) {
            work.retained_visits += 1;
            if open(saved, &span, &source) { occupied = true; break; }
        }
        if !occupied { continue; }
        let side = usize::from(!interval(saved, a, b, Marker::after(start), work));
        candidates[side] = true;
        let parent_start = parent.remap_site(&saved, start)?;
        if signature(parent, Marker::after(&parent_start), cuts, work) == target_signature {
            matching[side] = true;
        }
    }
    if !candidates[0] { return Ok(0); }
    if !candidates[1] { return Ok(1); }
    if cuts.iter().all(Option::is_none) {
        // With no Lambda intersection, its face is the one incident on alpha's
        // first germ, even if ab has two endpoints in alpha.
        return Ok(usize::from(interval(saved, a, b, Marker::after(alpha.start), work)));
    }
    match matching {
        [false, _] => Ok(0),
        [true, false] => Ok(1),
        [true, true] => Err(WitnessError::Unshielded { separator }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::base::{full_visibility, BaseError, MAX_BASE_EDGES};
    use crate::boundary::Chain;
    use crate::geometry::Point;
    use crate::hierarchy::{Catalogue, MergeEngine};
    use crate::input::Input;

    struct BoundedGeometry;
    impl<'a> MergeEngine<'a> for BoundedGeometry {
        type Error = BaseError;
        fn base_map(&mut self, boundary: Boundary<'a>, work: &mut Work)
            -> Result<Submap<'a>, Self::Error>
        {
            assert!(boundary.chain().edge_count() <= MAX_BASE_EDGES);
            full_visibility(boundary, work)
        }
        fn merge(&mut self, left: &Submap<'a>, right: &Submap<'a>, _: usize,
            catalogue: &Catalogue<'a>, work: &mut Work) -> Result<Submap<'a>, Self::Error>
        {
            let chain = Chain::new(catalogue.input(), left.chain().start, right.chain().end).unwrap();
            assert!(chain.edge_count() <= MAX_BASE_EDGES);
            full_visibility(Boundary::new(catalogue.input(), chain).unwrap(), work)
        }
    }

    fn depth(map: &Submap<'_>) -> usize {
        let tree = map.decomposition().unwrap();
        let mut pending = vec![(tree.root, 1)];
        let mut deepest = 0;
        while let Some((node, depth)) = pending.pop() {
            deepest = deepest.max(depth);
            if let Node::Split { left, right, .. } = tree.nodes[node] {
                pending.extend([(left, depth + 1), (right, depth + 1)]);
            }
        }
        deepest
    }

    /// This reference uses the independent, hard-bounded complete visibility
    /// map, not any witness shielding or saved-map traversal.
    fn intrinsic_reference(boundary: Boundary<'_>, full: &Submap<'_>,
        first: &Arc<'_>, second: &Arc<'_>) -> bool
    {
        full.chord_ids().any(|id| {
            let (ends, _) = full.chord(id).unwrap();
            [(ends[0], ends[1]), (ends[1], ends[0])].into_iter().any(|(a, b)| {
                matches!(a, Site::Vertex { .. }) && open(boundary, first, a) && open(boundary, second, b)
            })
        })
    }

    fn legal(boundary: Boundary<'_>, first: &Arc<'_>, second: &Arc<'_>, chord: &VisibleChord) {
        let [a, b] = &chord.endpoints;
        assert!(open(boundary, first, a));
        assert!(open(boundary, second, b));
        boundary.validate_site(a).unwrap();
        boundary.validate_site(b).unwrap();
        boundary.validate_route(a, b, boundary.direction(a).unwrap(), chord.route).unwrap();
        if let Some(null) = boundary.null_contact(a).unwrap() {
            assert_eq!(null, *b);
            assert_eq!(chord.route, Route::Null);
        } else {
            let circle = boundary.arc(a, a, true).unwrap();
            let hit = boundary.nearest_contacts(&circle, a, boundary.direction(a).unwrap()).unwrap().unwrap();
            assert_eq!(hit.route, chord.route);
            assert!(hit.into_iter().any(|contact| contact.site == *b));
            assert!(!boundary.inside_null_pair(b).unwrap());
            assert_eq!(boundary.direction(b).unwrap(), boundary.direction(a).unwrap().opposite());
        }
        if let Site::Vertex { vertex, .. } = a {
            assert_eq!(chord.level, LevelSource::Vertex(*vertex));
        } else if let Site::Vertex { vertex, .. } = b {
            assert_eq!(chord.level, LevelSource::Vertex(*vertex));
        }
        assert_eq!(boundary.input().vertex(match &chord.level {
            LevelSource::Vertex(vertex) => *vertex,
            LevelSource::Frozen(_) => panic!("original saved fixture lost its intrinsic source class"),
        }).y, boundary.point(a).unwrap().y);
    }

    #[test]
    fn directed_pairs_match_bounded_visibility_and_descend_one_child() {
        let points: Vec<_> = (0..=16).map(|i| Point::integer(i,
            if i % 2 == 0 { -i - 1 } else { 40 - i })).collect();
        let input = Input::open(&points).unwrap();
        let boundary = Boundary::new(&input, Chain::new(&input, VertexId(0), VertexId(16)).unwrap()).unwrap();
        assert!(boundary.chain().edge_count() <= MAX_BASE_EDGES);
        let full = full_visibility(boundary, &mut Work::default()).unwrap();
        let catalogue = Catalogue::build(&input, 1, &mut BoundedGeometry, &mut Work::default()).unwrap();
        let mut retained = Vec::new();
        // Keep only separated inside-turn chords on one side. The central
        // region is intentionally nonconformal, with nonconsecutive arcs and a
        // wrapping arc whose cutter has both cap runs.
        for id in full.chord_ids() {
            let (ends, route) = full.chord(id).unwrap();
            if route == Route::Null && ends[0].side() == Side::Left && retained.len() < 6 {
                retained.push(VisibleChord {
                    endpoints: [ends[0].clone(), ends[1].clone()], route,
                    level: full.chord_level(id).unwrap().clone(),
                });
            }
        }
        assert!(retained.len() >= 4);
        let current = Submap::from_verified_chords(&boundary, retained, &mut Work::default()).unwrap();
        assert!(current.decomposition().is_none());
        let mut saw_wrap_arc = false;
        let mut saw_wrap_contact = false;
        let mut saw_nonconsecutive = false;
        let mut saw_positive = false;
        let mut saw_negative = false;
        let mut saw_descent = false;
        assert!(depth(catalogue.saved(4, VertexId(0)).unwrap().oracle.map()) >= 3);
        for grade in [1, 4] {
            let mut queries = ArcQueries::new(&catalogue, grade);
            for region in current.region_ids() {
                let arcs = current.region_arcs(region).unwrap();
                for (i, &first_id) in arcs.iter().enumerate() {
                    let (start, end, full_arc) = current.arc_sites(first_id).unwrap();
                    let first = boundary.arc(start, end, full_arc).unwrap();
                    saw_wrap_arc |= boundary.runs(&first).count() == 3;
                    let mut pieces = Vec::new();
                    catalogue.cut_arc(boundary, start, end, full_arc, grade, &mut pieces).unwrap();
                    let saved_pieces = pieces.iter().filter(|piece| matches!(piece, Piece::Saved { .. })).count();
                    let visit_bound: usize = pieces.iter().filter_map(|piece| match piece {
                        Piece::Saved { chain, .. } => Some(depth(chain.oracle.map())),
                        Piece::Edge { .. } => None,
                    }).sum();
                    for (j, &second_id) in arcs.iter().enumerate() {
                        if first_id == second_id { continue; }
                        saw_nonconsecutive |= arcs.len() > 3 && (i + 1) % arcs.len() != j && (j + 1) % arcs.len() != i;
                        let (start, end, full_arc) = current.arc_sites(second_id).unwrap();
                        let second = boundary.arc(start, end, full_arc).unwrap();
                        let expected = intrinsic_reference(boundary, &full, &first, &second);
                        let mut work = Work::default();
                        let result = witness(&mut queries, &current, region, first_id, second_id, &mut work).unwrap();
                        assert!(work.decomposition_visits <= visit_bound as u128,
                            "visited both children or rebuilt the saved decomposition: {work:?}");
                        saw_descent |= work.decomposition_visits > saved_pieces as u128;
                        match result {
                            Some(chord) => {
                                legal(boundary, &first, &second, &chord);
                                saw_positive = true;
                                saw_wrap_contact |= chord.route == Route::Wrap;
                                // A separator may itself supply a legal
                                // augmented source; None has the narrower
                                // intrinsic-source guarantee.
                                if matches!(chord.endpoints[0], Site::Vertex { .. }) { assert!(expected); }
                            }
                            None => { assert!(!expected); saw_negative = true; }
                        }
                    }
                }
            }
        }
        assert!(saw_wrap_arc && saw_wrap_contact && saw_nonconsecutive && saw_positive && saw_negative && saw_descent);
    }

    #[test]
    fn true_parent_cap_flags_do_not_become_saved_extremum_companions() {
        let input = Input::open(&[
            Point::integer(0, 0), Point::integer(1, 7), Point::integer(2, 1),
            Point::integer(3, 9), Point::integer(4, 2), Point::integer(5, 8),
            Point::integer(6, 3), Point::integer(7, 10), Point::integer(8, 4),
        ]).unwrap();
        let boundary = Boundary::new(&input, Chain::new(&input, VertexId(0), VertexId(8)).unwrap()).unwrap();
        assert!(boundary.chain().edge_count() <= MAX_BASE_EDGES);
        let full = full_visibility(boundary, &mut Work::default()).unwrap();
        let catalogue = Catalogue::build(&input, 1, &mut BoundedGeometry, &mut Work::default()).unwrap();
        // Removing one real chord makes exactly its true endpoints available.
        // Every retained endpoint remains excluded, even when it is a cutter
        // cap or the other flag of the same geometric vertex.
        for removed in full.chord_ids() {
            let mut chords = Vec::new();
            for id in full.chord_ids() {
                if id == removed { continue; }
                let (ends, route) = full.chord(id).unwrap();
                chords.push(VisibleChord { endpoints: [ends[0].clone(), ends[1].clone()],
                    route, level: full.chord_level(id).unwrap().clone() });
            }
            let current = Submap::from_verified_chords(&boundary, chords, &mut Work::default()).unwrap();
            for region in current.region_ids() {
                for &first_id in current.region_arcs(region).unwrap() {
                    for &second_id in current.region_arcs(region).unwrap() {
                        if first_id == second_id { continue; }
                        let (start, end, full_arc) = current.arc_sites(first_id).unwrap();
                        let first = boundary.arc(start, end, full_arc).unwrap();
                        let (start, end, full_arc) = current.arc_sites(second_id).unwrap();
                        let second = boundary.arc(start, end, full_arc).unwrap();
                        let expected = intrinsic_reference(boundary, &full, &first, &second);
                        let result = witness(&mut ArcQueries::new(&catalogue, 0), &current, region,
                            first_id, second_id, &mut Work::default()).unwrap();
                        assert_eq!(result.is_some(), expected);
                        if let Some(chord) = result {
                            legal(boundary, &first, &second, &chord);
                            let (ends, route) = full.chord(removed).unwrap();
                            assert!(ends.contains(&&chord.endpoints[0]) && ends.contains(&&chord.endpoints[1]));
                            assert_eq!(route, chord.route);
                        }
                    }
                }
            }
        }
    }
}
