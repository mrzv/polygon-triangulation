//! Saved Root services on a bounded-description symbolic programme.
//! Only clipped endpoint edges and helper edges are direct; whole alias runs
//! borrow the owning Root oracle and its immutable decomposition.
use crate::arcs::ArcShot;
use crate::base::{self, BaseError};
use crate::boundary::{Arc, Boundary, BoundaryError, Chain, Position, Side, Site, Slot};
use crate::curve::{Curve, LevelSource};
use crate::decomposition::Node;
use crate::fusion::FusionQueries;
use crate::geometry::{contact_route, ray_order, Direction, Point, Rational, Route};
use crate::hierarchy::{Catalogue, CutError, HierarchyError, Piece as RootPiece, SavedChain};
use crate::input::{EdgeId, VertexId};
use crate::merge::{MergeError, OriginalMerge, PairQueries};
use crate::oracle::OracleError;
use crate::program::{Piece, Programme};
use crate::scalar::ExactScalar;
use crate::submap::{ArcId, ChordId, MapError, RegionId, Submap, VisibleChord};
use crate::symbolic::Symbolic;
use crate::view::{OffsetProbe, ViewError};
use crate::witness::{self, Cut, Marker, WitnessError};
use crate::work::Work;
use std::cmp::Ordering;
use std::fmt;

#[derive(Debug)]
pub enum ProgrammeQueryError {
    Boundary(BoundaryError), Cut(CutError), Oracle(OracleError),
    View(ViewError), Base(BaseError), Map(MapError), Witness(WitnessError),
    Interval(HierarchyError<MergeError>), DifferentProgramme, DifferentRoot,
    InvalidAlias, SourceOutsideSavedCover { vertex: VertexId, cover: Chain },
    MissingCutArrival { separator: ChordId },
}
// A missing cut carries its separator identity, not an owned symbolic source:
// borrowed coefficient lifetimes must not be erased merely to report an error.
impl fmt::Display for ProgrammeQueryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for ProgrammeQueryError {}
impl From<BoundaryError> for ProgrammeQueryError { fn from(e: BoundaryError) -> Self { Self::Boundary(e) } }
impl From<CutError> for ProgrammeQueryError { fn from(e: CutError) -> Self { Self::Cut(e) } }
impl From<OracleError> for ProgrammeQueryError { fn from(e: OracleError) -> Self { Self::Oracle(e) } }
impl From<ViewError> for ProgrammeQueryError { fn from(e: ViewError) -> Self { Self::View(e) } }
impl From<BaseError> for ProgrammeQueryError { fn from(e: BaseError) -> Self { Self::Base(e) } }
impl From<MapError> for ProgrammeQueryError { fn from(e: MapError) -> Self { Self::Map(e) } }
impl From<WitnessError> for ProgrammeQueryError { fn from(e: WitnessError) -> Self { Self::Witness(e) } }

enum QueryPiece<'c, 'a> {
    Direct { edge: EdgeId, side: Side, start: Symbolic<'a>, end: Symbolic<'a> },
    Saved { saved: &'c SavedChain<'a>, descriptor: usize, side: Side },
}

pub struct ProgrammeQueries<'c, 'p, 'a> {
    catalogue: &'c Catalogue<'a>,
    programme: &'p Programme<'a>,
    cutoff_grade: usize,
    scratch: Vec<QueryPiece<'c, 'a>>,
    witness_scratch: Vec<QueryPiece<'c, 'a>>,
    root_scratch: Vec<RootPiece<'c, 'a>>,
}

/// Arithmetic index transport for a whole-vertex subinterval of one alias.
struct Lift<'p, 'a> {
    programme: &'p Programme<'a>, descriptor: usize, root: Chain,
}
impl<'p, 'a> Lift<'p, 'a> {
    fn metadata(&self) -> (usize, EdgeId, bool, Chain) {
        let (piece, chain) = self.programme.piece(self.descriptor);
        let Piece::Alias { view, first, reverse, .. } = piece else { unreachable!() };
        (*view, *first, *reverse, chain)
    }
    fn vertex(&self, vertex: VertexId) -> Result<VertexId, ProgrammeQueryError> {
        if vertex.0 < self.root.start.0 || vertex.0 > self.root.end.0 {
            return Err(ProgrammeQueryError::SourceOutsideSavedCover { vertex, cover: self.root });
        }
        let (_, first, reverse, chain) = self.metadata();
        let offset = if reverse { (first.0 + 1).checked_sub(vertex.0) }
            else { vertex.0.checked_sub(first.0) }.ok_or(ProgrammeQueryError::InvalidAlias)?;
        let mapped = VertexId(chain.start.0 + offset);
        if mapped.0 > chain.end.0 { return Err(ProgrammeQueryError::InvalidAlias); }
        Ok(mapped)
    }
    fn chain(&self) -> Result<Chain, ProgrammeQueryError> {
        let a = self.vertex(self.root.start)?; let b = self.vertex(self.root.end)?;
        Ok(Chain { start: a.min(b), end: a.max(b) })
    }
    fn boundary(&self) -> Result<Boundary<'p, Programme<'a>>, ProgrammeQueryError> {
        Ok(Boundary::new(self.programme, self.chain()?)?)
    }
    fn level(&self, source: &LevelSource<Rational>) -> Result<LevelSource<Symbolic<'a>>, ProgrammeQueryError> {
        Ok(match source {
            LevelSource::Vertex(vertex) => LevelSource::Vertex(self.vertex(*vertex)?),
            LevelSource::Frozen(_) => LevelSource::frozen(self.programme.view(self.metadata().0).level_source(source)),
        })
    }
    fn site(&self, site: &Site<Rational>, source: &LevelSource<Rational>)
        -> Result<Site<Symbolic<'a>>, ProgrammeQueryError>
    {
        let (view, first, reverse, chain) = self.metadata();
        if let LevelSource::Vertex(vertex) = source { self.vertex(*vertex)?; }
        let lifted = self.programme.view(view).lift_site(site, source)?;
        let side = if reverse { site.side().opposite() } else { site.side() };
        let boundary = self.boundary()?;
        match lifted {
            Site::Vertex { vertex, slot, .. } => {
                let vertex = self.vertex(vertex)?;
                let slot = if !boundary.is_extremum(vertex) { Slot::Single }
                    else if reverse { match slot { Slot::Incoming => Slot::Outgoing,
                        Slot::Outgoing => Slot::Incoming, Slot::Single => return Err(ProgrammeQueryError::InvalidAlias) } }
                    else { slot };
                let mapped = Site::Vertex { vertex, side, slot };
                boundary.validate_site(&mapped)?;
                Ok(mapped)
            }
            Site::Edge { edge, t, .. } => {
                let offset = if reverse { first.0.checked_sub(edge.0) }
                    else { edge.0.checked_sub(first.0) }.ok_or(ProgrammeQueryError::InvalidAlias)?;
                let edge = EdgeId(chain.start.0 + offset);
                let alias = self.programme.alias_edge(edge).ok_or(ProgrammeQueryError::InvalidAlias)?;
                let t = t.minus(&alias.start).over(&alias.end.minus(&alias.start));
                Ok(boundary.normalize_site(&Site::Edge { edge, t, side })?)
            }
        }
    }
    fn arc_ends(&self, map: &Submap<'a>, arc: ArcId)
        -> Result<Option<(Site<Symbolic<'a>>, Site<Symbolic<'a>>, bool)>, ProgrammeQueryError>
    {
        let Some((a, b, full)) = map.arc_sites(arc) else { return Ok(None); };
        let [ea, eb] = map.arc_endpoints(arc).ok_or(MapError::InvalidArc)?;
        Ok(Some((self.site(a, map.chord_level(ea.0)?)?,
            self.site(b, map.chord_level(eb.0)?)?, full)))
    }
}

impl<'c, 'p, 'a> ProgrammeQueries<'c, 'p, 'a> {
    pub fn new(catalogue: &'c Catalogue<'a>, programme: &'p Programme<'a>, cutoff_grade: usize) -> Self {
        Self { catalogue, programme, cutoff_grade, scratch: Vec::new(),
            witness_scratch: Vec::new(), root_scratch: Vec::new() }
    }
    pub fn catalogue(&self) -> &'c Catalogue<'a> { self.catalogue }
    pub fn programme(&self) -> &'p Programme<'a> { self.programme }
    pub fn cutoff_grade(&self) -> usize { self.cutoff_grade }

    fn cut(&mut self, boundary: Boundary<'p, Programme<'a>>, arc: &Arc<'_, Symbolic<'a>>,
        pieces: &mut Vec<QueryPiece<'c, 'a>>) -> Result<(), ProgrammeQueryError>
    {
        pieces.clear();
        if !std::ptr::eq(boundary.input(), self.programme) { return Err(ProgrammeQueryError::DifferentProgramme); }
        for run in boundary.runs(arc) {
            let begin = pieces.len();
            let (low, high) = if run.side == Side::Left { (run.from, run.to) } else { (run.to, run.from) };
            let low_edge = match low { Position::Vertex(v) => v.0, Position::Edge { edge, .. } => edge.0 };
            let high_edge = match high { Position::Vertex(v) => v.0, Position::Edge { edge, .. } => edge.0 + 1 };
            for descriptor in 0..self.programme.piece_count() {
                let (piece, chain) = self.programme.piece(descriptor);
                let first = low_edge.max(chain.start.0);
                let last = high_edge.min(chain.end.0);
                if first >= last { continue; }
                let lo = match low { Position::Edge { edge, t } if edge.0 == first => t.clone(), _ => Symbolic::zero_value() };
                let hi = match high { Position::Edge { edge, t } if edge.0 + 1 == last => t.clone(), _ => Symbolic::one_value() };
                if first + 1 == last && lo >= hi { continue; }
                if let Piece::Alias { view, .. } = piece {
                    if !std::ptr::eq(self.programme.view(*view).input(), self.catalogue.input()) {
                        return Err(ProgrammeQueryError::DifferentRoot);
                    }
                    let a = self.programme.alias_edge(EdgeId(first)).unwrap();
                    let b = self.programme.alias_edge(EdgeId(last - 1)).unwrap();
                    let a_root = a.start.plus(&lo.times(&a.end.minus(&a.start)));
                    let b_root = b.start.plus(&hi.times(&b.end.minus(&b.start)));
                    let whole_start = if a.reverse { Symbolic::one_value() } else { Symbolic::zero_value() };
                    let whole_end = if a.reverse { Symbolic::zero_value() } else { Symbolic::one_value() };
                    let partial_first = a_root != whole_start;
                    let partial_last = b_root != whole_end;
                    if first + 1 == last && (partial_first || partial_last) {
                        pieces.push(QueryPiece::Direct { edge: EdgeId(first), side: run.side, start: lo, end: hi });
                        continue;
                    }
                    if partial_first { pieces.push(QueryPiece::Direct { edge: EdgeId(first), side: run.side,
                        start: lo, end: Symbolic::one_value() }); }
                    let whole_first = first + usize::from(partial_first);
                    let whole_last = last - usize::from(partial_last);
                    if whole_first < whole_last {
                        let a = self.programme.alias_edge(EdgeId(whole_first)).unwrap();
                        let b = self.programme.alias_edge(EdgeId(whole_last - 1)).unwrap();
                        let root_start = VertexId(a.edge.0.min(b.edge.0));
                        let root_end = VertexId(a.edge.0.max(b.edge.0) + 1);
                        let saved_begin = pieces.len();
                        let root_boundary = Boundary::new(self.catalogue.input(), Chain { start: root_start, end: root_end })?;
                        let c = Site::Vertex { vertex: root_start, side: Side::Left, slot: Slot::Single };
                        let d = Site::Vertex { vertex: root_end, side: Side::Left, slot: Slot::Single };
                        self.catalogue.cut_arc(root_boundary, &c, &d, false, self.cutoff_grade, &mut self.root_scratch)?;
                        for root_piece in &self.root_scratch {
                            let RootPiece::Saved { chain: saved, .. } = root_piece else { return Err(ProgrammeQueryError::InvalidAlias); };
                            pieces.push(QueryPiece::Saved { saved, descriptor, side: run.side });
                        }
                        if a.reverse { pieces[saved_begin..].reverse(); }
                    }
                    if partial_last { pieces.push(QueryPiece::Direct { edge: EdgeId(last - 1), side: run.side,
                        start: Symbolic::zero_value(), end: hi }); }
                } else {
                    pieces.push(QueryPiece::Direct { edge: EdgeId(first), side: run.side, start: lo, end: hi });
                }
            }
            if run.side == Side::Right { pieces[begin..].reverse(); }
        }
        Ok(())
    }

    pub fn shoot(&mut self, boundary: Boundary<'p, Programme<'a>>, start: &Site<Symbolic<'a>>,
        end: &Site<Symbolic<'a>>, full: bool, source: &Point<Symbolic<'a>>,
        direction: Direction, work: &mut Work) -> Result<Option<ArcShot<Symbolic<'a>>>, ProgrammeQueryError>
    {
        let start = boundary.normalize_site(start)?; let end = boundary.normalize_site(end)?;
        let arc = boundary.arc(&start, &end, full)?;
        let mut pieces = std::mem::take(&mut self.scratch);
        let result = (|| {
            self.cut(boundary, &arc, &mut pieces)?;
            let mut best = None;
            for endpoint in [&start, &end] {
                work.predicates += 1;
                let point = boundary.point(endpoint)?;
                if point.y == source.y { collect(boundary, &arc, endpoint, &point.x, source, direction, &mut best, work); }
            }
            for piece in &pieces {
                match piece {
                    QueryPiece::Direct { edge, side, start, end } => {
                        work.arc_edge_visits += 1; work.predicates += 1;
                        if let Some((t, x)) = self.programme.horizontal_hit(*edge, &source.y) {
                            work.predicates += 2;
                            if &t >= start && &t <= end {
                                let site = boundary.normalize_site(&Site::Edge { edge: *edge, t, side: *side })?;
                                collect(boundary, &arc, &site, &x, source, direction, &mut best, work);
                            }
                        }
                    }
                    QueryPiece::Saved { saved, descriptor, side } => {
                        let lift = Lift { programme: self.programme, descriptor: *descriptor, root: saved.oracle.map().chain() };
                        let view = self.programme.view(lift.metadata().0);
                        if let Some(hit) = saved.oracle.shoot(&OffsetProbe::new(view, source, direction), work)? {
                            let (_, first, reverse, chain) = lift.metadata();
                            let edge = EdgeId(chain.start.0 + if reverse { first.0 - hit.edge.0 } else { hit.edge.0 - first.0 });
                            let alias = self.programme.alias_edge(edge).ok_or(ProgrammeQueryError::InvalidAlias)?;
                            let t = hit.t.minus(&alias.start).over(&alias.end.minus(&alias.start));
                            let site = boundary.normalize_site(&Site::Edge { edge, t, side: *side })?;
                            collect(boundary, &arc, &site, &hit.x, source, direction, &mut best, work);
                        }
                    }
                }
            }
            Ok(best)
        })();
        pieces.clear(); self.scratch = pieces;
        result
    }

    /// Actual maps in contiguous programme order; clipped endpoint edges are
    /// separated from whole-vertex aliases before transporting retained records.
    pub fn piece_maps(&mut self, engine: &mut OriginalMerge, work: &mut Work)
        -> Result<Vec<Submap<'p, Programme<'a>>>, ProgrammeQueryError>
    {
        let mut maps = Vec::with_capacity(3 * self.programme.piece_count());
        for descriptor in 0..self.programme.piece_count() {
            let (piece, chain) = self.programme.piece(descriptor);
            if let Piece::Alias { view, .. } = piece {
                if !std::ptr::eq(self.programme.view(*view).input(), self.catalogue.input()) {
                    return Err(ProgrammeQueryError::DifferentRoot);
                }
            }
            if chain.edge_count() <= Programme::MAX_LEAF_EDGES {
                maps.push(base::full_visibility(Boundary::new(self.programme, chain)?, work)?);
                continue;
            }
            let Piece::Alias { reverse, start, end, .. } = piece else { return Err(ProgrammeQueryError::InvalidAlias); };
            let partial_first = start != &if *reverse { Symbolic::one_value() } else { Symbolic::zero_value() };
            let partial_last = end != &if *reverse { Symbolic::zero_value() } else { Symbolic::one_value() };
            let middle = Chain { start: VertexId(chain.start.0 + usize::from(partial_first)),
                end: VertexId(chain.end.0 - usize::from(partial_last)) };
            if partial_first {
                let leaf = Chain { start: chain.start, end: middle.start };
                maps.push(base::full_visibility(Boundary::new(self.programme, leaf)?, work)?);
            }
            if middle.start < middle.end {
                let boundary = Boundary::new(self.programme, middle)?;
                if middle.edge_count() <= Programme::MAX_LEAF_EDGES {
                    maps.push(base::full_visibility(boundary, work)?);
                } else {
                    let a = self.programme.alias_edge(EdgeId(middle.start.0)).unwrap();
                    let b = self.programme.alias_edge(EdgeId(middle.end.0 - 1)).unwrap();
                    let root = Chain { start: VertexId(a.edge.0.min(b.edge.0)), end: VertexId(a.edge.0.max(b.edge.0) + 1) };
                    let original = self.catalogue.interval(root.start, root.end, engine, work).map_err(ProgrammeQueryError::Interval)?;
                    let lift = Lift { programme: self.programme, descriptor, root };
                    let mut records = Vec::with_capacity(original.chord_ids().size_hint().1.unwrap_or(0));
                    for id in original.chord_ids() {
                        work.retained_visits += 1;
                        let ([a, b], route) = original.chord(id)?;
                        let source = original.chord_level(id)?;
                        records.push(VisibleChord { endpoints: [lift.site(a, source)?, lift.site(b, source)?],
                            route, level: lift.level(source)? });
                    }
                    maps.push(Submap::from_verified_chords(&boundary, records, work)?);
                }
            }
            if partial_last {
                let leaf = Chain { start: middle.end, end: chain.end };
                maps.push(base::full_visibility(Boundary::new(self.programme, leaf)?, work)?);
            }
        }
        Ok(maps)
    }
}

fn collect<'p, 'a>(boundary: Boundary<'p, Programme<'a>>, arc: &Arc<'_, Symbolic<'a>>,
    site: &Site<Symbolic<'a>>, x: &Symbolic<'a>, source: &Point<Symbolic<'a>>, direction: Direction,
    best: &mut Option<ArcShot<Symbolic<'a>>>, work: &mut Work)
{
    let mut retain = |contact: Site<Symbolic<'a>>| {
        work.predicates += 2;
        if contact != *arc.start && contact != *arc.end && !boundary.contains_site(arc, &contact) { return; }
        let order = best.as_ref().map(|old| ray_order(&source.x, direction, x, &old.x));
        if order.is_none() || order == Some(Ordering::Less) {
            *best = Some(ArcShot::new(x.clone(), contact_route(&source.x, x, direction)));
        } else if order != Some(Ordering::Equal) { return; }
        best.as_mut().unwrap().push_contact(contact);
    };
    match site {
        Site::Vertex { vertex, .. } => {
            let slots: &[Slot] = if boundary.is_extremum(*vertex) { &[Slot::Incoming, Slot::Outgoing] } else { &[Slot::Single] };
            for side in [Side::Left, Side::Right] { for &slot in slots { retain(Site::Vertex { vertex: *vertex, side, slot }); } }
        }
        Site::Edge { edge, t, .. } => {
            for side in [Side::Left, Side::Right] { retain(Site::Edge { edge: *edge, t: t.clone(), side }); }
        }
    }
}

impl<'c, 'p, 'a> FusionQueries<'p, Programme<'a>> for ProgrammeQueries<'c, 'p, 'a> {
    type Error = ProgrammeQueryError;
    fn shoot(&mut self, boundary: Boundary<'p, Programme<'a>>, start: &Site<Symbolic<'a>>,
        end: &Site<Symbolic<'a>>, full: bool, source: &Point<Symbolic<'a>>, direction: Direction,
        work: &mut Work) -> Result<Option<ArcShot<Symbolic<'a>>>, Self::Error>
    { ProgrammeQueries::shoot(self, boundary, start, end, full, source, direction, work) }
}

struct Search<'m, 'p, 'a> {
    map: &'m Submap<'p, Programme<'a>>, boundary: Boundary<'p, Programme<'a>>, region: RegionId,
    first: Arc<'m, Symbolic<'a>>, second: Arc<'m, Symbolic<'a>>,
}
struct Contact<'a> { site: Site<Symbolic<'a>>, route: Route }
impl<'m, 'p, 'a> Search<'m, 'p, 'a> {
    fn endpoint(&self, queries: &mut ProgrammeQueries<'_, 'p, 'a>, vertex: VertexId, work: &mut Work)
        -> Result<Option<VisibleChord<Symbolic<'a>>>, ProgrammeQueryError>
    {
        let slots: &[Slot] = if self.boundary.is_extremum(vertex) { &[Slot::Incoming, Slot::Outgoing] } else { &[Slot::Single] };
        for side in [Side::Left, Side::Right] { for &slot in slots {
            work.retained_visits += 1;
            let source = Site::Vertex { vertex, side, slot };
            if let Some(chord) = self.candidate(queries, source, LevelSource::Vertex(vertex), work)? { return Ok(Some(chord)); }
        } }
        Ok(None)
    }
    fn candidate(&self, queries: &mut ProgrammeQueries<'_, 'p, 'a>, source: Site<Symbolic<'a>>,
        level: LevelSource<Symbolic<'a>>, work: &mut Work)
        -> Result<Option<VisibleChord<Symbolic<'a>>>, ProgrammeQueryError>
    {
        work.predicates += 1;
        if !witness::open(self.boundary, &self.first, &source) { return Ok(None); }
        let Some(contact) = self.contact(queries, &source, work)? else { return Ok(None); };
        self.result(source, contact, level, work)
    }
    fn result(&self, source: Site<Symbolic<'a>>, contact: Contact<'a>, mut level: LevelSource<Symbolic<'a>>, work: &mut Work)
        -> Result<Option<VisibleChord<Symbolic<'a>>>, ProgrammeQueryError>
    {
        work.predicates += 2;
        if !witness::open(self.boundary, &self.first, &source) || !witness::open(self.boundary, &self.second, &contact.site) { return Ok(None); }
        if let Site::Vertex { vertex, .. } = &source { level = LevelSource::Vertex(*vertex); }
        else if let Site::Vertex { vertex, .. } = &contact.site { level = LevelSource::Vertex(*vertex); }
        self.boundary.validate_route(&source, &contact.site, self.boundary.direction(&source)?, contact.route)?;
        Ok(Some(VisibleChord { endpoints: [source, contact.site], route: contact.route, level }))
    }
    fn contact(&self, queries: &mut ProgrammeQueries<'_, 'p, 'a>, source: &Site<Symbolic<'a>>, work: &mut Work)
        -> Result<Option<Contact<'a>>, ProgrammeQueryError>
    {
        if let Some(site) = self.boundary.null_contact(source)? { return Ok(Some(Contact { site, route: Route::Null })); }
        let point = self.boundary.point(source)?; let direction = self.boundary.direction(source)?;
        let mut best: Option<ArcShot<Symbolic<'a>>> = None;
        for &arc in self.map.region_arcs(self.region)? {
            work.retained_visits += 1;
            let (start, end, full) = self.map.arc_sites(arc).ok_or(MapError::InvalidArc)?;
            let Some(shot) = queries.shoot(self.boundary, start, end, full, &point, direction, work)? else { continue; };
            work.predicates += 1;
            match best.as_ref().map(|old| ray_order(&point.x, direction, &shot.x, &old.x)) {
                None | Some(Ordering::Less) => best = Some(shot),
                Some(Ordering::Equal) => { let old = best.as_mut().unwrap(); for site in shot.into_contacts() { old.push_contact(site); } }
                Some(Ordering::Greater) => {}
            }
        }
        let Some(shot) = best else { return Ok(None); };
        let route = shot.route; let mut arrival = None;
        for site in shot.into_contacts() {
            work.predicates += 3;
            if &site == source || self.boundary.direction(&site)? != direction.opposite() || self.boundary.inside_null_pair(&site)? { continue; }
            if arrival.as_ref().is_some_and(|old| old != &site) { return Err(WitnessError::AmbiguousArrival.into()); }
            arrival = Some(site);
        }
        Ok(arrival.map(|site| Contact { site, route }))
    }
    fn saved(&self, queries: &mut ProgrammeQueries<'_, 'p, 'a>, saved: &SavedChain<'a>, descriptor: usize,
        side: Side, work: &mut Work) -> Result<Option<VisibleChord<Symbolic<'a>>>, ProgrammeQueryError>
    {
        let map = saved.oracle.map();
        let lift = Lift { programme: queries.programme, descriptor, root: map.chain() };
        let boundary = lift.boundary()?;
        let decomposition = map.decomposition().ok_or(WitnessError::MissingDecomposition)?;
        let cap = |vertex| Site::Vertex { vertex, side, slot: Slot::Single };
        let (c, d) = if side == Side::Left { (cap(boundary.chain().start), cap(boundary.chain().end)) }
            else { (cap(boundary.chain().end), cap(boundary.chain().start)) };
        let alpha = boundary.arc(&c, &d, false)?;
        let pc = self.boundary.remap_site(&boundary, &c)?; let pd = self.boundary.remap_site(&boundary, &d)?;
        let parent_alpha = self.boundary.arc(&pc, &pd, false)?;
        let mut node = decomposition.root;
        loop {
            work.decomposition_visits += 1;
            match decomposition.nodes[node] {
                Node::Region(region) => {
                    for &arc in map.region_arcs(RegionId(region))? {
                        work.retained_visits += 1;
                        let ends = lift.arc_ends(map, arc)?;
                        let (start, end, full) = ends.unwrap_or_else(|| (c.clone(), c.clone(), true));
                        let leaf = boundary.arc(&start, &end, full)?;
                        for source in boundary.arc_occurrences(&leaf) {
                            work.retained_visits += 1;
                            if !witness::open(boundary, &alpha, &source) { continue; }
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
                    let ([ra, rb], route) = map.chord(chord)?; let root_level = map.chord_level(chord)?;
                    let a = lift.site(ra, root_level)?; let b = lift.site(rb, root_level)?;
                    let level = lift.level(root_level)?;
                    let mut cuts: [Option<Cut<Symbolic<'a>>>; 2] = [None, None];
                    for (index, (source, target)) in [(&a, &b), (&b, &a)].into_iter().enumerate() {
                        work.predicates += 1;
                        if !witness::open(boundary, &alpha, source) { continue; }
                        let source = self.boundary.remap_site(&boundary, source)?;
                        let contact = self.contact(queries, &source, work)?
                            .ok_or(ProgrammeQueryError::MissingCutArrival { separator: chord })?;
                        work.predicates += 2;
                        if witness::open(self.boundary, &self.first, &source) && witness::open(self.boundary, &self.second, &contact.site) {
                            return self.result(source, contact, level.clone(), work);
                        }
                        if route == Route::Null { continue; }
                        let start_point = self.boundary.point(&source)?; let end_point = boundary.point(target)?;
                        let hit_point = self.boundary.point(&contact.site)?;
                        work.predicates += 1;
                        if ray_order(&start_point.x, self.boundary.direction(&source)?, &hit_point.x, &end_point.x) == Ordering::Greater { continue; }
                        if witness::open(self.boundary, &parent_alpha, &contact.site) {
                            let mapped_target = self.boundary.remap_site(&boundary, target)?;
                            if contact.site != mapped_target && contact.site != source {
                                return Err(WitnessError::SeparatorBlockedByAlpha { separator: chord }.into());
                            }
                            continue;
                        }
                        cuts[index] = Some(Cut { source, hit: contact.site });
                    }
                    let rejected = witness::shield(self.boundary, boundary, &alpha, &self.second, &a, &b, &cuts, chord, work)?;
                    let child_side = |child: usize, work: &mut Work| -> Result<usize, ProgrammeQueryError> {
                        work.retained_visits += 1;
                        let representative = RegionId(decomposition.nodes[child].representative());
                        let arc = *map.region_arcs(representative)?.first().ok_or(WitnessError::InvalidRepresentative)?;
                        let (start, _, _) = lift.arc_ends(map, arc)?.ok_or(WitnessError::InvalidRepresentative)?;
                        Ok(usize::from(!witness::interval(boundary, &a, &b, Marker::after(&start), work)))
                    };
                    let left_side = child_side(left, work)?; let right_side = child_side(right, work)?;
                    if left_side == right_side { return Err(WitnessError::InvalidRepresentative.into()); }
                    node = if left_side == rejected { right } else { left };
                }
            }
        }
    }
}
impl<'c, 'p, 'a> PairQueries<'p, Programme<'a>> for ProgrammeQueries<'c, 'p, 'a> {
    type Error = ProgrammeQueryError;
    fn witness(&mut self, map: &Submap<'p, Programme<'a>>, region: RegionId, first: ArcId,
        second: ArcId, work: &mut Work) -> Result<Option<VisibleChord<Symbolic<'a>>>, Self::Error>
    {
        if !std::ptr::eq(map.input(), self.programme) { return Err(ProgrammeQueryError::DifferentProgramme); }
        let boundary = Boundary::new(map.input(), map.chain())?;
        if first == second || map.arc_region(first)? != region || map.arc_region(second)? != region { return Err(WitnessError::WrongRegion.into()); }
        let (start, end, full) = map.arc_sites(first).ok_or(MapError::InvalidArc)?;
        let (ts, te, tf) = map.arc_sites(second).ok_or(MapError::InvalidArc)?;
        let search = Search { map, boundary, region, first: boundary.arc(start, end, full)?, second: boundary.arc(ts, te, tf)? };
        let mut pieces = std::mem::take(&mut self.witness_scratch);
        let result = (|| {
            self.cut(boundary, &search.first, &mut pieces)?;
            for piece in &pieces {
                match piece {
                    QueryPiece::Saved { saved, descriptor, side } => {
                        let lift = Lift { programme: self.programme, descriptor: *descriptor, root: saved.oracle.map().chain() };
                        let chain = lift.chain()?;
                        for vertex in [chain.start, chain.end] {
                            if let Some(chord) = search.endpoint(self, vertex, work)? { return Ok(Some(chord)); }
                        }
                        if let Some(chord) = search.saved(self, saved, *descriptor, *side, work)? { return Ok(Some(chord)); }
                    }
                    QueryPiece::Direct { edge, start, end, .. } => {
                        for parameter in [start, end] {
                            let vertex = if parameter.is_zero_value() { Some(VertexId(edge.0)) }
                                else if parameter.compare_one() == Ordering::Equal { Some(VertexId(edge.0 + 1)) } else { None };
                            if let Some(vertex) = vertex {
                                if let Some(chord) = search.endpoint(self, vertex, work)? { return Ok(Some(chord)); }
                            }
                        }
                    }
                }
            }
            Ok(None)
        })();
        pieces.clear(); self.witness_scratch = pieces;
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fusion;
    use crate::merge;
    use crate::input::Input;
    use crate::view::OffsetView;

    fn s(n: i64, d: i64) -> Symbolic<'static> {
        Symbolic::owned(Rational::new(n.into(), d.into()))
    }
    fn zigzag(edges: i64) -> Input {
        let points: Vec<_> = (0..=edges).map(|i| Point::integer(i,
            if i % 2 == 0 { -i - 1 } else { 40 - i })).collect();
        Input::open(&points).unwrap()
    }
    fn alias<'a>(input: &'a Input, reverse: bool, clipped: bool) -> Programme<'a> {
        let mut p = Programme::new(vec![OffsetView::new(input,
            Symbolic::variable(0), Symbolic::variable(1))]);
        let last = input.edge_count() - 1;
        p.append(Piece::Alias { view: 0,
            first: EdgeId(if reverse { last } else { 0 }),
            last: EdgeId(if reverse { 0 } else { last }),
            start: if clipped { s(if reverse { 3 } else { 1 }, 4) }
                else if reverse { s(1, 1) } else { s(0, 1) },
            end: if clipped { s(if reverse { 1 } else { 3 }, 4) }
                else if reverse { s(0, 1) } else { s(1, 1) },
            reverse }).unwrap();
        p
    }
    fn full_boundary<'p, 'a>(p: &'p Programme<'a>) -> Boundary<'p, Programme<'a>> {
        Boundary::new(p, Chain { start: VertexId(0), end: VertexId(p.edge_count()) }).unwrap()
    }
    /// Independent exhaustive reference, strictly confined to a fixed test size.
    /// It enumerates actual intrinsic flags and geometric edge contacts, without
    /// using programme cutters, saved oracles, or the production tie collector.
    fn reference<'p, 'a>(boundary: Boundary<'p, Programme<'a>>, arc: &Arc<'_, Symbolic<'a>>,
        point: &Point<Symbolic<'a>>, direction: Direction) -> Option<ArcShot<Symbolic<'a>>>
    {
        assert!(boundary.chain().edge_count() <= 64);
        let closed = |site: &Site<Symbolic<'a>>| site == arc.start || site == arc.end || boundary.contains_site(arc, site);
        let mut contacts = Vec::new();
        for site in boundary.occurrences() {
            let p = boundary.point(&site).unwrap();
            if p.y == point.y && closed(&site) { contacts.push((site, p.x.clone())); }
        }
        for hit in boundary.hits(arc, &point.y) {
            if matches!(hit.site, Site::Edge { .. }) { contacts.push((hit.site, hit.x)); }
        }
        for site in [arc.start, arc.end] {
            if matches!(site, Site::Edge { .. }) {
                let p = boundary.point(site).unwrap();
                if p.y == point.y { contacts.push((site.clone(), p.x.clone())); }
            }
        }
        let best = contacts.iter().map(|(_, x)| x)
            .min_by(|a, b| ray_order(&point.x, direction, a, b))?.clone();
        let mut shot = ArcShot::new(best.clone(), contact_route(&point.x, &best, direction));
        for (site, x) in contacts { if x == best { shot.push_contact(site); } }
        Some(shot)
    }
    fn compare_shot<'p, 'a>(queries: &mut ProgrammeQueries<'_, 'p, 'a>,
        boundary: Boundary<'p, Programme<'a>>, arc: &Arc<'_, Symbolic<'a>>,
        point: &Point<Symbolic<'a>>, direction: Direction)
    {
        let got = queries.shoot(boundary, arc.start, arc.end, arc.full_circuit,
            point, direction, &mut Work::default()).unwrap();
        let expected = reference(boundary, arc, point, direction);
        assert_eq!(got.is_some(), expected.is_some());
        if let (Some(got), Some(expected)) = (got, expected) {
            assert_eq!(got.x, expected.x);
            assert_eq!(got.route, expected.route);
            let mut actual: Vec<_> = got.contacts().cloned().collect();
            let mut wanted: Vec<_> = expected.contacts().cloned().collect();
            actual.sort_by(|a, b| boundary.compare_sites(a, b));
            wanted.sort_by(|a, b| boundary.compare_sites(a, b));
            assert_eq!(actual, wanted);
        }
    }
    fn legal<'p, 'a>(boundary: Boundary<'p, Programme<'a>>, chord: &VisibleChord<Symbolic<'a>>) {
        assert!(boundary.chain().edge_count() <= 64);
        let [a, b] = &chord.endpoints;
        boundary.validate_route(a, b, boundary.direction(a).unwrap(), chord.route).unwrap();
        assert_eq!(boundary.input().level(&chord.level).as_ref(), &boundary.point(a).unwrap().y);
        if let Some(null) = boundary.null_contact(a).unwrap() {
            assert_eq!(null, *b);
            assert_eq!(chord.route, Route::Null);
        } else {
            let circle = boundary.arc(a, a, true).unwrap();
            let nearest = boundary.nearest_contacts(&circle, a, boundary.direction(a).unwrap()).unwrap().unwrap();
            assert_eq!(nearest.route, chord.route);
            assert!(nearest.into_iter().any(|hit| hit.site == *b));
            assert_eq!(boundary.direction(b).unwrap(), boundary.direction(a).unwrap().opposite());
            assert!(!boundary.inside_null_pair(b).unwrap());
        }
    }
    fn depth(map: &Submap<'_>) -> usize {
        let tree = map.decomposition().unwrap();
        let mut stack = vec![(tree.root, 1)];
        let mut deepest = 0;
        while let Some((node, distance)) = stack.pop() {
            deepest = deepest.max(distance);
            if let Node::Split { left, right, .. } = tree.nodes[node] {
                stack.extend([(left, distance + 1), (right, distance + 1)]);
            }
        }
        deepest
    }

    #[test]
    fn displaced_saved_alias_shots_match_raw_geometry_in_both_directions_and_caps() {
        let input = zigzag(32);
        let catalogue = Catalogue::build(&input, 4, &mut OriginalMerge, &mut Work::default()).unwrap();
        for reverse in [false, true] { for clipped in [false, true] {
            let p = alias(&input, reverse, clipped);
            let boundary = full_boundary(&p);
            let left = Site::Vertex { vertex: VertexId(0), side: Side::Left, slot: Slot::Single };
            let end_left = Site::Vertex { vertex: VertexId(32), side: Side::Left, slot: Slot::Single };
            let right = Site::Vertex { vertex: VertexId(0), side: Side::Right, slot: Slot::Single };
            let end_right = Site::Vertex { vertex: VertexId(32), side: Side::Right, slot: Slot::Single };
            let arcs = [boundary.arc(&left, &left, true).unwrap(),
                boundary.arc(&left, &end_left, false).unwrap(),
                boundary.arc(&end_right, &right, false).unwrap(),
                boundary.arc(&end_left, &right, false).unwrap()];
            let mut queries = ProgrammeQueries::new(&catalogue, &p, 4);
            for index in [0, 1, 7, 15, 16, 23, 31, 32] {
                let point = p.vertex(VertexId(index)).into_owned();
                let stale = Symbolic::borrowed(&input.vertex(VertexId(index)).y);
                for level in [point.y.clone(), stale, point.y.plus(&Symbolic::variable(2))] {
                    let source = Point::new(s(-1, 2), level);
                    for direction in [Direction::Left, Direction::Right] {
                        for arc in &arcs { compare_shot(&mut queries, boundary, arc, &source, direction); }
                    }
                }
            }
            let zero = boundary.normalize_site(&Site::Edge { edge: EdgeId(0), t: s(1, 3), side: Side::Left }).unwrap();
            let arc = boundary.arc(&zero, &zero, false).unwrap();
            let source = boundary.point(&zero).unwrap().into_owned();
            for direction in [Direction::Left, Direction::Right] {
                compare_shot(&mut queries, boundary, &arc, &source, direction);
                compare_shot(&mut queries, boundary, &arc,
                    &Point::new(source.x.clone(), source.y.plus(&s(1, 1))), direction);
            }
        } }
    }

    #[test]
    fn transported_interval_maps_have_real_sources_and_contiguous_clipped_pieces() {
        let input = zigzag(32);
        let catalogue = Catalogue::build(&input, 4, &mut OriginalMerge, &mut Work::default()).unwrap();
        for reverse in [false, true] {
            let p = alias(&input, reverse, true);
            let mut queries = ProgrammeQueries::new(&catalogue, &p, 4);
            let maps = queries.piece_maps(&mut OriginalMerge, &mut Work::default()).unwrap();
            assert_eq!(maps.first().unwrap().chain().start, VertexId(0));
            assert_eq!(maps.last().unwrap().chain().end, VertexId(32));
            for pair in maps.windows(2) { assert_eq!(pair[0].chain().end, pair[1].chain().start); }
            assert_eq!(maps.len(), 3);
            assert_eq!(maps[1].chain().edge_count(), 30);
            let mut augmented = false;
            for map in &maps {
                let boundary = Boundary::new(&p, map.chain()).unwrap();
                for id in map.chord_ids() {
                    let ([a, b], route) = map.chord(id).unwrap();
                    let chord = VisibleChord { endpoints: [a.clone(), b.clone()], route,
                        level: map.chord_level(id).unwrap().clone() };
                    assert!(matches!(chord.level, LevelSource::Vertex(_)));
                    augmented |= chord.endpoints.iter().any(|site| matches!(site, Site::Edge { .. }));
                    legal(boundary, &chord);
                }
            }
            assert!(augmented);
        }
    }

    #[test]
    fn directed_programme_pairs_preserve_intrinsic_negatives_and_one_child_descent() {
        let input = zigzag(16);
        let catalogue = Catalogue::build(&input, 4, &mut OriginalMerge, &mut Work::default()).unwrap();
        let mut positive = false; let mut negative = false; let mut descended = false;
        let mut wrapping = false; let mut nonconsecutive = false;
        for reverse in [false, true] {
            let p = alias(&input, reverse, false);
            let boundary = full_boundary(&p);
            assert!(boundary.chain().edge_count() <= Programme::MAX_LEAF_EDGES);
            let full = base::full_visibility(boundary, &mut Work::default()).unwrap();
            let mut retained = Vec::new();
            for id in full.chord_ids() {
                let ([a, b], route) = full.chord(id).unwrap();
                let side = if reverse { Side::Right } else { Side::Left };
                if route == Route::Null && a.side() == side && retained.len() < 6 {
                    retained.push(VisibleChord { endpoints: [a.clone(), b.clone()], route,
                        level: full.chord_level(id).unwrap().clone() });
                }
            }
            assert!(retained.len() >= 4);
            let current = Submap::from_verified_chords(&boundary, retained, &mut Work::default()).unwrap();
            for cutoff in [1, 4] {
                let mut queries = ProgrammeQueries::new(&catalogue, &p, cutoff);
                for region in current.region_ids() {
                    let arcs = current.region_arcs(region).unwrap();
                    for (i, &first_id) in arcs.iter().enumerate() {
                        let (a, b, full_arc) = current.arc_sites(first_id).unwrap();
                        let first = boundary.arc(a, b, full_arc).unwrap();
                        let mut pieces = Vec::new();
                        queries.cut(boundary, &first, &mut pieces).unwrap();
                        let saved_count = pieces.iter().filter(|piece| matches!(piece, QueryPiece::Saved { .. })).count();
                        let bound: usize = pieces.iter().filter_map(|piece| match piece {
                            QueryPiece::Saved { saved, .. } => Some(depth(saved.oracle.map())), _ => None }).sum();
                        for (j, &second_id) in arcs.iter().enumerate() {
                            if first_id == second_id { continue; }
                            nonconsecutive |= arcs.len() > 3 && (i + 1) % arcs.len() != j && (j + 1) % arcs.len() != i;
                            let (a, b, full_arc) = current.arc_sites(second_id).unwrap();
                            let second = boundary.arc(a, b, full_arc).unwrap();
                            let expected = full.chord_ids().any(|id| {
                                let ([a, b], _) = full.chord(id).unwrap();
                                [(a, b), (b, a)].into_iter().any(|(a, b)|
                                    matches!(a, Site::Vertex { .. }) && witness::open(boundary, &first, a)
                                        && witness::open(boundary, &second, b))
                            });
                            let mut work = Work::default();
                            let result = queries.witness(&current, region, first_id, second_id, &mut work).unwrap();
                            assert!(work.decomposition_visits <= bound as u128);
                            descended |= work.decomposition_visits > saved_count as u128;
                            match result {
                                Some(chord) => {
                                    positive = true; wrapping |= chord.route == Route::Wrap;
                                    assert!(witness::open(boundary, &first, &chord.endpoints[0]));
                                    assert!(witness::open(boundary, &second, &chord.endpoints[1]));
                                    legal(boundary, &chord);
                                    if matches!(chord.endpoints[0], Site::Vertex { .. }) { assert!(expected); }
                                }
                                None => { assert!(!expected); negative = true; }
                            }
                        }
                    }
                }
            }
        }
        assert!(positive && negative && descended && wrapping && nonconsecutive);
    }

    #[test]
    fn finite_projective_piece_maps_support_actual_fusion_and_restoration() {
        let input = Input::open(&(0..=4).map(|i| Point::integer(i, i)).collect::<Vec<_>>()).unwrap();
        let catalogue = Catalogue::build(&input, 2, &mut OriginalMerge, &mut Work::default()).unwrap();
        let view = OffsetView::new(&input, Symbolic::variable(0), Symbolic::variable(1));
        let finite_start = view.finite_vertex(VertexId(4));
        let finite_end = Point::new(finite_start.x.plus(&s(3, 1)), finite_start.y.plus(&s(2, 1)));
        let mut p = Programme::new(vec![view]);
        p.append(Piece::Alias { view: 0, first: EdgeId(0), last: EdgeId(3),
            start: s(0, 1), end: s(1, 1), reverse: false }).unwrap();
        p.append(Piece::Finite { start: finite_start, end: finite_end.clone() }).unwrap();
        let projective_start = p.vertex(VertexId(5)).into_owned();
        p.append(Piece::Projective { start: projective_start,
            end: Point::new(s(-1, 2), finite_end.y.plus(&s(3, 1))), winding: 1 }).unwrap();
        let boundary = full_boundary(&p);
        let mut queries = ProgrammeQueries::new(&catalogue, &p, 2);
        let anchor = Site::Vertex { vertex: VertexId(0), side: Side::Left, slot: Slot::Single };
        let circle = boundary.arc(&anchor, &anchor, true).unwrap();
        for edge in [EdgeId(4), EdgeId(5)] {
            let target = p.edge_point(edge, &s(1, 2));
            for direction in [Direction::Left, Direction::Right] {
                compare_shot(&mut queries, boundary, &circle, &Point::new(s(0, 1), target.y.clone()), direction);
            }
        }
        let mut work = Work::default();
        let maps = queries.piece_maps(&mut OriginalMerge, &mut work).unwrap();
        fn balanced<'c, 'p, 'a>(maps: &mut std::vec::IntoIter<Submap<'p, Programme<'a>>>,
            count: usize, queries: &mut ProgrammeQueries<'c, 'p, 'a>, work: &mut Work) -> Submap<'p, Programme<'a>>
        {
            if count == 1 { return maps.next().unwrap(); }
            let left = balanced(maps, count / 2, queries, work);
            let right = balanced(maps, count - count / 2, queries, work);
            let mut map = fusion::fuse(&left, &right, queries, work).unwrap();
            merge::restore(&mut map, queries, work).unwrap();
            map
        }
        let count = maps.len();
        let merged = balanced(&mut maps.into_iter(), count, &mut queries, &mut work);
        let full = base::full_visibility(boundary, &mut Work::default()).unwrap();
        fn records<'p, 'a>(map: &Submap<'p, Programme<'a>>, boundary: Boundary<'p, Programme<'a>>)
            -> Vec<([Site<Symbolic<'a>>; 2], Route, LevelSource<Symbolic<'a>>)>
        {
            map.chord_ids().map(|id| {
                let ([a, b], route) = map.chord(id).unwrap();
                let mut ends = [a.clone(), b.clone()];
                if boundary.compare_sites(&ends[0], &ends[1]) == Ordering::Greater { ends.swap(0, 1); }
                (ends, route, map.chord_level(id).unwrap().clone())
            }).collect()
        }
        let mut got = records(&merged, boundary); let mut expected = records(&full, boundary);
        got.sort_by(|a, b| boundary.compare_sites(&a.0[0], &b.0[0]));
        expected.sort_by(|a, b| boundary.compare_sites(&a.0[0], &b.0[0]));
        assert_eq!(got, expected);
        for record in got { legal(boundary, &VisibleChord { endpoints: record.0, route: record.1, level: record.2 }); }
    }
}
