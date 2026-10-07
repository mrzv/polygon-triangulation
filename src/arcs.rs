//! First geometric blockers on raw double-boundary arcs, using saved chains.
//! Arrival sectors are deliberately left to the caller: no nearer contact is
//! discarded for facing the wrong way. Only clipped endpoint geometry is direct.
use crate::boundary::{Arc, Boundary, BoundaryError, Side, Site, Slot};
use crate::curve::Curve;
use crate::geometry::{contact_route, ray_order, Direction, Point, Rational, Route};
use crate::hierarchy::{Catalogue, CutError, Piece};
use crate::input::{EdgeId, VertexId};
use crate::oracle::{OracleError, PointProbe};
use crate::work::Work;
use num_traits::{One, Zero};
use std::cmp::Ordering;
use std::fmt;

/// All intrinsic incidences at one physical first-contact coordinate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArcShot<S = Rational> {
    pub x: S,
    pub route: Route,
    contacts: [Option<Site<S>>; 4],
    count: usize,
}
impl<S: PartialEq> ArcShot<S> {
    pub(crate) fn new(x: S, route: Route) -> Self {
        Self { x, route, contacts: [None, None, None, None], count: 0 }
    }
    pub(crate) fn push_contact(&mut self, site: Site<S>) {
        if self.contacts().any(|old| old == &site) { return; }
        assert!(self.count < self.contacts.len(), "more than four intrinsic contacts at one coordinate");
        self.contacts[self.count] = Some(site);
        self.count += 1;
    }
    pub fn contacts(&self) -> impl ExactSizeIterator<Item = &Site<S>> + DoubleEndedIterator {
        self.contacts[..self.count].iter().map(|site| site.as_ref().unwrap())
    }
    pub(crate) fn into_contacts(self) -> impl Iterator<Item = Site<S>> {
        self.contacts.into_iter().flatten()
    }
}

#[derive(Debug)]
pub enum ArcQueryError { Cut(CutError), Boundary(BoundaryError), Oracle(OracleError) }
impl From<CutError> for ArcQueryError { fn from(e: CutError) -> Self { Self::Cut(e) } }
impl From<BoundaryError> for ArcQueryError { fn from(e: BoundaryError) -> Self { Self::Boundary(e) } }
impl From<OracleError> for ArcQueryError { fn from(e: OracleError) -> Self { Self::Oracle(e) } }
impl fmt::Display for ArcQueryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for ArcQueryError {}

pub struct ArcQueries<'c, 'a> {
    catalogue: &'c Catalogue<'a>,
    max_saved_grade: usize,
    scratch: Vec<Piece<'c, 'a>>,
    witness_pieces: Vec<Piece<'c, 'a>>,
}
impl<'c, 'a> ArcQueries<'c, 'a> {
    pub fn new(catalogue: &'c Catalogue<'a>, max_saved_grade: usize) -> Self {
        Self { catalogue, max_saved_grade, scratch: Vec::new(), witness_pieces: Vec::new() }
    }
    pub fn catalogue(&self) -> &'c Catalogue<'a> { self.catalogue }
    pub fn max_saved_grade(&self) -> usize { self.max_saved_grade }
    /// Keep the search cutter's pieces independent of local-shooting scratch.
    pub(crate) fn take_witness_pieces(&mut self) -> Vec<Piece<'c, 'a>> {
        std::mem::take(&mut self.witness_pieces)
    }
    pub(crate) fn recycle_witness_pieces(&mut self, mut pieces: Vec<Piece<'c, 'a>>) {
        pieces.clear();
        self.witness_pieces = pieces;
    }
    pub fn shoot(&mut self, boundary: Boundary<'a>, start: &Site, end: &Site,
        full: bool, source: &Point, direction: Direction, work: &mut Work)
        -> Result<Option<ArcShot>, ArcQueryError>
    {
        self.catalogue.cut_arc(boundary, start, end, full, self.max_saved_grade, &mut self.scratch)?;
        let start = boundary.normalize_site(start)?;
        let end = boundary.normalize_site(end)?;
        let arc = boundary.arc(&start, &end, full)?;
        let probe = PointProbe { x: source.x.clone(), y: source.y.clone(), direction };
        let mut best = None;
        // The raw clip is closed even when it has no positive-length pieces.
        // Evaluate both endpoints explicitly, not just endpoints of saved pieces.
        for endpoint in [&start, &end] {
            work.predicates += 1;
            let point = boundary.point(endpoint)?;
            if point.y == source.y {
                collect_site(boundary, &arc, endpoint, &point.x, source, direction, &mut best, work);
            }
        }
        for piece in &self.scratch {
            match piece {
                Piece::Saved { chain, side } => {
                    if let Some(hit) = chain.oracle.shoot(&probe, work)? {
                        collect_edge(boundary, &arc, hit.edge, &hit.t, *side, &hit.x,
                            source, direction, &mut best, work)?;
                    }
                }
                Piece::Edge { edge, side, start, end } => {
                    // Charge every attempt, including a level miss or clip miss.
                    work.arc_edge_visits += 1;
                    work.predicates += 1;
                    if let Some((t, x)) = boundary.input().horizontal_hit(*edge, &source.y) {
                        work.predicates += 2;
                        if &t >= start && &t <= end {
                            collect_edge(boundary, &arc, *edge, &t, *side, &x,
                                source, direction, &mut best, work)?;
                        }
                    }
                }
            }
        }
        Ok(best)
    }
}

fn in_clip(boundary: Boundary<'_>, arc: &Arc<'_>, site: &Site) -> bool {
    site == arc.start || site == arc.end || boundary.contains_site(arc, site)
}
fn retain(site: Site, x: &Rational, source: &Point, direction: Direction,
    best: &mut Option<ArcShot>, work: &mut Work)
{
    work.predicates += 1;
    let order = best.as_ref().map(|old| ray_order(&source.x, direction, x, &old.x));
    if order.is_none() || order == Some(Ordering::Less) {
        *best = Some(ArcShot::new(x.clone(), contact_route(&source.x, x, direction)));
    } else if order != Some(Ordering::Equal) { return; }
    best.as_mut().unwrap().push_contact(site);
}
fn collect_site(boundary: Boundary<'_>, arc: &Arc<'_>, site: &Site, x: &Rational,
    source: &Point, direction: Direction, best: &mut Option<ArcShot>, work: &mut Work)
{
    match site {
        Site::Vertex { vertex, .. } => {
            // A saved-chain cap can hide the second support edge in the parent
            // scope. Expand the physical vertex in that scope before clipping.
            let slots: &[Slot] = if boundary.is_extremum(*vertex) {
                &[Slot::Incoming, Slot::Outgoing]
            } else { &[Slot::Single] };
            for side in [Side::Left, Side::Right] {
                for &slot in slots {
                    let contact = Site::Vertex { vertex: *vertex, side, slot };
                    work.predicates += 1;
                    if in_clip(boundary, arc, &contact) {
                        retain(contact, x, source, direction, best, work);
                    }
                }
            }
        }
        Site::Edge { edge, t, .. } => {
            for side in [Side::Left, Side::Right] {
                let contact = Site::Edge { edge: *edge, t: t.clone(), side };
                work.predicates += 1;
                if in_clip(boundary, arc, &contact) {
                    retain(contact, x, source, direction, best, work);
                }
            }
        }
    }
}
fn collect_edge(boundary: Boundary<'_>, arc: &Arc<'_>, edge: EdgeId, t: &Rational,
    side: Side, x: &Rational, source: &Point, direction: Direction,
    best: &mut Option<ArcShot>, work: &mut Work) -> Result<(), BoundaryError>
{
    let site = if t.is_zero() {
        Site::Vertex { vertex: VertexId(edge.0), side,
            slot: if boundary.is_extremum(VertexId(edge.0)) { Slot::Outgoing } else { Slot::Single } }
    } else if t == &Rational::one() {
        Site::Vertex { vertex: VertexId(edge.0 + 1), side,
            slot: if boundary.is_extremum(VertexId(edge.0 + 1)) { Slot::Incoming } else { Slot::Single } }
    } else { Site::Edge { edge, t: t.clone(), side } };
    boundary.validate_site(&site)?;
    collect_site(boundary, arc, &site, x, source, direction, best, work);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::base::{full_visibility, BaseError};
    use crate::boundary::Chain;
    use crate::hierarchy::MergeEngine;
    use crate::input::Input;
    use crate::submap::Submap;

    struct BoundedGeometry;
    impl<'a> MergeEngine<'a> for BoundedGeometry {
        type Error = BaseError;
        fn base_map(&mut self, boundary: Boundary<'a>, work: &mut Work)
            -> Result<Submap<'a>, Self::Error>
        {
            assert!(boundary.chain().edge_count() <= 16);
            full_visibility(boundary, work)
        }
        fn merge(&mut self, left: &Submap<'a>, right: &Submap<'a>, _: usize,
            catalogue: &Catalogue<'a>, work: &mut Work) -> Result<Submap<'a>, Self::Error>
        {
            let chain = Chain::new(catalogue.input(), left.chain().start, right.chain().end).unwrap();
            assert!(chain.edge_count() <= 16);
            full_visibility(Boundary::new(catalogue.input(), chain).unwrap(), work)
        }
    }
    fn compare<'a>(boundary: Boundary<'a>, query: &mut ArcQueries<'_, 'a>,
        start: &Site, end: &Site, full: bool, source: &Site, direction: Direction)
    {
        let arc = boundary.arc(start, end, full).unwrap();
        let point = boundary.point(source).unwrap();
        let actual = query.shoot(boundary, start, end, full, &point, direction,
            &mut Work::default()).unwrap();
        let expected = boundary.nearest_contacts(&arc, source, direction).unwrap();
        // The point-based service has no source identity to exclude. Its raw
        // arc includes that incidence too, if the first coordinate is source X.
        match (actual, expected) {
            (None, None) => {}
            (Some(actual), Some(expected)) => {
                assert_eq!(actual.x, expected.x, "{start:?} -> {end:?}, source {source:?}");
                assert_eq!(actual.route, expected.route);
                let mut contacts: Vec<_> = expected.map(|contact| contact.site).collect();
                if actual.x == point.x && in_clip(boundary, &arc, source) {
                    contacts.push(source.clone());
                }
                assert_eq!(actual.contacts().len(), contacts.len());
                for site in actual.contacts() {
                    assert!(contacts.contains(site), "unexpected {site:?}: {contacts:?}");
                }
            }
            (Some(actual), None) if in_clip(boundary, &arc, source) => {
                assert_eq!(actual.x, point.x);
                assert_eq!(actual.route, Route::Wrap);
                assert_eq!(actual.contacts().collect::<Vec<_>>(), [source]);
            }
            (actual, expected) => panic!("different blockers: {actual:?}, expected {}", expected.is_some()),
        }
    }

    #[test]
    fn canonical_saved_chains_match_all_first_coordinate_flags() {
        // Strictly increasing X keeps this zigzag simple; its middle vertex
        // is ordinary and its alternating peaks give genuine extrema.
        let input = Input::open(&[
            Point::integer(0, 0), Point::integer(1, 3), Point::integer(2, 1),
            Point::integer(3, 2), Point::integer(4, 3), Point::integer(5, -1),
            Point::integer(6, 2), Point::integer(7, -2), Point::integer(8, 0),
        ]).unwrap();
        let boundary = Boundary::new(&input, Chain::new(&input, VertexId(0), VertexId(8)).unwrap()).unwrap();
        let catalogue = Catalogue::build(&input, 1, &mut BoundedGeometry, &mut Work::default()).unwrap();
        let vertices: Vec<_> = boundary.occurrences().collect();
        assert!(vertices.iter().any(|s| matches!(s, Site::Vertex { slot: Slot::Incoming, .. })));
        let mut endpoints = vertices.clone();
        endpoints.extend((0..8).flat_map(|e| [Side::Left, Side::Right].map(|side|
            Site::Edge { edge: EdgeId(e), t: Rational::new(1.into(), 2.into()), side })));
        for grade in [0, 2] {
            let mut query = ArcQueries::new(&catalogue, grade);
            for start in &endpoints {
                for end in &endpoints {
                    if start == end { continue; }
                    for source in endpoints.iter().step_by(3) {
                        for direction in [Direction::Left, Direction::Right] {
                            compare(boundary, &mut query, start, end, false, source, direction);
                        }
                    }
                }
            }
            for start in &vertices {
                for source in endpoints.iter().step_by(3) {
                    for direction in [Direction::Left, Direction::Right] {
                        compare(boundary, &mut query, start, start, true, source, direction);
                    }
                }
            }
        }
    }

    #[test]
    fn closed_zero_length_clips_and_reused_scratch_count_direct_misses() {
        let input = Input::open(&(0..=8).map(|i| Point::integer(0, i)).collect::<Vec<_>>()).unwrap();
        let boundary = Boundary::new(&input, Chain::new(&input, VertexId(0), VertexId(8)).unwrap()).unwrap();
        let catalogue = Catalogue::build(&input, 1, &mut BoundedGeometry, &mut Work::default()).unwrap();
        let mut query = ArcQueries::new(&catalogue, 1);
        let start = Site::Edge { edge: EdgeId(2), t: Rational::new(1.into(), 4.into()), side: Side::Left };
        let end = Site::Edge { edge: EdgeId(5), t: Rational::new(3.into(), 4.into()), side: Side::Left };
        query.shoot(boundary, &start, &end, false, &Point::integer(1, 100),
            Direction::Right, &mut Work::default()).unwrap();
        let capacity = query.scratch.capacity();
        for site in [start.clone(), Site::Vertex { vertex: VertexId(0), side: Side::Right, slot: Slot::Single }] {
            let point = boundary.point(&site).unwrap();
            let source = Point::new(&point.x - Rational::one(), point.y.clone());
            let hit = query.shoot(boundary, &site, &site, false, &source,
                Direction::Right, &mut Work::default()).unwrap().unwrap();
            assert_eq!(hit.x, point.x);
            assert_eq!(hit.route, Route::Finite);
            assert_eq!(hit.contacts().collect::<Vec<_>>(), [&site]);
            assert!(query.scratch.is_empty());
            assert_eq!(query.scratch.capacity(), capacity);
        }
        let mut work = Work::default();
        assert!(query.shoot(boundary, &start, &end, false, &Point::integer(1, 100),
            Direction::Right, &mut work).unwrap().is_none());
        assert!(work.arc_edge_visits >= 2, "both directly clipped edges must count misses");
        assert_eq!(query.scratch.capacity(), capacity);
    }
}
