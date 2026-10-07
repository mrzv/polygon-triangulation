//! Complete visibility for the fixed-size leaves of Chazelle's hierarchy.
//!
//! This is not a fallback triangulator: the edge limit is independent of input
//! size, and larger chains are rejected. Every intrinsic occurrence receives
//! its nearest admissible contact, including null and full-circle routes.

use crate::boundary::{Boundary, BoundaryError, Direction, Side, Site};
use crate::geometry::{Rational, Route, contact_route, horizontal_hit, ray_order};
use crate::input::{EdgeId, VertexId};
use crate::submap::{MapError, Submap, VisibleChord};
use crate::work::Work;
use std::cmp::Ordering;
use std::fmt;

pub const MAX_BASE_EDGES: usize = 16;

#[derive(Debug)]
pub enum BaseError {
    TooLarge { edges: usize },
    Boundary(BoundaryError),
    Map(MapError),
    MissingArrival,
    AmbiguousArrival,
    ConflictingPartner,
}
impl fmt::Display for BaseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for BaseError {}
impl From<BoundaryError> for BaseError {
    fn from(error: BoundaryError) -> Self { Self::Boundary(error) }
}
impl From<MapError> for BaseError {
    fn from(error: MapError) -> Self { Self::Map(error) }
}

pub fn full_visibility<'a>(boundary: Boundary<'a>, work: &mut Work) -> Result<Submap<'a>, BaseError> {
    let chain = boundary.chain();
    let edges = chain.end.0 - chain.start.0;
    if edges > MAX_BASE_EDGES { return Err(BaseError::TooLarge { edges }); }
    let mut chords: Vec<VisibleChord> = Vec::with_capacity(2 * (edges + 1));
    for source in boundary.occurrences() {
        work.predicates += 1;
        let (target, route) = if boundary.inside_null_pair(&source)? {
            (boundary.companion(&source)?.ok_or(BaseError::MissingArrival)?, Route::Null)
        } else {
            let Site::Vertex { vertex, .. } = source else { unreachable!() };
            let point = boundary.input().vertex(vertex);
            let direction = boundary.direction(&source)?;
            let mut closest: Option<Rational> = None;
            let mut arrival: Option<Site> = None;
            let mut ambiguous = false;
            for index in chain.start.0..chain.end.0 {
                let edge = EdgeId(index);
                work.arc_edge_visits += 1;
                let a = boundary.input().vertex(VertexId(index));
                let b = boundary.input().vertex(VertexId(index + 1));
                work.predicates += 1;
                let Some((t, x)) = horizontal_hit(a, b, &point.y) else { continue; };
                let order = closest.as_ref().map_or(Ordering::Less, |old| {
                    work.predicates += 1;
                    ray_order(&point.x, direction, &x, old)
                });
                if order == Ordering::Greater { continue; }
                if order == Ordering::Less {
                    closest = Some(x);
                    arrival = None;
                    ambiguous = false;
                }
                let ray_sign = if direction == Direction::Right { Ordering::Greater } else { Ordering::Less };
                let side = if boundary.input().edge_y_sign(edge) == ray_sign { Side::Left } else { Side::Right };
                let hit = boundary.normalize_site(&Site::Edge { edge, t, side })?;
                work.predicates += 1;
                // A remote ray cannot reach the small inside-turn connector.
                // Keep the geometric blocker even if this particular incidence
                // is inadmissible; another supporting edge may supply its flag.
                if boundary.inside_null_pair(&hit)? || hit == source { continue; }
                if arrival.as_ref().is_some_and(|old| old != &hit) { ambiguous = true; }
                else { arrival = Some(hit); }
            }
            if ambiguous { return Err(BaseError::AmbiguousArrival); }
            let x = closest.ok_or(BaseError::MissingArrival)?;
            let target = arrival.ok_or(BaseError::MissingArrival)?;
            let route = contact_route(&point.x, &x, direction);
            boundary.validate_route(&source, &target, direction, route)?;
            (target, route)
        };
        let mut duplicate = false;
        for old in &chords {
            work.retained_visits += 1;
            if (old.endpoints[0] == source && old.endpoints[1] == target)
                || (old.endpoints[0] == target && old.endpoints[1] == source) {
                if old.route != route { return Err(BaseError::ConflictingPartner); }
                duplicate = true;
                break;
            }
            if old.endpoints.iter().any(|site| site == &source || site == &target) {
                return Err(BaseError::ConflictingPartner);
            }
        }
        if !duplicate { chords.push(VisibleChord { endpoints: [source, target], route }); }
    }
    let map = Submap::from_verified_chords(&boundary, chords, work)?;
    if map.decomposition().is_none() { return Err(BaseError::Map(MapError::NonConformal)); }
    Ok(map)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boundary::{Chain, Slot};
    use crate::geometry::Point;
    use crate::input::Input;

    #[test]
    fn finite_blocker_and_opposite_wrapping_partner_are_not_conflated() {
        let input = Input::open(&[Point::integer(0, 0), Point::integer(2, 4), Point::integer(4, 0)]).unwrap();
        let chain = Chain::new(&input, VertexId(0), VertexId(2)).unwrap();
        let boundary = Boundary::new(&input, chain).unwrap();
        let mut work = Work::default();
        let map = full_visibility(boundary, &mut work).unwrap();
        for (side, expected_route) in [(Side::Right, Route::Finite), (Side::Left, Route::Wrap)] {
            let source = Site::Vertex { vertex: VertexId(2), side, slot: Slot::Single };
            let (ends, route) = map.chord_ids().find_map(|id| {
                let (ends, route) = map.chord(id).unwrap();
                ends.contains(&&source).then_some((ends, route))
            }).unwrap();
            let target = if ends[0] == &source { ends[1] } else { ends[0] };
            assert_eq!(route, expected_route);
            assert_eq!(boundary.point(target).unwrap().x, Rational::new(4.into(), 11.into()));
            assert_eq!(boundary.point(target).unwrap().y, Rational::from_integer(4.into()));
        }
        for source in boundary.occurrences() {
            assert_eq!(map.chord_ids().filter(|&id| map.chord(id).unwrap().0.contains(&&source)).count(), 1);
            if boundary.inside_null_pair(&source).unwrap() {
                let partner = boundary.companion(&source).unwrap().unwrap();
                assert!(map.chord_ids().any(|id| {
                    let (ends, route) = map.chord(id).unwrap();
                    route == Route::Null && ends.contains(&&source) && ends.contains(&&partner)
                }));
            }
        }
    }

    #[test]
    fn collinear_chain_keeps_every_original_full_circle_level() {
        let points: Vec<_> = (0..5).map(|x| Point::integer(x, 0)).collect();
        let input = Input::open(&points).unwrap();
        let chain = Chain::new(&input, VertexId(0), VertexId(input.len() - 1)).unwrap();
        let boundary = Boundary::new(&input, chain).unwrap();
        let mut work = Work::default();
        let map = full_visibility(boundary, &mut work).unwrap();
        for source in boundary.occurrences() {
            let partner = boundary.companion(&source).unwrap().unwrap();
            assert!(map.chord_ids().any(|id| {
                let (ends, route) = map.chord(id).unwrap();
                route == Route::Wrap && ends.contains(&&source) && ends.contains(&&partner)
            }));
        }
        assert!(work.arc_edge_visits <= (4 * (MAX_BASE_EDGES + 1) * MAX_BASE_EDGES) as u128);
    }

    #[test]
    fn larger_chain_cannot_take_the_constant_leaf_path() {
        let points: Vec<_> = (0..18).map(|x| Point::integer(x, x)).collect();
        let input = Input::open(&points).unwrap();
        let chain = Chain::new(&input, VertexId(0), VertexId(input.len() - 1)).unwrap();
        let boundary = Boundary::new(&input, chain).unwrap();
        assert!(matches!(full_visibility(boundary, &mut Work::default()), Err(BaseError::TooLarge { .. })));
    }
}
