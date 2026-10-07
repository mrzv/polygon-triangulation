//! Chazelle's saved-chain construction, region refinement and closed reduction.
use crate::arcs::ArcQueries;
use crate::boundary::{Boundary, BoundaryError};
use crate::closure::{ClosureError, close_visibility};
use crate::collapse::{CollapseError, collapse};
use crate::completion::{CompletionError, FIXED_COMPLETION_GRANULARITY, complete};
use crate::fusion::{FusionError, fuse};
use crate::geometry::Point;
use crate::graft::{GraftError, graft};
use crate::hierarchy::{Catalogue, CutError, HierarchyError, grade, granularity};
use crate::input::{Input, InputError};
use crate::merge::{MergeError, OriginalMerge, RestoreError, restore_visibility};
use crate::program::Programme;
use crate::program_queries::{ProgrammeQueries, ProgrammeQueryError};
use crate::reduction::{ReductionError, triangulate_visibility};
use crate::ribbon::{Ribbon, RibbonError};
use crate::submap::{MapError, RegionId, Submap};
use crate::witness::WitnessError;
use crate::work::Work;
use std::fmt;

#[derive(Debug)]
pub enum TriangulationError {
    Input(InputError),
    Boundary(BoundaryError),
    Cut(CutError),
    Hierarchy(HierarchyError<MergeError>),
    Ribbon(RibbonError),
    Programme(ProgrammeQueryError),
    Fusion(FusionError<ProgrammeQueryError>),
    ProgrammeRestore(RestoreError<ProgrammeQueryError>),
    Collapse(CollapseError),
    Graft(GraftError),
    Restore(RestoreError<WitnessError>),
    Map(MapError),
    Completion(CompletionError),
    Closure(ClosureError),
    Reduction(ReductionError),
    EmptyProgramme,
    RefinementWeight { region: RegionId, weight: usize, limit: usize },
}
impl fmt::Display for TriangulationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for TriangulationError {}

fn local_map<'p, 'a>(ribbon: &'p Ribbon<'a>, catalogue: &Catalogue<'a>,
    gamma: usize, work: &mut Work) -> Result<Submap<'p, Programme<'a>>, TriangulationError>
{
    let mut queries = ProgrammeQueries::new(catalogue, &ribbon.programme, grade(gamma));
    let mut maps = queries.piece_maps(&mut OriginalMerge, work)
        .map_err(TriangulationError::Programme)?;
    for map in &mut maps {
        work.retained_visits += 1;
        let boundary = Boundary::new(&ribbon.programme, map.chain())
            .map_err(TriangulationError::Boundary)?;
        map.coarsen(&boundary, gamma, work).map_err(TriangulationError::Map)?;
    }
    while maps.len() > 1 {
        let mut next = Vec::with_capacity(maps.len().div_ceil(2));
        let mut pieces = maps.into_iter();
        while let Some(left) = pieces.next() {
            work.retained_visits += 1;
            if let Some(right) = pieces.next() {
                let mut joined = fuse(&left, &right, &mut queries, work)
                    .map_err(TriangulationError::Fusion)?;
                restore_visibility(&mut joined, &mut queries, work)
                    .map_err(TriangulationError::ProgrammeRestore)?;
                let boundary = Boundary::new(&ribbon.programme, joined.chain())
                    .map_err(TriangulationError::Boundary)?;
                joined.coarsen(&boundary, gamma, work).map_err(TriangulationError::Map)?;
                next.push(joined);
            } else {
                next.push(left);
            }
        }
        maps = next;
    }
    maps.pop().ok_or(TriangulationError::EmptyProgramme)
}

/// Refine a conformal whole-curve map through smaller saved original chains.
///
/// The caller supplies its actual upper granularity; this also permits direct
/// execution of refinement on coarser valid maps without enormous inputs.
/// Every published stage checks the original arc bound. Current-map publication
/// is linear and deliberately does not construct a saved-query decomposition.
/// Chord levels must be normalized Vertex descriptors, as emitted by Catalogue
/// and OriginalMerge. Arbitrary certified Frozen augmentations belong to the
/// low-level kernel, not this production refinement contract.
pub fn refine<'a>(mut current: Submap<'a>, mut gamma: usize,
    catalogue: &Catalogue<'a>, work: &mut Work) -> Result<Submap<'a>, TriangulationError>
{
    if !std::ptr::eq(current.input(), catalogue.input()) {
        return Err(TriangulationError::Cut(CutError::DifferentInput));
    }
    if gamma == 0 {
        return Err(TriangulationError::Cut(CutError::InvalidInterval));
    }
    let boundary = Boundary::new(current.input(), current.chain())
        .map_err(TriangulationError::Boundary)?;
    while gamma > FIXED_COMPLETION_GRANULARITY {
        let temporary_gamma = granularity(grade(gamma)).map_err(TriangulationError::Cut)?;
        // Each original arc inherits one temporary support arc, plus at most
        // one trimmed original edge at each of its two endpoint collars.
        let next_gamma = temporary_gamma.checked_add(2)
            .ok_or(TriangulationError::Cut(CutError::SizeOverflow))?;
        let mut queries = ArcQueries::new(catalogue, grade(gamma));
        let mut regions = Vec::with_capacity(current.region_ids().count());
        for region in current.region_ids() {
            work.retained_visits += 1;
            let weight = current.region_weight(&boundary, region)
                .map_err(TriangulationError::Map)?;
            if weight > gamma {
                return Err(TriangulationError::RefinementWeight { region, weight, limit: gamma });
            }
            // A wrapping cap hemisphere may have zero original arc weight;
            // preserve its existing topology rather than calling it empty.
            if weight == 0 { continue; }
            let ribbon = Ribbon::compile(&current, region, work)
                .map_err(TriangulationError::Ribbon)?;
            let temporary = local_map(&ribbon, catalogue, temporary_gamma, work)?;
            regions.push(collapse(&current, &ribbon, &temporary, &mut queries, work)
                .map_err(TriangulationError::Collapse)?);
        }
        current = graft(&current, regions, work).map_err(TriangulationError::Graft)?;
        restore_visibility(&mut current, &mut queries, work).map_err(TriangulationError::Restore)?;
        for region in current.region_ids() {
            work.retained_visits += 1;
            let weight = current.region_weight(&boundary, region)
                .map_err(TriangulationError::Map)?;
            if weight > next_gamma {
                return Err(TriangulationError::RefinementWeight { region, weight, limit: next_gamma });
            }
        }
        current.coarsen_visibility(&boundary, next_gamma, work).map_err(TriangulationError::Map)?;
        gamma = next_gamma;
    }
    complete(&mut current, work).map_err(TriangulationError::Completion)?;
    Ok(current)
}

/// Construct complete horizontal visibility of an immutable padded input.
/// Arithmetic is exact; bit complexity is separate from counted primitives.
pub fn visibility<'a>(input: &'a Input, work: &mut Work)
    -> Result<Submap<'a>, TriangulationError>
{
    let mut catalogue = Catalogue::build(input, 4, &mut OriginalMerge, work)
        .map_err(TriangulationError::Hierarchy)?;
    let gamma = granularity(grade(input.edge_count())).map_err(TriangulationError::Cut)?;
    let root = catalogue.take_root().map_err(TriangulationError::Cut)?;
    refine(root, gamma, &catalogue, work)
}

/// Triangulate a simple polygon, returning nondegenerate CCW original vertex IDs.
///
/// Vertices must be pairwise distinct and describe a simple, nonzero-area
/// polygon without repeating the closing vertex. Either winding and consecutive
/// collinear vertices are accepted. Simplicity and distinctness are caller
/// preconditions, not an expected-time hash or a slower validation pass.
/// `work` accumulates primitive counts; it is not reset by this function.
pub fn triangulate(points: &[Point], work: &mut Work)
    -> Result<Vec<[usize; 3]>, TriangulationError>
{
    let input = Input::polygon(points).map_err(TriangulationError::Input)?;
    let map = visibility(&input, work)?;
    let closed = close_visibility(&map, work).map_err(TriangulationError::Closure)?;
    triangulate_visibility(&closed.vertices, &closed.cells, work)
        .map_err(TriangulationError::Reduction)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geometry::{Rational, orientation};
    use crate::input::VertexId;
    use crate::scalar::ExactScalar;
    use std::cmp::Ordering;
    use std::collections::BTreeMap;

    fn area2(a: &Point, b: &Point, c: &Point) -> Rational {
        (&b.x - &a.x) * (&c.y - &a.y) - (&b.y - &a.y) * (&c.x - &a.x)
    }

    fn check(points: &[Point], triangles: &[[usize; 3]]) {
        assert_eq!(triangles.len(), points.len() - 2);
        let polygon = points.iter().zip(points.iter().cycle().skip(1)).take(points.len())
            .fold(Rational::zero_value(), |sum, (a, b)| sum + &a.x * &b.y - &a.y * &b.x);
        let mut total = Rational::zero_value();
        let mut edges = BTreeMap::new();
        for &[a, b, c] in triangles {
            assert!(a < points.len() && b < points.len() && c < points.len());
            assert_eq!(orientation(&points[a], &points[b], &points[c]), Ordering::Greater);
            total += area2(&points[a], &points[b], &points[c]);
            for (u, v) in [(a, b), (b, c), (c, a)] {
                *edges.entry((u.min(v), u.max(v))).or_insert(0usize) += 1;
            }
        }
        assert_eq!(total, polygon.absolute());
        for i in 0..points.len() {
            let j = (i + 1) % points.len();
            assert_eq!(edges.remove(&(i.min(j), i.max(j))), Some(1));
        }
        assert!(edges.values().all(|&count| count == 2));
    }

    #[test]
    fn complete_api_preserves_original_boundary_and_exact_area() {
        let shapes = [
            vec![(0,0), (5,0), (1,3)],
            vec![(0,0), (2,0), (4,0), (4,4), (0,4)],
            vec![(0,0), (6,0), (6,2), (2,2), (2,6), (0,6)],
            vec![(0,0), (8,0), (8,1), (2,1), (2,3), (8,3), (8,4), (0,4)],
        ];
        for shape in shapes {
            let original: Vec<_> = shape.into_iter().map(|(x, y)| Point::integer(x, y)).collect();
            for rational in [false, true] {
                let mut points: Vec<_> = original.iter().map(|p| if rational {
                    Point::new(&p.x * Rational::new(3.into(), 7.into())
                        + &p.y * Rational::new(1.into(), 7.into()) + Rational::new(1.into(), 11.into()),
                        &p.x * Rational::new(1.into(), 13.into())
                        + &p.y * Rational::new(2.into(), 13.into()) - Rational::new(2.into(), 17.into()))
                } else { p.clone() }).collect();
                for _ in 0..2 {
                    let triangles = triangulate(&points, &mut Work::default()).unwrap();
                    check(&points, &triangles);
                    points.reverse();
                }
            }
        }
    }

    #[test]
    fn actual_coarse_down_phase_then_original_only_reduction() {
        let mut points: Vec<_> = (0..=24).map(|x| Point::integer(x, -3 - 2 * (x % 5))).collect();
        points.extend((0..=24).rev().map(|x| Point::integer(x, 13 + 2 * (x % 7))));
        let input = Input::polygon(&points).unwrap();
        let mut work = Work::default();
        let catalogue = Catalogue::build(&input, 4, &mut OriginalMerge, &mut work).unwrap();
        let mut coarse = catalogue.saved(grade(input.edge_count()), VertexId(0))
            .unwrap().oracle.map().clone();
        let boundary = Boundary::new(&input, coarse.chain()).unwrap();
        coarse.coarsen_visibility(&boundary, 32, &mut work).unwrap();
        assert!(coarse.region_ids().any(|region| coarse.region_weight(&boundary, region).unwrap() > 16));
        let map = refine(coarse, 32, &catalogue, &mut work).unwrap();
        assert!(map.decomposition().is_none());
        let closed = close_visibility(&map, &mut work).unwrap();
        let triangles = triangulate_visibility(&closed.vertices, &closed.cells, &mut work).unwrap();
        check(&points, &triangles);
    }
}
