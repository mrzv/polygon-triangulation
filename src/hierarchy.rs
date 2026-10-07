//! Immutable aligned-chain catalogue and the saved-chain oracles of §4.1.
//!
//! Only retained topology is copied. Arbitrary intervals depend strictly on
//! earlier grades; their pieces share one granularity and merge in a balanced
//! tree. Arc cuts use the double boundary's constant-size side runs, never a
//! scan of the supporting input curve.
use crate::boundary::{Boundary, BoundaryError, Chain, Position, Side, Site};
use crate::geometry::Rational;
use crate::input::{EdgeId, Input, VertexId};
use crate::oracle::{OracleError, RayOracle};
use crate::submap::{MapError, Submap};
use crate::work::Work;
use num_traits::{One, Zero};
use std::fmt;

pub trait MergeEngine<'a> {
    type Error;
    /// Construct the actual visibility map of a bounded early-grade chain.
    fn base_map(&mut self, boundary: Boundary<'a>, work: &mut Work)
        -> Result<Submap<'a>, Self::Error>;
    /// Fuse contiguous maps using the immutable saved smaller-grade oracles.
    fn merge(&mut self, left: &Submap<'a>, right: &Submap<'a>, target_gamma: usize,
        catalogue: &Catalogue<'a>, work: &mut Work) -> Result<Submap<'a>, Self::Error>;
}

#[derive(Debug)]
pub enum CutError {
    Boundary(BoundaryError),
    InvalidInterval,
    Unaligned { grade: usize, start: VertexId },
    MissingSaved { grade: usize, start: VertexId },
    SizeOverflow,
    DifferentInput,
}
impl From<BoundaryError> for CutError {
    fn from(error: BoundaryError) -> Self { Self::Boundary(error) }
}
impl fmt::Display for CutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for CutError {}

#[derive(Debug)]
pub enum HierarchyError<E> {
    Cut(CutError),
    Map(MapError),
    Oracle(OracleError),
    Engine(E),
    WrongMap,
    NotGranular,
}
impl<E> From<CutError> for HierarchyError<E> {
    fn from(error: CutError) -> Self { Self::Cut(error) }
}
impl<E> From<BoundaryError> for HierarchyError<E> {
    fn from(error: BoundaryError) -> Self { Self::Cut(CutError::Boundary(error)) }
}
impl<E> From<MapError> for HierarchyError<E> {
    fn from(error: MapError) -> Self { Self::Map(error) }
}
impl<E> From<OracleError> for HierarchyError<E> {
    fn from(error: OracleError) -> Self { Self::Oracle(error) }
}
impl<E: fmt::Debug> fmt::Display for HierarchyError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl<E: fmt::Debug> std::error::Error for HierarchyError<E> {}

/// ceil(log2(m)); grade zero is the single-edge base case (also zero for m=0).
pub fn grade(m: usize) -> usize {
    if m <= 1 { 0 } else { (usize::BITS - (m - 1).leading_zeros()) as usize }
}
/// Exact beta=1/5 canonical granularity, without floating-point rounding.
pub fn granularity(lambda: usize) -> Result<usize, CutError> {
    let exponent = lambda / 5 + usize::from(lambda % 5 != 0);
    let shift = u32::try_from(exponent).map_err(|_| CutError::SizeOverflow)?;
    1usize.checked_shl(shift).ok_or(CutError::SizeOverflow)
}
fn span(mu: usize) -> Result<usize, CutError> {
    let shift = u32::try_from(mu).map_err(|_| CutError::SizeOverflow)?;
    1usize.checked_shl(shift).ok_or(CutError::SizeOverflow)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AlignedChain { pub grade: usize, pub start: VertexId }

/// Maximal aligned dyadic cover with an explicit inclusive grade cutoff.
/// The two end fringes contribute at most two pieces per uncapped grade.
pub fn partition(start: VertexId, end: VertexId, max_grade: usize)
    -> Result<Vec<AlignedChain>, CutError>
{
    if start.0 > end.0 { return Err(CutError::InvalidInterval); }
    let mut pieces = Vec::new();
    let mut at = start.0;
    while at < end.0 {
        let remaining = end.0 - at;
        let fits = (usize::BITS - 1 - remaining.leading_zeros()) as usize;
        let aligned = if at == 0 { fits } else { at.trailing_zeros() as usize };
        let mu = fits.min(aligned).min(max_grade);
        pieces.push(AlignedChain { grade: mu, start: VertexId(at) });
        at += span(mu)?;
    }
    Ok(pieces)
}

pub struct SavedChain<'a> {
    pub grade: usize,
    pub start: VertexId,
    pub oracle: RayOracle<'a>,
}

pub struct Catalogue<'a> {
    input: &'a Input,
    grades: Vec<Vec<SavedChain<'a>>>,
}

/// Bounds on direct pieces are always input-forward; Right traverses end to
/// start. Saved chains likewise retain input-forward geometry on either side.
pub enum Piece<'c, 'a> {
    Saved { chain: &'c SavedChain<'a>, side: Side },
    Edge { edge: EdgeId, side: Side, start: Rational, end: Rational },
}

impl<'a> Catalogue<'a> {
    pub fn build<E: MergeEngine<'a>>(input: &'a Input, base_grade: usize,
        engine: &mut E, work: &mut Work) -> Result<Self, HierarchyError<E::Error>>
    {
        let n = input.edge_count();
        if n == 0 || !n.is_power_of_two() { return Err(CutError::InvalidInterval.into()); }
        let top = grade(n);
        let mut catalogue = Self { input, grades: Vec::with_capacity(top + 1) };
        // Grade one must be direct: ceil(lambda/5)=lambda there. Beyond it,
        // every arc-cut dependency is strictly earlier than the current grade.
        let base_grade = base_grade.max(1).min(top);
        for mu in 0..=top {
            let length = span(mu)?;
            let gamma = granularity(mu)?;
            let mut saved = Vec::with_capacity(n / length);
            for start in (0..n).step_by(length) {
                let chain = Chain::new(input, VertexId(start), VertexId(start + length))?;
                let boundary = Boundary::new(input, chain)?;
                let mut map = if mu <= base_grade {
                    engine.base_map(boundary, work).map_err(HierarchyError::Engine)?
                } else {
                    catalogue.interval(chain.start, chain.end, engine, work)?
                };
                catalogue.prepare(&mut map, boundary, gamma, work)?;
                let oracle = RayOracle::build(map, gamma, work)?;
                saved.push(SavedChain { grade: mu, start: chain.start, oracle });
            }
            // Publish the entire grade atomically. Even earlier chains within
            // this grade are not visible to the engine constructing its peers.
            catalogue.grades.push(saved);
        }
        Ok(catalogue)
    }

    pub fn input(&self) -> &'a Input { self.input }
    pub fn grade_count(&self) -> usize { self.grades.len() }
    /// Move the whole-curve map into the down-phase without copying topology.
    ///
    /// Its saved oracle is removed. Down-phase queries use strictly smaller
    /// grades; attempting to query the removed entry returns `MissingSaved`.
    pub fn take_root(&mut self) -> Result<Submap<'a>, CutError> {
        let mu = grade(self.input.edge_count());
        let missing = || CutError::MissingSaved { grade: mu, start: VertexId(0) };
        let root = self.grades.get_mut(mu).ok_or_else(missing)?.pop().ok_or_else(missing)?;
        Ok(root.oracle.into_map())
    }
    pub fn saved(&self, mu: usize, start: VertexId) -> Result<&SavedChain<'a>, CutError> {
        let length = span(mu)?;
        if start.0 % length != 0 { return Err(CutError::Unaligned { grade: mu, start }); }
        self.grades.get(mu).and_then(|g| g.get(start.0 / length))
            .ok_or(CutError::MissingSaved { grade: mu, start })
    }

    fn prepare<E>(&self, map: &mut Submap<'a>, boundary: Boundary<'a>, gamma: usize,
        work: &mut Work) -> Result<(), HierarchyError<E>>
    {
        if !std::ptr::eq(map.input(), self.input) || map.chain() != boundary.chain() {
            return Err(HierarchyError::WrongMap);
        }
        map.coarsen(&boundary, gamma, work)?;
        for region in map.region_ids() {
            work.retained_visits += 1;
            if map.region_weight(&boundary, region)? > gamma { return Err(HierarchyError::NotGranular); }
        }
        Ok(())
    }

    pub fn interval<E: MergeEngine<'a>>(&self, start: VertexId, end: VertexId,
        engine: &mut E, work: &mut Work) -> Result<Submap<'a>, HierarchyError<E::Error>>
    {
        let chain = Chain::new(self.input, start, end)?;
        let lambda = grade(chain.edge_count());
        let target = granularity(lambda)?;
        if lambda == 0 {
            let mut map = self.saved(0, start)?.oracle.map().clone();
            self.prepare(&mut map, Boundary::new(self.input, chain)?, target, work)?;
            return Ok(map);
        }
        let cover = partition(start, end, lambda - 1)?;
        let mut maps = Vec::with_capacity(cover.len());
        for piece in cover {
            let mut map = self.saved(piece.grade, piece.start)?.oracle.map().clone();
            let boundary = Boundary::new(self.input, map.chain())?;
            let effective = target.min(boundary.chain().edge_count().saturating_mul(2));
            self.prepare(&mut map, boundary, effective, work)?;
            maps.push(map);
        }
        let count = maps.len();
        self.merge_balanced(&mut maps.into_iter(), count, target, engine, work)
    }

    fn merge_balanced<E: MergeEngine<'a>>(&self, maps: &mut std::vec::IntoIter<Submap<'a>>,
        count: usize, target: usize, engine: &mut E, work: &mut Work)
        -> Result<Submap<'a>, HierarchyError<E::Error>>
    {
        if count == 1 { return maps.next().ok_or(CutError::InvalidInterval.into()); }
        if count == 0 { return Err(CutError::InvalidInterval.into()); }
        let left = self.merge_balanced(maps, count / 2, target, engine, work)?;
        let right = self.merge_balanced(maps, count - count / 2, target, engine, work)?;
        let chain = Chain::new(self.input, left.chain().start, right.chain().end)?;
        if left.chain().end != right.chain().start { return Err(HierarchyError::WrongMap); }
        let mut map = engine.merge(&left, &right, target, self, work).map_err(HierarchyError::Engine)?;
        let effective = target.min(chain.edge_count().saturating_mul(2));
        self.prepare(&mut map, Boundary::new(self.input, chain)?, effective, work)?;
        Ok(map)
    }

    /// Replace the caller's scratch contents, retaining its allocation.
    pub fn cut_arc<'c>(&'c self, boundary: Boundary<'a>, start: &Site, end: &Site,
        full: bool, max_saved_grade: usize, pieces: &mut Vec<Piece<'c, 'a>>)
        -> Result<(), CutError>
    {
        pieces.clear();
        if !std::ptr::eq(boundary.input(), self.input) { return Err(CutError::DifferentInput); }
        let start = boundary.normalize_site(start)?;
        let end = boundary.normalize_site(end)?;
        let arc = boundary.arc(&start, &end, full)?;
        for run in boundary.runs(&arc) {
            let begin = pieces.len();
            let (low, high) = if run.side == Side::Left { (run.from, run.to) } else { (run.to, run.from) };
            if let (Position::Edge { edge: a, t: lo }, Position::Edge { edge: b, t: hi }) = (low, high) {
                if a == b {
                    if lo < hi { pieces.push(Piece::Edge { edge: a, side: run.side, start: lo.clone(), end: hi.clone() }); }
                    continue;
                }
            }
            let first = match low {
                Position::Vertex(v) => v,
                Position::Edge { edge, t } => {
                    pieces.push(Piece::Edge { edge, side: run.side, start: t.clone(), end: Rational::one() });
                    VertexId(edge.0 + 1)
                }
            };
            let last = match high { Position::Vertex(v) => v, Position::Edge { edge, .. } => VertexId(edge.0) };
            if first.0 > last.0 { return Err(CutError::InvalidInterval); }
            let mut at = first.0;
            while at < last.0 {
                let remaining = last.0 - at;
                let fits = (usize::BITS - 1 - remaining.leading_zeros()) as usize;
                let aligned = if at == 0 { fits } else { at.trailing_zeros() as usize };
                let mu = fits.min(aligned).min(max_saved_grade);
                pieces.push(Piece::Saved { chain: self.saved(mu, VertexId(at))?, side: run.side });
                at += span(mu)?;
            }
            if let Position::Edge { edge, t } = high {
                pieces.push(Piece::Edge { edge, side: run.side, start: Rational::zero(), end: t.clone() });
            }
            if run.side == Side::Right { pieces[begin..].reverse(); }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::base::{BaseError, full_visibility};
    use crate::boundary::Slot;
    use crate::geometry::Point;
    use std::collections::BTreeMap;

    // This test engine computes genuine complete visibility geometry, only
    // within the production base routine's fixed bound. It is not an echo
    // oracle or a replacement for the unbounded production fusion engine.
    #[derive(Default)]
    struct BoundedGeometry {
        depths: BTreeMap<(usize, usize), usize>,
        max_depth: usize,
    }
    impl<'a> MergeEngine<'a> for BoundedGeometry {
        type Error = BaseError;
        fn base_map(&mut self, boundary: Boundary<'a>, work: &mut Work)
            -> Result<Submap<'a>, BaseError>
        {
            full_visibility(boundary, work)
        }
        fn merge(&mut self, left: &Submap<'a>, right: &Submap<'a>, _: usize,
            catalogue: &Catalogue<'a>, work: &mut Work) -> Result<Submap<'a>, BaseError>
        {
            let a = left.chain();
            let b = right.chain();
            assert_eq!(a.end, b.start);
            let depth = 1 + self.depths.get(&(a.start.0, a.end.0)).copied().unwrap_or(0)
                .max(self.depths.get(&(b.start.0, b.end.0)).copied().unwrap_or(0));
            self.depths.insert((a.start.0, b.end.0), depth);
            self.max_depth = self.max_depth.max(depth);
            full_visibility(Boundary::new(catalogue.input(),
                Chain::new(catalogue.input(), a.start, b.end).unwrap()).unwrap(), work)
        }
    }
    fn input() -> Input {
        Input::open(&(0..=8).map(|i| Point::integer(0, i)).collect::<Vec<_>>()).unwrap()
    }
    fn boundary(input: &Input) -> Boundary<'_> {
        Boundary::new(input, Chain::new(input, VertexId(0), VertexId(8)).unwrap()).unwrap()
    }
    fn vertex(v: usize, side: Side) -> Site {
        Site::Vertex { vertex: VertexId(v), side, slot: Slot::Single }
    }
    fn edge(e: usize, numerator: i64, denominator: i64, side: Side) -> Site {
        Site::Edge { edge: EdgeId(e), t: Rational::new(numerator.into(), denominator.into()), side }
    }
    fn catalogue(input: &Input) -> Catalogue<'_> {
        Catalogue::build(input, 4, &mut BoundedGeometry::default(), &mut Work::default()).unwrap()
    }
    fn assert_granular(map: &Submap<'_>, gamma: usize) {
        let b = Boundary::new(map.input(), map.chain()).unwrap();
        assert!(map.decomposition().is_some());
        for r in map.region_ids() {
            assert!(map.region_exits(r).unwrap().len() <= 4);
            assert!(map.region_weight(&b, r).unwrap() <= gamma);
        }
    }
    fn edge_order(pieces: &[Piece<'_, '_>]) -> Vec<(Side, usize, Rational, Rational)> {
        let mut result = Vec::new();
        for piece in pieces {
            match piece {
                Piece::Edge { edge, side, start, end } => {
                    result.push((*side, edge.0, start.clone(), end.clone()));
                }
                Piece::Saved { chain, side } => {
                    let c = chain.oracle.map().chain();
                    let mut edges: Vec<_> = (c.start.0..c.end.0).collect();
                    if *side == Side::Right { edges.reverse(); }
                    result.extend(edges.into_iter().map(|e| (*side, e, Rational::zero(), Rational::one())));
                }
            }
        }
        result
    }

    #[test]
    fn integer_canonical_scales_and_strict_dyadic_cover() {
        for lambda in 0..=30 {
            assert_eq!(granularity(lambda).unwrap(), 1usize << ((lambda + 4) / 5));
        }
        for start in 0..32 {
            for length in 2..=32 {
                let lambda = grade(length);
                let pieces = partition(VertexId(start), VertexId(start + length), lambda - 1).unwrap();
                let mut at = start;
                let mut counts = vec![0; lambda];
                for p in &pieces {
                    assert!(p.grade < lambda);
                    assert_eq!(p.start.0, at);
                    assert_eq!(at % (1 << p.grade), 0);
                    counts[p.grade] += 1;
                    at += 1 << p.grade;
                }
                assert_eq!(at, start + length);
                assert!(counts.iter().all(|&count| count <= 2));
                assert!(pieces.len() <= 2 * lambda);
            }
        }
        assert_eq!(partition(VertexId(0), VertexId(8), 2).unwrap(),
            [AlignedChain { grade: 2, start: VertexId(0) },
             AlignedChain { grade: 2, start: VertexId(4) }]);
    }

    #[test]
    fn saved_base_topology_and_non_circular_balanced_intervals() {
        let input = input();
        let saved = catalogue(&input);
        for mu in 0..saved.grade_count() {
            for chain in &saved.grades[mu] {
                assert!(std::ptr::eq(chain.oracle.map().input(), &input));
                assert_granular(chain.oracle.map(), granularity(mu).unwrap());
            }
        }
        // Delete the current grade from this separately owned test catalogue:
        // even a whole aligned interval must use its two saved children.
        let smaller = Catalogue { input: &input, grades: saved.grades.into_iter().take(3).collect() };
        let mut engine = BoundedGeometry::default();
        let map = smaller.interval(VertexId(0), VertexId(8), &mut engine, &mut Work::default()).unwrap();
        assert_eq!(map.chain(), Chain { start: VertexId(0), end: VertexId(8) });
        assert_granular(&map, 2);
        assert_eq!(engine.max_depth, 1);
        let mut engine = BoundedGeometry::default();
        let map = smaller.interval(VertexId(1), VertexId(8), &mut engine, &mut Work::default()).unwrap();
        assert_granular(&map, 2);
        assert_eq!(engine.max_depth, 2);
        let one = smaller.interval(VertexId(3), VertexId(4), &mut engine, &mut Work::default()).unwrap();
        assert_granular(&one, 1);
    }

    #[test]
    fn clipped_arc_crosses_both_caps_in_clockwise_order() {
        let input = input();
        let saved = catalogue(&input);
        let b = boundary(&input);
        let start = edge(3, 1, 4, Side::Left);
        let end = edge(1, 3, 4, Side::Left);
        let mut pieces = Vec::new();
        saved.cut_arc(b, &start, &end, false, 1, &mut pieces).unwrap();
        assert_eq!(pieces.iter().filter(|p| matches!(p, Piece::Edge { .. })).count(), 2);
        let actual = edge_order(&pieces);
        let mut expected = Vec::new();
        expected.push((Side::Left, 3, Rational::new(1.into(), 4.into()), Rational::one()));
        expected.extend((4..8).map(|e| (Side::Left, e, Rational::zero(), Rational::one())));
        expected.extend((0..8).rev().map(|e| (Side::Right, e, Rational::zero(), Rational::one())));
        expected.push((Side::Left, 0, Rational::zero(), Rational::one()));
        expected.push((Side::Left, 1, Rational::zero(), Rational::new(3.into(), 4.into())));
        assert_eq!(actual, expected);
        assert_eq!(b.runs(&b.arc(&start, &end, false).unwrap()).count(), 3);
    }

    #[test]
    fn empty_full_normalized_and_same_edge_right_cuts() {
        let input = input();
        let saved = catalogue(&input);
        let b = boundary(&input);
        let cap = vertex(0, Side::Left);
        let mut pieces = Vec::new();
        saved.cut_arc(b, &cap, &cap, false, 1, &mut pieces).unwrap();
        assert!(pieces.is_empty());
        saved.cut_arc(b, &cap, &cap, true, 1, &mut pieces).unwrap();
        assert_eq!(edge_order(&pieces).len(), 16);
        assert!(pieces.iter().all(|p| matches!(p, Piece::Saved { .. })));
        let from = edge(2, 3, 4, Side::Right);
        let to = edge(2, 1, 4, Side::Right);
        saved.cut_arc(b, &from, &to, false, 1, &mut pieces).unwrap();
        assert_eq!(edge_order(&pieces), [(Side::Right, 2,
            Rational::new(1.into(), 4.into()), Rational::new(3.into(), 4.into()))]);
        saved.cut_arc(b, &edge(0, 0, 1, Side::Left),
            &edge(1, 1, 1, Side::Left), false, 1, &mut pieces).unwrap();
        assert_eq!(edge_order(&pieces), [(Side::Left, 0, Rational::zero(), Rational::one()),
            (Side::Left, 1, Rational::zero(), Rational::one())]);
        drop(pieces);
        let only_base = Catalogue { input: &input, grades: saved.grades.into_iter().take(1).collect() };
        assert!(matches!(only_base.cut_arc(b, &cap, &vertex(4, Side::Left), false, 2, &mut Vec::new()),
            Err(CutError::MissingSaved { grade: 2, .. })));
    }

    #[test]
    fn production_base_bound_errors_propagate_without_fallback() {
        let input = Input::open(&(0..=32).map(|i| Point::integer(0, i)).collect::<Vec<_>>()).unwrap();
        let result = Catalogue::build(&input, 5, &mut BoundedGeometry::default(), &mut Work::default());
        assert!(matches!(result, Err(HierarchyError::Engine(_))));
    }
}
