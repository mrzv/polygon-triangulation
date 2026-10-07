//! Chazelle's fusion, visibility-pair restoration, and target-scale contraction.
//!
//! Restoration uses the existing saved-chain witness service. It never scans
//! an input arc to discover a missing chord. The input's region degrees must
//! have the constant bound supplied by fusion; the output degree is at most four.

use crate::arcs::{ArcQueries, ArcQueryError};
use crate::base::{self, BaseError};
use crate::boundary::{Boundary, BoundaryError};
use crate::curve::Curve;
use crate::fusion::{self, FusionError};
use crate::hierarchy::{Catalogue, MergeEngine, grade};
use crate::input::Input;
use crate::submap::{ArcId, MapError, RegionId, Submap, VisibleChord};
use crate::witness::{self, WitnessError};
use crate::work::Work;
use std::fmt;

/// Directed visibility-pair discovery in two nonconsecutive current region arcs.
/// A negative answer concerns original intrinsic sources in the first arc;
/// restoration therefore calls both ordered directions.
pub trait PairQueries<'a, C: Curve> {
    type Error: fmt::Debug;
    fn witness(
        &mut self,
        map: &Submap<'a, C>,
        region: RegionId,
        first: ArcId,
        second: ArcId,
        work: &mut Work,
    ) -> Result<Option<VisibleChord<C::Scalar>>, Self::Error>;
}

impl<'c, 'a> PairQueries<'a, Input> for ArcQueries<'c, 'a> {
    type Error = WitnessError;
    fn witness(
        &mut self,
        map: &Submap<'a>,
        region: RegionId,
        first: ArcId,
        second: ArcId,
        work: &mut Work,
    ) -> Result<Option<VisibleChord>, Self::Error> {
        witness::witness(self, map, region, first, second, work)
    }
}

#[derive(Debug)]
pub enum RestoreError<E> {
    Boundary(BoundaryError),
    Map(MapError),
    Witness(E),
    MissingWitness { region: RegionId, degree: usize },
    InvalidSplit { region: RegionId, degree: usize },
}
impl<E> From<BoundaryError> for RestoreError<E> {
    fn from(value: BoundaryError) -> Self { Self::Boundary(value) }
}
impl<E> From<MapError> for RestoreError<E> {
    fn from(value: MapError) -> Self { Self::Map(value) }
}
impl<E: fmt::Debug> fmt::Display for RestoreError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl<E: fmt::Debug> std::error::Error for RestoreError<E> {}

/// Add separators until every region has at most four exits.
///
/// Nonconsecutive boundary arcs yield two strictly smaller daughter degrees.
/// The potential sum(max(0, degree-4)) drops at each insertion. Added chords
/// only subdivide original arcs, so an existing upper granularity bound remains
/// valid. Normal form is rebuilt once after the insertion batch.
pub fn restore<'a, C: Curve, Q: PairQueries<'a, C>>(
    map: &mut Submap<'a, C>,
    queries: &mut Q,
    work: &mut Work,
) -> Result<(), RestoreError<Q::Error>> {
    restore_core(map, queries, work, false)
}

/// Restore conformality and publish only linear boundary visibility.
pub fn restore_visibility<'a, C: Curve, Q: PairQueries<'a, C>>(
    map: &mut Submap<'a, C>, queries: &mut Q, work: &mut Work,
) -> Result<(), RestoreError<Q::Error>> {
    restore_core(map, queries, work, true)
}

fn restore_core<'a, C: Curve, Q: PairQueries<'a, C>>(
    map: &mut Submap<'a, C>, queries: &mut Q, work: &mut Work, visibility_only: bool,
) -> Result<(), RestoreError<Q::Error>> {
    let boundary = Boundary::new(map.input(), map.chain())?;
    let mut pending: Vec<_> = map.region_ids().map(|region| {
        work.retained_visits += 1;
        region
    }).collect();
    let mut arcs = Vec::new();
    while let Some(region) = pending.pop() {
        work.retained_visits += 1;
        let degree = map.region_exits(region)?.len();
        if degree <= 4 { continue; }
        arcs.clear();
        let first = map.region_arcs(region)?[0];
        let mut arc = first;
        loop {
            work.retained_visits += 1;
            arcs.push(arc);
            arc = map.arc_successor(arc)?;
            if arc == first { break; }
        }
        let mut found = None;
        'pairs: for i in 0..arcs.len() {
            for j in 0..arcs.len() {
                if i == j || (i + 1) % arcs.len() == j || (j + 1) % arcs.len() == i {
                    continue;
                }
                work.retained_visits += 1;
                if let Some(chord) = queries.witness(map, region, arcs[i], arcs[j], work)
                    .map_err(RestoreError::Witness)? {
                    found = Some(chord);
                    break 'pairs;
                }
            }
        }
        let chord = found.ok_or(RestoreError::MissingWitness { region, degree })?;
        let inserted = map.insert_verified(&boundary, region, chord)?;
        let daughters = map.chord_regions(inserted)?;
        let degrees = [map.region_exits(daughters[0])?.len(), map.region_exits(daughters[1])?.len()];
        if degrees.iter().any(|&d| d >= degree) || degrees[0] + degrees[1] != degree + 2 {
            return Err(RestoreError::InvalidSplit { region, degree });
        }
        pending.extend(daughters);
    }
    if visibility_only { map.publish_visibility(&boundary, work)?; }
    else { map.rebuild_normal_form(&boundary, work)?; }
    Ok(())
}

#[derive(Debug)]
pub enum MergeError {
    Base(BaseError),
    Fusion(FusionError<ArcQueryError>),
    Restore(RestoreError<WitnessError>),
    Map(MapError),
    Boundary(BoundaryError),
}
impl fmt::Display for MergeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for MergeError {}

/// The actual merge service used by the original-input saved-chain catalogue.
/// Direct visibility is restricted to the fixed sixteen-edge leaf bound.
#[derive(Default, Debug)]
pub struct OriginalMerge;

impl<'a> MergeEngine<'a> for OriginalMerge {
    type Error = MergeError;
    fn base_map(&mut self, boundary: Boundary<'a>, work: &mut Work)
        -> Result<Submap<'a>, Self::Error> {
        base::full_visibility(boundary, work).map_err(MergeError::Base)
    }
    fn merge(
        &mut self,
        left: &Submap<'a>,
        right: &Submap<'a>,
        target_gamma: usize,
        catalogue: &Catalogue<'a>,
        work: &mut Work,
    ) -> Result<Submap<'a>, Self::Error> {
        let mut queries = ArcQueries::new(catalogue, grade(target_gamma));
        let mut map = fusion::fuse(left, right, &mut queries, work).map_err(MergeError::Fusion)?;
        restore_visibility(&mut map, &mut queries, work).map_err(MergeError::Restore)?;
        let boundary = Boundary::new(map.input(), map.chain()).map_err(MergeError::Boundary)?;
        map.coarsen(&boundary, target_gamma, work).map_err(MergeError::Map)?;
        Ok(map)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boundary::Chain;
    use crate::geometry::Point;
    use crate::input::VertexId;

    struct NoQueries;
    impl<'a> PairQueries<'a, Input> for NoQueries {
        type Error = ();
        fn witness(
            &mut self, _: &Submap<'a>, _: RegionId, _: ArcId, _: ArcId, _: &mut Work,
        ) -> Result<Option<VisibleChord>, ()> {
            panic!("conformal visibility publication must not query");
        }
    }

    #[test]
    fn visibility_restoration_publishes_without_saved_query_tree() {
        let input = Input::open(&[Point::integer(0,0),Point::integer(0,1)]).unwrap();
        let boundary = Boundary::new(&input, Chain::new(&input,VertexId(0),VertexId(1)).unwrap()).unwrap();
        let mut work = Work::default();
        let mut map = Submap::from_verified_chords(&boundary,vec![],&mut work).unwrap();
        assert!(map.decomposition().is_some());
        restore_visibility(&mut map,&mut NoQueries,&mut work).unwrap();
        assert!(map.decomposition().is_none());
        assert_eq!(map.canonical_arcs().len(),1);
        restore(&mut map,&mut NoQueries,&mut work).unwrap();
        assert!(map.decomposition().is_some());
    }
}
