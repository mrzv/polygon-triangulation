//! Linear assembly of monotone Root cuts into the authoritative old topology.
use std::cmp::Ordering;
use std::fmt;
use crate::boundary::{Arc, Boundary, BoundaryError};
use crate::collapse::CollapsedRegion;
use crate::submap::{MapError, Submap, VisibleChord};
use crate::work::Work;

#[derive(Debug)]
pub enum GraftError {
    Boundary(BoundaryError),
    Map(MapError),
    InvalidPayload,
    WrongArc,
    UnorderedCuts,
}
impl fmt::Display for GraftError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for GraftError {}
impl From<BoundaryError> for GraftError {
    fn from(value: BoundaryError) -> Self { Self::Boundary(value) }
}
impl From<MapError> for GraftError {
    fn from(value: MapError) -> Self { Self::Map(value) }
}

/// Preserve old separators and splice each region's clockwise cut quotient.
/// Local sites are moved, rather than cloned, into the published topology.
pub fn graft<'a>(
    old: &Submap<'a>, regions: Vec<CollapsedRegion>, work: &mut Work,
) -> Result<Submap<'a>, GraftError> {
    let boundary = Boundary::new(old.input(), old.chain())?;
    let mut rows = vec![usize::MAX; old.chord_ids().map(|id| id.0 + 1).max().unwrap_or(0)];
    let mut records = Vec::new();
    for id in old.chord_ids() {
        let (sites, route) = old.chord(id)?;
        rows[id.0] = records.len();
        records.push(VisibleChord {
            endpoints: [sites[0].clone(), sites[1].clone()], route,
            level: old.chord_level(id)?.clone(),
        });
        work.retained_visits += 1;
    }
    let extent = old.canonical_arcs().iter().map(|id| id.0 + 1).max().unwrap_or(0);
    let mut payloads: Vec<Option<Vec<(usize, usize)>>> = (0..extent).map(|_| None).collect();
    let mut live = vec![false; extent];
    for arc in old.canonical_arcs() { live[arc.0] = true; }
    for region in regions {
        let offset = records.len();
        let count = region.chords.len();
        records.extend(region.chords);
        for cuts in region.cuts {
            if cuts.arc.0 >= extent || !live[cuts.arc.0] || payloads[cuts.arc.0].is_some() {
                return Err(GraftError::InvalidPayload);
            }
            let mut mapped = Vec::with_capacity(cuts.endpoints.len());
            for (row, slot) in cuts.endpoints {
                if row >= count || slot > 1 { return Err(GraftError::InvalidPayload); }
                mapped.push((offset + row, slot));
            }
            payloads[cuts.arc.0] = Some(mapped);
        }
    }
    let mut order = Vec::with_capacity(2 * records.len());
    for &arc in old.canonical_arcs() {
        work.retained_visits += 1;
        if let Some(endpoints) = old.arc_endpoints(arc) {
            let (row, slot) = endpoints[0];
            order.push((rows[row.0], slot));
        }
        if let Some(cuts) = payloads[arc.0].take() {
            if let Some((start, end, full)) = old.arc_sites(arc) {
                let original = Arc { start, end, full_circuit: full };
                let mut previous = start;
                let mut crossed_seam = false;
                for &(row, slot) in &cuts {
                    let site = &records[row].endpoints[slot];
                    if !boundary.contains_site(&original, site)
                        || boundary.compare_sites(start, site) == Ordering::Equal
                        || boundary.compare_sites(end, site) == Ordering::Equal {
                        return Err(GraftError::WrongArc);
                    }
                    if boundary.compare_sites(previous, site) == Ordering::Greater {
                        if crossed_seam || boundary.compare_sites(start, end) == Ordering::Less {
                            return Err(GraftError::UnorderedCuts);
                        }
                        crossed_seam = true;
                    }
                    // Once wrapped, returning to the initial side is not monotone.
                    if crossed_seam && boundary.compare_sites(start, site) != Ordering::Greater {
                        return Err(GraftError::UnorderedCuts);
                    }
                    previous = site;
                    work.predicates += 4;
                    work.retained_visits += 1;
                }
            }
            order.extend(cuts);
        }
    }
    Ok(Submap::from_ordered_verified_chords(&boundary, records, order, work)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boundary::{Chain, Side, Site, Slot};
    use crate::curve::LevelSource;
    use crate::geometry::{Point, Route};
    use crate::input::{Input, VertexId};

    #[test]
    fn graft_preserves_authoritative_separators_and_sources() {
        let input = Input::open(&[Point::integer(0,0),Point::integer(0,1)]).unwrap();
        let boundary = Boundary::new(&input, Chain::new(&input,VertexId(0),VertexId(1)).unwrap()).unwrap();
        let records = (0..2).map(|vertex| VisibleChord {
            endpoints: [Side::Left,Side::Right].map(|side| Site::Vertex {
                vertex: VertexId(vertex), side, slot: Slot::Single,
            }),
            route: Route::Wrap, level: LevelSource::Vertex(VertexId(vertex)),
        }).collect();
        let old = Submap::from_verified_chords(&boundary, records, &mut Work::default()).unwrap();
        let new = graft(&old, vec![], &mut Work::default()).unwrap();
        assert_eq!(new.chord_ids().count(),2);
        assert_eq!(new.region_ids().count(),3);
        assert!(new.decomposition().is_none());
        for (a,b) in old.chord_ids().zip(new.chord_ids()) {
            assert_eq!(old.chord(a).unwrap(),new.chord(b).unwrap());
            assert_eq!(old.chord_level(a).unwrap(),new.chord_level(b).unwrap());
        }
        assert_eq!(new.canonical_arcs().len(),old.canonical_arcs().len());
    }
}
