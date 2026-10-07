//! Constant-granularity completion on the original curve. Geometry is confined
//! to each old region's bounded boundary; publication does not build a query tree.

use crate::arcs::ArcShot;
use crate::boundary::{Boundary, BoundaryError, Side, Site, Slot};
use crate::curve::LevelSource;
use crate::geometry::{contact_route, ray_order, Route};
use crate::input::Input;
use crate::submap::{MapError, RegionId, Submap, VisibleChord};
use crate::work::Work;
use std::cmp::Ordering;
use std::fmt;

pub const FIXED_COMPLETION_GRANULARITY: usize = 16;

#[derive(Debug)]
pub enum CompletionError {
    Boundary(BoundaryError),
    Map(MapError),
    OversizedArc { weight: usize },
    MissingArrival,
    AmbiguousArrival,
    ConflictingPartner,
}
impl fmt::Display for CompletionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for CompletionError {}
impl From<BoundaryError> for CompletionError {
    fn from(error: BoundaryError) -> Self { Self::Boundary(error) }
}
impl From<MapError> for CompletionError {
    fn from(error: MapError) -> Self { Self::Map(error) }
}

struct Clip { start: Site, end: Site, full: bool, weight: usize, uncut: bool, flags: Vec<Site> }
struct OldRegion { id: RegionId, clips: Vec<Clip> }

fn closed(boundary: Boundary<'_>, clip: &Clip, site: &Site) -> bool {
    site == &clip.start || site == &clip.end || boundary.contains_site(
        &boundary.arc(&clip.start, &clip.end, clip.full).unwrap(), site)
}

/// Complete every missing intrinsic original flag. Old occupied flags are
/// authoritative: their legal original-visibility chords are never reshot.
pub fn complete<'a>(map: &mut Submap<'a, Input>, work: &mut Work) -> Result<(), CompletionError> {
    let boundary = Boundary::new(map.input(), map.chain())?;
    let mut old_regions = Vec::new();
    // Validate every weight by index arithmetic before visiting any input edge.
    for id in map.region_ids() {
        work.retained_visits += 1;
        let arcs = map.region_arcs(id)?;
        if map.region_exits(id)?.len() > 4 || arcs.len() > 4 {
            return Err(MapError::NonConformal.into());
        }
        let mut clips = Vec::with_capacity(arcs.len());
        for &arc in arcs {
            work.retained_visits += 1;
            let (start, end, full, uncut) = match map.arc_sites(arc) {
                Some((a, b, full)) => (a.clone(), b.clone(), full, false),
                None => {
                    let site = Site::Vertex { vertex: map.chain().start, side: Side::Left, slot: Slot::Single };
                    (site.clone(), site, true, true)
                }
            };
            work.predicates += 1;
            let weight = boundary.arc_weight(&start, &end, full)?;
            if weight > FIXED_COMPLETION_GRANULARITY { return Err(CompletionError::OversizedArc { weight }); }
            let descriptor = boundary.arc(&start, &end, full)?;
            let mut flags = Vec::new();
            for flag in boundary.arc_occurrences(&descriptor) {
                work.retained_visits += 1;
                work.predicates += 1;
                if flag == start || flag == end || boundary.contains_site(&descriptor, &flag) {
                    flags.push(flag);
                }
            }
            clips.push(Clip { start, end, full, weight, uncut, flags });
        }
        old_regions.push(OldRegion { id, clips });
    }
    for old in old_regions {
        let mut sources = Vec::new();
        for clip in &old.clips {
            for source in &clip.flags {
                work.retained_visits += 1;
                if old.clips.iter().any(|c| !c.uncut && (&c.start == source || &c.end == source)) { continue; }
                if !sources.contains(source) { sources.push(source.clone()); }
            }
        }
        let mut additions: Vec<VisibleChord> = Vec::new();
        for source in sources {
            work.predicates += 1;
            let (target, route) = if let Some(target) = boundary.null_contact(&source)? {
                (target, Route::Null)
            } else {
                let point = boundary.point(&source)?;
                let direction = boundary.direction(&source)?;
                let mut best: Option<ArcShot> = None;
                for clip in &old.clips {
                    let arc = boundary.arc(&clip.start, &clip.end, clip.full)?;
                    // hits enumerates precisely these positive original pieces,
                    // including both cap connectors and zero-weight null arcs.
                    work.arc_edge_visits += clip.weight as u128;
                    work.predicates += clip.weight as u128;
                    // hits tests every intrinsic level, including level misses.
                    work.retained_visits += clip.flags.len() as u128;
                    work.predicates += clip.flags.len() as u128;
                    for hit in boundary.hits(&arc, &point.y) {
                        work.retained_visits += 1;
                        work.predicates += 1;
                        if !closed(boundary, clip, &hit.site) { continue; }
                        let order = best.as_ref().map_or(Ordering::Less, |old| {
                            work.predicates += 1;
                            ray_order(&point.x, direction, &hit.x, &old.x)
                        });
                        if order == Ordering::Greater { continue; }
                        if order == Ordering::Less {
                            best = Some(ArcShot::new(hit.x.clone(), contact_route(&point.x, &hit.x, direction)));
                        }
                        best.as_mut().unwrap().push_contact(hit.site);
                    }
                }
                let best = best.ok_or(CompletionError::MissingArrival)?;
                let mut arrival = None;
                for hit in best.contacts() {
                    work.predicates += 2;
                    if hit == &source || boundary.inside_null_pair(hit)?
                        || !boundary.contact_faces_ray(hit, direction)? { continue; }
                    if arrival.as_ref().is_some_and(|old| old != hit) {
                        return Err(CompletionError::AmbiguousArrival);
                    }
                    arrival = Some(hit.clone());
                }
                let target = arrival.ok_or(CompletionError::MissingArrival)?;
                boundary.validate_route(&source, &target, direction, best.route)?;
                (target, best.route)
            };
            let mut duplicate = false;
            for chord in &additions {
                work.retained_visits += 1;
                work.predicates += 1;
                if (chord.endpoints[0] == source && chord.endpoints[1] == target)
                    || (chord.endpoints[1] == source && chord.endpoints[0] == target) {
                    if chord.route != route { return Err(CompletionError::ConflictingPartner); }
                    duplicate = true;
                    break;
                }
                if chord.endpoints.iter().any(|s| s == &source || s == &target) {
                    return Err(CompletionError::ConflictingPartner);
                }
            }
            if !duplicate {
                let Site::Vertex { vertex, .. } = source else { unreachable!() };
                additions.push(VisibleChord { endpoints: [source, target], route, level: LevelSource::Vertex(vertex) });
            }
        }
        // These descendants belong only to this old region. Each insertion
        // creates one more, bounded by the old region's intrinsic flag count.
        let mut descendants = vec![old.id];
        for chord in additions {
            let region = descendants.iter().copied().find(|&id| {
                chord.endpoints.iter().all(|site| {
                    map.region_arcs(id).unwrap().iter().any(|&arc| {
                        work.retained_visits += 1;
                        work.predicates += 3;
                        let Some((start, end, full)) = map.arc_sites(arc) else { return true; };
                        site != start && site != end && boundary.contains_site(
                            &boundary.arc(start, end, full).unwrap(), site)
                    })
                })
            }).ok_or(MapError::PointOutsideRegion)?;
            let id = map.insert_verified(&boundary, region, chord)?;
            for id in map.chord_regions(id)? {
                if !descendants.contains(&id) { descendants.push(id); }
            }
        }
    }
    map.publish_visibility(&boundary, work)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::base::full_visibility;
    use crate::boundary::Chain;
    use crate::geometry::Point;
    use crate::hierarchy::Catalogue;
    use crate::input::VertexId;
    use crate::merge::OriginalMerge;

    fn boundary(input: &Input) -> Boundary<'_> {
        Boundary::new(input, Chain::new(input, VertexId(0), VertexId(input.len() - 1)).unwrap()).unwrap()
    }

    fn same_chords(a: &Submap<'_>, b: &Submap<'_>) {
        assert_eq!(a.chord_ids().count(), b.chord_ids().count());
        for id in a.chord_ids() {
            let (ends, route) = a.chord(id).unwrap();
            assert!(b.chord_ids().any(|id| {
                let (other, other_route) = b.chord(id).unwrap();
                route == other_route && (ends == other || ends == [other[1], other[0]])
            }), "missing chord {ends:?} {route:?}");
        }
    }

    #[test]
    fn bounded_coarse_consumers_restore_nulls_caps_wraps_and_polygon_seams() {
        let fixtures = [
            (false, vec![(0,0),(2,4),(4,0)]),
            (false, vec![(0,4),(1,0),(2,3),(3,1),(4,5),(5,0),(6,4)]),
            (false, vec![(0,0),(1,0),(2,0),(3,0),(4,0)]),
            (true, vec![(0,0),(6,0),(6,5),(4,2),(2,5),(0,5)]),
        ];
        for (polygon, coordinates) in fixtures {
            let points: Vec<_> = coordinates.into_iter().map(|(x,y)| Point::integer(x,y)).collect();
            let input = if polygon { Input::polygon(&points) } else { Input::open(&points) }.unwrap();
            assert!(input.edge_count() <= 16);
            let b = boundary(&input);
            let reference = full_visibility(b, &mut Work::default()).unwrap();
            let mut coarse = full_visibility(b, &mut Work::default()).unwrap();
            coarse.coarsen(&b, FIXED_COMPLETION_GRANULARITY, &mut Work::default()).unwrap();
            assert!(coarse.chord_ids().count() < reference.chord_ids().count());
            let mut work = Work::default();
            complete(&mut coarse, &mut work).unwrap();
            same_chords(&coarse, &reference);
            assert!(coarse.decomposition().is_none());
            assert!(!coarse.canonical_arcs().is_empty());
            for &arc in coarse.canonical_arcs() {
                assert!(coarse.region_exits(coarse.arc_region(arc).unwrap()).unwrap().len() <= 4);
            }
            // Canonical publication remains a consumer-ready normal form.
            for edge in 0..input.edge_count() {
                coarse.double_identify(&b, crate::input::EdgeId(edge),
                    &crate::geometry::Rational::new(1.into(), 2.into())).unwrap();
            }
        }
    }

    #[test]
    fn actual_catalogue_completion_has_original_flags_and_first_blockers() {
        for count in [32, 64, 128] {
            let points: Vec<_> = (0..count).map(|i| Point::integer(i,
                if i % 2 == 0 { 0 } else { 3 + i % 5 })).collect();
            let input = Input::open(&points).unwrap();
            let b = boundary(&input);
            let mut engine = OriginalMerge;
            let catalogue = Catalogue::build(&input, 4, &mut engine, &mut Work::default()).unwrap();
            let mut map = catalogue.interval(b.chain().start, b.chain().end,
                &mut engine, &mut Work::default()).unwrap();
            let mut work = Work::default();
            complete(&mut map, &mut work).unwrap();
            // Independent reference geometry is deliberately hard bounded.
            assert!(input.edge_count() <= 128);
            let anchor = Site::Vertex { vertex: b.chain().start, side: Side::Left, slot: Slot::Single };
            let whole = b.arc(&anchor, &anchor, true).unwrap();
            for source in b.occurrences() {
                let matching: Vec<_> = map.chord_ids().filter(|&id|
                    map.chord(id).unwrap().0.contains(&&source)).collect();
                assert_eq!(matching.len(), 1, "{source:?}");
                let (ends, route) = map.chord(matching[0]).unwrap();
                let target = if ends[0] == &source { ends[1] } else { ends[0] };
                if let Some(null) = b.null_contact(&source).unwrap() {
                    assert_eq!(target, &null);
                    assert_eq!(route, Route::Null);
                } else {
                    let direction = b.direction(&source).unwrap();
                    let nearest = b.nearest_contacts(&whole, &source, direction).unwrap().unwrap();
                    assert_eq!(b.point(target).unwrap().x, nearest.x);
                    assert_eq!(route, nearest.route);
                    assert!(nearest.into_iter().any(|hit| hit.site == *target
                        && !b.inside_null_pair(&hit.site).unwrap()
                        && b.contact_faces_ray(&hit.site, direction).unwrap()));
                }
            }
            let size = input.edge_count() as u128;
            assert!(work.arc_edge_visits <= 4096 * size, "{work:?}");
            assert!(work.predicates <= 32768 * size, "{work:?}");
            assert!(work.retained_visits <= 32768 * size, "{work:?}");
        }
    }

    #[test]
    fn oversized_real_arc_is_rejected_before_edge_geometry() {
        let points: Vec<_> = (0..34).map(|i| Point::integer(i,i % 3)).collect();
        let input = Input::open(&points).unwrap();
        let b = boundary(&input);
        let mut map = Submap::from_verified_chords(&b, vec![], &mut Work::default()).unwrap();
        let mut work = Work::default();
        assert!(matches!(complete(&mut map, &mut work), Err(CompletionError::OversizedArc { .. })));
        assert_eq!(work.arc_edge_visits, 0);
        assert_eq!(work.retained_visits, 2);
    }
}
