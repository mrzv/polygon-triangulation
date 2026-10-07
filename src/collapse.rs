//! Directed quotient of a local ribbon, with independent old-face repairs.
//!
//! Ordinary Original2 records use their persistent visibility certificate. Only
//! records meeting the bounded star/equal-base packet need saved-arc queries.
//! Endpoint order is transported from the temporary Left tour, never rebuilt by
//! sorting all contacts or by scanning original supports.
use crate::arcs::{ArcQueries, ArcQueryError, ArcShot};
use crate::boundary::{Boundary, BoundaryError, Side, Site, Slot};
use crate::curve::LevelSource;
use crate::geometry::{ray_order, Point, Route};
use crate::input::VertexId;
use crate::program::Programme;
use crate::ribbon::{ProjectedCut, Ribbon, RibbonError};
use crate::submap::{ArcId, MapError, Submap, VisibleChord};
use crate::work::Work;
use std::cmp::Ordering;
use std::fmt;

/// Clockwise endpoint stream in one immutable old arc.
pub struct ArcCuts {
    pub arc: ArcId,
    pub endpoints: Vec<(usize, usize)>,
}

/// Local records; authoritative old exits are owned once by the graft caller.
pub struct CollapsedRegion {
    pub chords: Vec<VisibleChord>,
    pub cuts: Vec<ArcCuts>,
}

#[derive(Debug)]
pub enum CollapseError {
    Boundary(BoundaryError),
    Map(MapError),
    Ribbon(RibbonError),
    Query(ArcQueryError),
    WrongCurve,
    TooManyOldArcs,
    FrozenProductionSource,
    WrongSourceLevel,
    UncertifiedLimit,
    MissingBlocker,
    MissingArrival,
    AmbiguousArrival,
    ConflictingPartner,
    WrongArc,
    NonMonotoneQuotient,
}
impl From<BoundaryError> for CollapseError {
    fn from(error: BoundaryError) -> Self { Self::Boundary(error) }
}
impl From<MapError> for CollapseError {
    fn from(error: MapError) -> Self { Self::Map(error) }
}
impl From<RibbonError> for CollapseError {
    fn from(error: RibbonError) -> Self { Self::Ribbon(error) }
}
impl From<ArcQueryError> for CollapseError {
    fn from(error: ArcQueryError) -> Self { Self::Query(error) }
}
impl fmt::Display for CollapseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for CollapseError {}

struct OldArc {
    id: ArcId,
    start: Site,
    end: Site,
    full: bool,
}
impl OldArc {
    fn contains(&self, boundary: Boundary<'_>, site: &Site) -> Result<bool, CollapseError> {
        Ok(boundary.contains_site(&boundary.arc(&self.start, &self.end, self.full)?, site))
    }
    fn compare(&self, boundary: Boundary<'_>, a: &Site, b: &Site) -> Ordering {
        // Unwrap at this arc's start, including arcs crossing a Root cap.
        let wrapped = |site: &Site| boundary.compare_sites(site, &self.start) == Ordering::Less;
        wrapped(a).cmp(&wrapped(b)).then_with(|| boundary.compare_sites(a, b))
    }
}

struct Request {
    site: Site,
    source: VertexId,
    result: Option<(usize, usize)>,
}
struct Transport {
    projected: [Option<ProjectedCut>; 2],
    endpoint: [Option<(usize, usize)>; 2],
    repair: [Option<usize>; 2],
}

fn same_pair(a: &VisibleChord, b: &VisibleChord) -> bool {
    a.route == b.route && (a.endpoints == b.endpoints
        || (a.endpoints[0] == b.endpoints[1] && a.endpoints[1] == b.endpoints[0]))
}
fn occupied<'r>(protected: &'r [VisibleChord], site: &Site) -> Option<&'r VisibleChord> {
    protected.iter().find(|chord| chord.endpoints.contains(site))
}
fn endpoint_slot(chord: &VisibleChord, site: &Site) -> Result<usize, CollapseError> {
    chord.endpoints.iter().position(|endpoint| endpoint == site)
        .ok_or(CollapseError::ConflictingPartner)
}

/// Inclusive physical incidence: an exceptional endpoint is as important as
/// an exceptional open blocker. Wrap with equal coordinates is the FULL circle.
fn meets_packet(boundary: Boundary<'_>, chord: &VisibleChord, packet: &[Point],
    work: &mut Work) -> Result<bool, CollapseError>
{
    let a = boundary.point(&chord.endpoints[0])?;
    let b = boundary.point(&chord.endpoints[1])?;
    let lo = std::cmp::min(&a.x, &b.x);
    let hi = std::cmp::max(&a.x, &b.x);
    for point in packet {
        work.predicates += 3;
        if point.y != a.y { continue; }
        let meets = match chord.route {
            Route::Null => point.x == a.x,
            Route::Finite => &point.x >= lo && &point.x <= hi,
            Route::Wrap => a.x == b.x || &point.x <= lo || &point.x >= hi,
        };
        if meets { return Ok(true); }
    }
    Ok(false)
}

fn enqueue(requests: &mut Vec<Request>, site: Site, source: VertexId,
    protected: &[VisibleChord], work: &mut Work) -> Option<usize>
{
    if occupied(protected, &site).is_some() { return None; }
    for (index, request) in requests.iter().enumerate() {
        work.predicates += 1;
        if request.site == site { return Some(index); }
    }
    let index = requests.len();
    requests.push(Request { site, source, result: None });
    Some(index)
}

fn source_at_star(boundary: Boundary<'_>, site: &Site, protected: &[VisibleChord])
    -> Result<VertexId, CollapseError>
{
    if let Site::Vertex { vertex, .. } = site { return Ok(*vertex); }
    let point = boundary.point(site)?;
    for chord in protected {
        let LevelSource::Vertex(vertex) = &chord.level else {
            return Err(CollapseError::FrozenProductionSource);
        };
        // Source classes, not endpoint identity: a transit can be opposite a
        // remote augmented exit whose generator is nowhere near this star.
        if boundary.input().vertex(*vertex).y == point.y { return Ok(*vertex); }
    }
    Err(CollapseError::WrongSourceLevel)
}

/// First RAW blocker on <=4 immutable old arcs. No route continuation and no
/// farther contact after a wrong-sector first coordinate. The closed clips
/// supply the actual named-old-face arrival packet.
fn repair<'c, 'a>(boundary: Boundary<'a>, arcs: &[OldArc], source: &Site,
    inherited: VertexId, queries: &mut ArcQueries<'c, 'a>, work: &mut Work)
    -> Result<VisibleChord, CollapseError>
{
    let (arrival, route) = if let Some(partner) = boundary.null_contact(source)? {
        (partner, Route::Null)
    } else {
        let point = boundary.point(source)?;
        let direction = boundary.direction(source)?;
        let mut best: Option<ArcShot> = None;
        for arc in arcs {
            work.retained_visits += 1;
            let Some(shot) = queries.shoot(boundary, &arc.start, &arc.end, arc.full,
                &point, direction, work)? else { continue; };
            work.predicates += 1;
            match best.as_ref().map(|old| ray_order(&point.x, direction, &shot.x, &old.x)) {
                None | Some(Ordering::Less) => best = Some(shot),
                Some(Ordering::Equal) => {
                    for contact in shot.into_contacts() {
                        best.as_mut().unwrap().push_contact(contact);
                    }
                }
                Some(Ordering::Greater) => {}
            }
        }
        let shot = best.ok_or(CollapseError::MissingBlocker)?;
        let route = shot.route;
        let mut arrival = None;
        for contact in shot.into_contacts() {
            work.predicates += 3;
            if &contact == source || boundary.inside_null_pair(&contact)?
                || boundary.direction(&contact)? != direction.opposite() { continue; }
            if arrival.as_ref().is_some_and(|old| old != &contact) {
                return Err(CollapseError::AmbiguousArrival);
            }
            arrival = Some(contact);
        }
        (arrival.ok_or(CollapseError::MissingArrival)?, route)
    };
    boundary.validate_route(source, &arrival, boundary.direction(source)?, route)?;
    let vertex = match source {
        Site::Vertex { vertex, .. } => *vertex,
        _ => match &arrival { Site::Vertex { vertex, .. } => *vertex, _ => inherited },
    };
    if boundary.input().vertex(vertex).y != boundary.point(source)?.y {
        return Err(CollapseError::WrongSourceLevel);
    }
    Ok(VisibleChord { endpoints: [source.clone(), arrival], route,
        level: LevelSource::Vertex(vertex) })
}

pub fn collapse<'c, 'a>(old: &Submap<'a>, ribbon: &Ribbon<'a>,
    temporary: &Submap<'_, Programme<'a>>, queries: &mut ArcQueries<'c, 'a>,
    work: &mut Work) -> Result<CollapsedRegion, CollapseError>
{
    if !std::ptr::eq(old.input(), ribbon.root_input()) || old.chain() != ribbon.root_chain
        || !std::ptr::eq(temporary.input(), &ribbon.programme)
        || !std::ptr::eq(queries.catalogue().input(), old.input()) {
        return Err(CollapseError::WrongCurve);
    }
    let boundary = Boundary::new(old.input(), old.chain())?;
    let temp_boundary = Boundary::new(temporary.input(), temporary.chain())?;
    let old_ids = old.region_arcs(ribbon.region)?;
    if old_ids.is_empty() || old_ids.len() > 4 { return Err(CollapseError::TooManyOldArcs); }
    let mut arcs = Vec::with_capacity(old_ids.len());
    for &id in old_ids {
        let (start, end, full) = match old.arc_sites(id) {
            Some((a, b, full)) => (a.clone(), b.clone(), full),
            None if old_ids.len() == 1 && old.region_exits(ribbon.region)?.is_empty() => {
                let anchor = Site::Vertex { vertex: old.chain().start, side: Side::Left, slot: Slot::Single };
                (anchor.clone(), anchor, true)
            }
            None => return Err(CollapseError::WrongArc),
        };
        arcs.push(OldArc { id, start, end, full });
    }
    // The compiler packet includes remote actual old Vertex(q) blockers, not
    // merely geometrically local helper points. Add authoritative generators
    // explicitly so omission cannot silently invalidate the Original2 proof.
    let mut packet = ribbon.exceptional.clone();
    for protected in &ribbon.protected {
        let LevelSource::Vertex(vertex) = &protected.level else {
            return Err(CollapseError::FrozenProductionSource);
        };
        let point = old.input().vertex(*vertex);
        if !packet.contains(point) { packet.push(point.clone()); }
    }

    let ids: Vec<_> = temporary.chord_ids().collect();
    let extent = ids.last().map_or(0, |id| id.0 + 1);
    let mut transport: Vec<Option<Transport>> = (0..extent).map(|_| None).collect();
    let mut chords = Vec::with_capacity(ids.len());
    let mut requests = Vec::new();
    for &id in &ids {
        work.retained_visits += 1;
        let (sites, route) = temporary.chord(id)?;
        let LevelSource::Vertex(vertex) = temporary.chord_level(id)? else {
            return Err(CollapseError::FrozenProductionSource);
        };
        let source = ribbon.root_source(*vertex)?;
        let projected = [ribbon.project_cut(sites[0], work)?, ribbon.project_cut(sites[1], work)?];
        for cut in projected.iter().flatten() {
            if !arcs.iter().any(|arc| arc.id == cut.arc) { return Err(CollapseError::WrongArc); }
            if boundary.point(&cut.site)?.y != old.input().vertex(source).y {
                return Err(CollapseError::WrongSourceLevel);
            }
        }
        let mut record = Transport { projected, endpoint: [None; 2], repair: [None; 2] };
        if let [Some(a), Some(b)] = &record.projected {
            let candidate = VisibleChord { endpoints: [a.site.clone(), b.site.clone()], route,
                level: LevelSource::Vertex(source) };
            if ribbon.protected.iter().any(|exit| same_pair(exit, &candidate)) {
                transport[id.0] = Some(record);
                continue;
            }
            let exceptional = meets_packet(boundary, &candidate, &packet, work)?;
            let direction = boundary.direction(&candidate.endpoints[0])?;
            let legal_incidence = candidate.endpoints[0] != candidate.endpoints[1]
                && boundary.validate_route(&candidate.endpoints[0], &candidate.endpoints[1], direction, route).is_ok()
                && (route == Route::Null || (boundary.direction(&candidate.endpoints[1])? == direction.opposite()
                    && !boundary.inside_null_pair(&candidate.endpoints[0])?
                    && !boundary.inside_null_pair(&candidate.endpoints[1])?
                    && temp_boundary.direction(sites[0])? == direction));
            if !exceptional {
                if !legal_incidence || candidate.endpoints.iter().any(|site| occupied(&ribbon.protected, site).is_some()) {
                    return Err(CollapseError::UncertifiedLimit);
                }
                let index = chords.len();
                chords.push(candidate);
                record.endpoint = [Some((index, 0)), Some((index, 1))];
                transport[id.0] = Some(record);
                continue;
            }
        }
        // Neither locality nor the discarded chord's direction is used here:
        // independently conserve EVERY selected original endpoint, remote too.
        for slot in 0..2 {
            if let Some(cut) = &record.projected[slot] {
                record.repair[slot] = enqueue(&mut requests, cut.site.clone(), source,
                    &ribbon.protected, work);
            }
        }
        transport[id.0] = Some(record);
    }
    for flag in &ribbon.star_flags {
        let source = source_at_star(boundary, flag, &ribbon.protected)?;
        enqueue(&mut requests, flag.clone(), source, &ribbon.protected, work);
    }
    let ordinary_count = chords.len();
    for index in 0..requests.len() {
        let request = &requests[index];
        let candidate = repair(boundary, &arcs, &request.site, request.source, queries, work)?;
        let mut authoritative = false;
        for endpoint in &candidate.endpoints {
            if let Some(exit) = occupied(&ribbon.protected, endpoint) {
                if !same_pair(exit, &candidate) { return Err(CollapseError::ConflictingPartner); }
                authoritative = true;
            }
        }
        if authoritative { continue; }
        // Only the bounded repair packet is searched, never all ordinary rows.
        let mut duplicate = None;
        for (row, prior) in chords.iter().enumerate().skip(ordinary_count) {
            work.retained_visits += 1;
            if same_pair(prior, &candidate) { duplicate = Some(row); break; }
            if prior.endpoints.iter().any(|site| candidate.endpoints.contains(site)) {
                return Err(CollapseError::ConflictingPartner);
            }
        }
        let row = duplicate.unwrap_or_else(|| { let row = chords.len(); chords.push(candidate); row });
        requests[index].result = Some((row, endpoint_slot(&chords[row], &requests[index].site)?));
    }
    for record in transport.iter_mut().flatten() {
        for slot in 0..2 {
            if let Some(request) = record.repair[slot] { record.endpoint[slot] = requests[request].result; }
        }
    }

    let mut cuts: Vec<_> = arcs.iter().map(|arc| ArcCuts { arc: arc.id, endpoints: Vec::new() }).collect();
    // Retained endpoint identity comes directly from sparse topology. Each
    // canonical arc contributes its START once; Right/helper starts are ignored.
    for &arc in temporary.canonical_arcs() {
        let Some([(id, slot), _]) = temporary.arc_endpoints(arc) else { continue; };
        let record = transport.get(id.0).and_then(Option::as_ref).ok_or(CollapseError::WrongArc)?;
        let (Some(cut), Some(endpoint)) = (&record.projected[slot], record.endpoint[slot]) else { continue; };
        let index = arcs.iter().position(|arc| arc.id == cut.arc).ok_or(CollapseError::WrongArc)?;
        if !arcs[index].contains(boundary, &cut.site)? { return Err(CollapseError::WrongArc); }
        cuts[index].endpoints.push(endpoint);
    }
    for (index, stream) in cuts.iter_mut().enumerate() {
        let arc = &arcs[index];
        let mut descent = None;
        for offset in 1..stream.endpoints.len() {
            let a = stream.endpoints[offset - 1]; let b = stream.endpoints[offset];
            work.predicates += 1;
            if arc.compare(boundary, &chords[a.0].endpoints[a.1], &chords[b.0].endpoints[b.1]) == Ordering::Greater {
                if descent.replace(offset).is_some() { return Err(CollapseError::NonMonotoneQuotient); }
            }
        }
        if let Some(offset) = descent { stream.endpoints.rotate_left(offset); }
    }
    // Repair partners and direct stars need not occur in the temporary tour.
    // Merge only this constant packet into each already ordered old-arc stream.
    let mut additions: Vec<Vec<(usize, usize)>> = arcs.iter().map(|_| Vec::new()).collect();
    for row in ordinary_count..chords.len() {
        for slot in 0..2 {
            let site = &chords[row].endpoints[slot];
            let mut owner = None;
            for (index, arc) in arcs.iter().enumerate() {
                if arc.contains(boundary, site)? {
                    if owner.replace(index).is_some() { return Err(CollapseError::WrongArc); }
                }
            }
            let index = owner.ok_or(CollapseError::WrongArc)?;
            additions[index].push((row, slot));
        }
    }
    for (index, extra) in additions.iter_mut().enumerate() {
        let arc = &arcs[index];
        extra.sort_unstable_by(|a, b| {
            work.predicates += 1;
            arc.compare(boundary, &chords[a.0].endpoints[a.1], &chords[b.0].endpoints[b.1])
        });
        let transported = std::mem::take(&mut cuts[index].endpoints);
        let mut merged: Vec<(usize, usize)> = Vec::with_capacity(transported.len() + extra.len());
        let mut i = 0; let mut j = 0;
        while i < transported.len() || j < extra.len() {
            let take_old = if i == transported.len() { false }
                else if j == extra.len() { true }
                else {
                    work.predicates += 1;
                    let a = transported[i]; let b = extra[j];
                    arc.compare(boundary, &chords[a.0].endpoints[a.1], &chords[b.0].endpoints[b.1]) != Ordering::Greater
                };
            let endpoint = if take_old { let item = transported[i]; i += 1; item }
                else { let item = extra[j]; j += 1; item };
            if let Some(&(row, slot)) = merged.last() {
                work.predicates += 1;
                let order = arc.compare(boundary, &chords[row].endpoints[slot], &chords[endpoint.0].endpoints[endpoint.1]);
                if order == Ordering::Greater { return Err(CollapseError::NonMonotoneQuotient); }
                if order == Ordering::Equal && !same_pair(&chords[row], &chords[endpoint.0]) {
                    return Err(CollapseError::ConflictingPartner);
                }
                // A transported repair and its explicit addition name the same
                // record endpoint. Distinct duplicate-pair rows retain coverage.
                if endpoint == (row, slot) { continue; }
            }
            merged.push(endpoint);
        }
        cuts[index].endpoints = merged;
    }
    Ok(CollapsedRegion { chords, cuts })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boundary::Chain;
    use crate::curve::Curve;
    use crate::geometry::{Point, Rational};
    use crate::hierarchy::Catalogue;
    use crate::input::{EdgeId, Input, VertexSource};
    use crate::merge::OriginalMerge;
    use crate::submap::RegionId;

    fn whole(input: &Input) -> Boundary<'_> {
        Boundary::new(input, Chain::new(input, VertexId(0), VertexId(input.len() - 1)).unwrap()).unwrap()
    }

    fn root_vertex(input: &Input, original: usize) -> VertexId {
        (0..input.len()).map(VertexId)
            .find(|vertex| input.source(*vertex) == &VertexSource::Original(original)).unwrap()
    }

    fn original_contact(input: &Input, original: usize, level: &Rational, side: Side) -> Site {
        (0..input.edge_count()).map(EdgeId).find_map(|edge| {
            if input.edge_source(edge).original != original { return None; }
            let (t, _) = input.horizontal_hit(edge, level)?;
            let zero = Rational::from_integer(0.into());
            let one = Rational::from_integer(1.into());
            (t > zero && t < one).then_some(Site::Edge { edge, t, side })
        }).unwrap()
    }

    #[test]
    fn compiled_empty_temporary_preserves_every_cap_flag_and_full_return() {
        let input = Input::open(&[Point::integer(0, -2), Point::integer(0, 3)]).unwrap();
        let boundary = whole(&input);
        let mut work = Work::default();
        let old = Submap::from_verified_chords(&boundary, Vec::new(), &mut work).unwrap();
        let ribbon = Ribbon::compile(&old, RegionId(0), &mut work).unwrap();
        let local = Boundary::new(&ribbon.programme,
            Chain::new(&ribbon.programme, VertexId(0), VertexId(ribbon.programme.len() - 1)).unwrap()).unwrap();
        let temporary = Submap::from_verified_chords(&local, Vec::new(), &mut work).unwrap();
        let catalogue = Catalogue::build(&input, 1, &mut OriginalMerge, &mut work).unwrap();
        let mut queries = ArcQueries::new(&catalogue, 1);
        let collapsed = collapse(&old, &ribbon, &temporary, &mut queries, &mut work).unwrap();
        assert_eq!(collapsed.chords.len(), 2);
        for flag in &ribbon.star_flags {
            assert!(collapsed.chords.iter().any(|chord| chord.endpoints.contains(flag)));
        }
        assert!(collapsed.chords.iter().all(|chord| chord.route == Route::Wrap));
        assert_eq!(collapsed.cuts.len(), 1);
        assert_eq!(collapsed.cuts[0].endpoints.len(), 4);
        for pair in collapsed.cuts[0].endpoints.windows(2) {
            let a = pair[0]; let b = pair[1];
            assert_ne!(boundary.compare_sites(&collapsed.chords[a.0].endpoints[a.1],
                &collapsed.chords[b.0].endpoints[b.1]), Ordering::Greater);
        }
    }

    #[test]
    fn actual_compiled_helper_contact_preserves_its_remote_original_cut() {
        let input = Input::open(&[
            Point::integer(0, -2), Point::integer(0, 2),
            Point::integer(4, 3), Point::integer(4, -3),
        ]).unwrap();
        let boundary = whole(&input);
        let mut work = Work::default();
        let old = Submap::from_verified_chords(&boundary, Vec::new(), &mut work).unwrap();
        let ribbon = Ribbon::compile(&old, RegionId(0), &mut work).unwrap();
        let local = Boundary::new(&ribbon.programme,
            Chain::new(&ribbon.programme, VertexId(0), VertexId(ribbon.programme.len() - 1)).unwrap()).unwrap();
        let anchor = Site::Vertex { vertex: VertexId(0), side: Side::Left, slot: Slot::Single };
        let full = local.arc(&anchor, &anchor, true).unwrap();
        let mut found = None;
        // Test-only direct geometry computes a REAL temporary visible record;
        // it is not a query callback that echoes an expected repaired chord.
        for source in local.occurrences() {
            if ribbon.project_cut(&source, &mut work).unwrap().is_some()
                || local.inside_null_pair(&source).unwrap() { continue; }
            let direction = local.direction(&source).unwrap();
            let Some(contacts) = local.nearest_contacts(&full, &source, direction).unwrap() else { continue; };
            let route = contacts.route;
            for contact in contacts {
                if local.inside_null_pair(&contact.site).unwrap()
                    || local.direction(&contact.site).unwrap() != direction.opposite() { continue; }
                let Some(projected) = ribbon.project_cut(&contact.site, &mut work).unwrap() else { continue; };
                if !matches!(projected.site, Site::Edge { .. }) { continue; }
                let Site::Vertex { vertex, .. } = &source else { unreachable!() };
                found = Some((VisibleChord { endpoints: [source.clone(), contact.site], route,
                    level: LevelSource::Vertex(*vertex) }, projected.site));
                break;
            }
            if found.is_some() { break; }
        }
        let (record, remote) = found.expect("compiled cap has a remote selected original contact");
        let temporary = Submap::from_verified_chords(&local, vec![record], &mut work).unwrap();
        let catalogue = Catalogue::build(&input, 1, &mut OriginalMerge, &mut work).unwrap();
        let mut queries = ArcQueries::new(&catalogue, 1);
        let collapsed = collapse(&old, &ribbon, &temporary, &mut queries, &mut work).unwrap();
        assert!(collapsed.chords.iter().any(|chord| chord.endpoints.contains(&remote)));
        assert!(collapsed.chords.iter().all(|chord| matches!(chord.level, LevelSource::Vertex(_))));
        let published = crate::graft::graft(&old, vec![collapsed], &mut work).unwrap();
        assert!(published.chord_ids().any(|id| published.chord(id).unwrap().0.contains(&&remote)));
    }

    #[test]
    fn actual_original2_record_rebases_source_without_endpoint_queries() {
        let input = Input::open(&[
            Point::integer(0, -2), Point::integer(0, 2),
            Point::integer(4, 3), Point::integer(4, -3),
        ]).unwrap();
        let boundary = whole(&input);
        let mut work = Work::default();
        let old = Submap::from_verified_chords(&boundary, Vec::new(), &mut work).unwrap();
        let ribbon = Ribbon::compile(&old, RegionId(0), &mut work).unwrap();
        let local = Boundary::new(&ribbon.programme,
            Chain::new(&ribbon.programme, VertexId(0), VertexId(ribbon.programme.len() - 1)).unwrap()).unwrap();
        let anchor = Site::Vertex { vertex: VertexId(0), side: Side::Left, slot: Slot::Single };
        let full = local.arc(&anchor, &anchor, true).unwrap();
        let mut found = None;
        for source in local.occurrences() {
            let Some(a) = ribbon.project_cut(&source, &mut work).unwrap() else { continue; };
            if local.inside_null_pair(&source).unwrap() { continue; }
            let direction = local.direction(&source).unwrap();
            let Some(contacts) = local.nearest_contacts(&full, &source, direction).unwrap() else { continue; };
            let route = contacts.route;
            for contact in contacts {
                if local.inside_null_pair(&contact.site).unwrap()
                    || local.direction(&contact.site).unwrap() != direction.opposite() { continue; }
                let Some(b) = ribbon.project_cut(&contact.site, &mut work).unwrap() else { continue; };
                let Site::Vertex { vertex, .. } = &source else { unreachable!() };
                let root_source = ribbon.root_source(*vertex).unwrap();
                let candidate = VisibleChord { endpoints: [a.site.clone(), b.site], route,
                    level: LevelSource::Vertex(root_source) };
                if meets_packet(boundary, &candidate, &ribbon.exceptional, &mut work).unwrap() { continue; }
                if boundary.validate_route(&candidate.endpoints[0], &candidate.endpoints[1],
                    boundary.direction(&candidate.endpoints[0]).unwrap(), route).is_err() { continue; }
                found = Some((VisibleChord { endpoints: [source.clone(), contact.site], route,
                    level: LevelSource::Vertex(*vertex) }, candidate));
                break;
            }
            if found.is_some() { break; }
        }
        let (record, expected) = found.expect("compiled ribbon has an ordinary Original2 record");
        let temporary = Submap::from_verified_chords(&local, vec![record], &mut work).unwrap();
        let empty = Submap::from_verified_chords(&local, Vec::new(), &mut work).unwrap();
        let catalogue = Catalogue::build(&input, 1, &mut OriginalMerge, &mut work).unwrap();
        let mut queries = ArcQueries::new(&catalogue, 1);
        let mut baseline = Work::default();
        collapse(&old, &ribbon, &empty, &mut queries, &mut baseline).unwrap();
        let mut actual = Work::default();
        let collapsed = collapse(&old, &ribbon, &temporary, &mut queries, &mut actual).unwrap();
        assert!(collapsed.chords.iter().any(|chord| same_pair(chord, &expected)
            && chord.level == expected.level));
        assert_eq!(actual.oracle_calls, baseline.oracle_calls);
        assert_eq!(actual.arc_edge_visits, baseline.arc_edge_visits);
    }

    #[test]
    fn compiled_augmented_exit_keeps_opposite_side_transit_cuts() {
        let input = Input::open(&[
            Point::integer(-5, 4), Point::integer(-5, -5),
            Point::integer(-1, -1), Point::integer(0, 0), Point::integer(1, -2),
            Point::integer(5, -4), Point::integer(5, 2),
            Point::integer(10, 3), Point::integer(10, -3),
            Point::integer(12, -6), Point::integer(12, 5),
        ]).unwrap();
        let boundary = whole(&input);
        let generator = root_vertex(&input, 3);
        let level = &input.vertex(generator).y;
        let a = original_contact(&input, 7, level, Side::Left);
        let b = original_contact(&input, 9, level, Side::Left);
        let transit_a = match &a { Site::Edge { edge, t, .. } =>
            Site::Edge { edge: *edge, t: t.clone(), side: Side::Right }, _ => unreachable!() };
        let transit_b = match &b { Site::Edge { edge, t, .. } =>
            Site::Edge { edge: *edge, t: t.clone(), side: Side::Right }, _ => unreachable!() };
        let mut work = Work::default();
        let old = Submap::from_verified_chords(&boundary, vec![VisibleChord {
            endpoints: [a, b], route: Route::Finite, level: LevelSource::Vertex(generator),
        }], &mut work).unwrap();
        let catalogue = Catalogue::build(&input, 1, &mut OriginalMerge, &mut work).unwrap();
        let mut queries = ArcQueries::new(&catalogue, 1);
        let mut conserved = [false; 2];
        for region in old.region_ids() {
            let ribbon = Ribbon::compile(&old, region, &mut work).unwrap();
            assert!(ribbon.exceptional.contains(input.vertex(generator)),
                "equal-base source packet must contain the untouched remote generator");
            let local = Boundary::new(&ribbon.programme,
                Chain::new(&ribbon.programme, VertexId(0), VertexId(ribbon.programme.len() - 1)).unwrap()).unwrap();
            let temporary = Submap::from_verified_chords(&local, Vec::new(), &mut work).unwrap();
            let collapsed = collapse(&old, &ribbon, &temporary, &mut queries, &mut work).unwrap();
            for flag in &ribbon.star_flags {
                assert!(occupied(&ribbon.protected, flag).is_some()
                    || collapsed.chords.iter().any(|chord| chord.endpoints.contains(flag)));
            }
            for (index, transit) in [&transit_a, &transit_b].into_iter().enumerate() {
                conserved[index] |= collapsed.chords.iter().any(|chord| chord.endpoints.contains(transit));
            }
        }
        assert_eq!(conserved, [true, true]);
    }

    #[test]
    fn remote_equal_base_vertex_is_an_exceptional_open_blocker() {
        let input = Input::open(&[
            Point::integer(-5, 4), Point::integer(-5, -5),
            Point::integer(-1, -1), Point::integer(0, 0), Point::integer(1, -2),
            Point::integer(5, -4), Point::integer(5, 2),
            Point::integer(10, 3), Point::integer(10, -3),
            Point::integer(12, -6), Point::integer(12, 5),
        ]).unwrap();
        let boundary = whole(&input);
        let generator = root_vertex(&input, 3);
        let level = &input.vertex(generator).y;
        let chord = VisibleChord {
            endpoints: [original_contact(&input, 0, level, Side::Right),
                original_contact(&input, 5, level, Side::Left)],
            route: Route::Finite, level: LevelSource::Vertex(generator),
        };
        assert!(meets_packet(boundary, &chord, &[input.vertex(generator).clone()],
            &mut Work::default()).unwrap());
        // The remote old-exit endpoints alone do NOT certify this failure.
        let old_exit_points = [Point::new(Rational::from_integer(10.into()), level.clone()),
            Point::new(Rational::from_integer(12.into()), level.clone())];
        assert!(!meets_packet(boundary, &chord, &old_exit_points, &mut Work::default()).unwrap());
    }
}
