//! Ordered fusion tours from Chazelle §3.1. Input maps remain immutable.
//! Arrival sectors are resolved only after the first geometric blocker is known.
use crate::arcs::{ArcQueries, ArcQueryError, ArcShot};
use crate::boundary::{Boundary, BoundaryError, Side, Site, Slot};
use crate::cap::{CapError, Join, Scope};
use crate::curve::{Curve, LevelSource};
use crate::geometry::{ray_order, Direction, Point, Route};
use crate::input::Input;
use crate::scalar::ExactScalar;
use crate::submap::{ArcId, ChordId, MapError, RegionId, Submap, VisibleChord};
use crate::work::Work;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;

/// Actual arc services used by the same fusion algorithm on original and local
/// curves. A service must return the first raw coordinate, not the first
/// admissible arrival, and must use saved chains or bounded direct pieces.
pub trait FusionQueries<'a, C: Curve> {
    type Error: fmt::Debug;
    fn shoot(&mut self, boundary: Boundary<'a, C>, start: &Site<C::Scalar>,
        end: &Site<C::Scalar>, full: bool, source: &Point<C::Scalar>,
        direction: Direction, work: &mut Work)
        -> Result<Option<ArcShot<C::Scalar>>, Self::Error>;
}
impl<'c, 'a> FusionQueries<'a, Input> for ArcQueries<'c, 'a> {
    type Error = ArcQueryError;
    fn shoot(&mut self, boundary: Boundary<'a>, start: &Site, end: &Site,
        full: bool, source: &Point, direction: Direction, work: &mut Work)
        -> Result<Option<ArcShot>, Self::Error>
    { ArcQueries::shoot(self, boundary, start, end, full, source, direction, work) }
}

#[derive(Debug)]
pub enum FusionError<E: fmt::Debug> {
    Query(E), Boundary(BoundaryError), Map(MapError), InvalidJoin,
    InvalidCapRegion, InvalidTurn, MissingArrival, AmbiguousArrival,
    InvalidExit, ConflictingPartner,
}
impl<E: fmt::Debug> From<BoundaryError> for FusionError<E> {
    fn from(error: BoundaryError) -> Self { Self::Boundary(error) }
}
impl<E: fmt::Debug> From<MapError> for FusionError<E> {
    fn from(error: MapError) -> Self { Self::Map(error) }
}
impl<E: fmt::Debug> From<CapError> for FusionError<E> {
    fn from(error: CapError) -> Self {
        match error {
            CapError::Boundary(e) => Self::Boundary(e), CapError::Map(e) => Self::Map(e),
            CapError::InvalidJoin => Self::InvalidJoin,
            CapError::InvalidTurn => Self::InvalidTurn,
            CapError::InvalidCapRegion => Self::InvalidCapRegion,
        }
    }
}
impl<E: fmt::Debug> fmt::Display for FusionError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl<E: fmt::Debug> std::error::Error for FusionError<E> {}

struct Event<'m, S> { site: &'m Site<S>, chord: Option<(ChordId, usize)>, after: ArcId }
/// Canonical endpoint rotation plus the two common-vertex flags. No endpoint
/// vector or coordinate table is copied; the two virtual flags are constant-size.
struct Tour<'m, 'a, C: Curve> {
    map: &'m Submap<'a, C>, boundary: Boundary<'a, C>,
    first: Site<C::Scalar>, last: Site<C::Scalar>,
    first_meta: Option<(ChordId, usize)>, last_meta: Option<(ChordId, usize)>,
    first_after: ArcId, last_after: ArcId, offset: usize, interior: usize,
}
impl<'m, 'a, C: Curve> Tour<'m, 'a, C> {
    fn new(map: &'m Submap<'a, C>, join: Join<'a, C>, scope: Scope, work: &mut Work)
        -> Result<Self, MapError>
    {
        let boundary = join.scope(scope);
        let first_side = if scope == Scope::First { Side::Right } else { Side::Left };
        let first = Site::Vertex { vertex: join.common(), side: first_side, slot: Slot::Single };
        let last = Site::Vertex { vertex: join.common(), side: if first_side == Side::Left { Side::Right } else { Side::Left }, slot: Slot::Single };
        let incident = map.end_incident_arcs(join.common())?;
        let mut first_meta = None; let mut last_meta = None;
        let mut offset = None; let mut count = 0;
        for (i, &arc) in map.canonical_arcs().iter().enumerate() {
            work.retained_visits += 1;
            let Some((site, _, _)) = map.arc_sites(arc) else { continue };
            let endpoint = map.arc_endpoints(arc).unwrap()[0];
            work.predicates += 1;
            if offset.is_none() && boundary.compare_sites(site, &first) != Ordering::Less { offset = Some(i); }
            if site == &first { first_meta = Some(endpoint); }
            else if site == &last { last_meta = Some(endpoint); }
            else { count += 1; }
        }
        let mut offset = offset.unwrap_or(0);
        if first_meta.is_some() { offset = (offset + 1) % map.canonical_arcs().len(); }
        let index = if first_side == Side::Left { 0 } else { 1 };
        Ok(Self { map, boundary, first, last, first_meta, last_meta,
            first_after: incident[index][1], last_after: incident[1-index][1], offset, interior: count })
    }
    fn last_index(&self) -> usize { self.interior + 1 }
    fn event(&self, index: usize) -> Event<'_, C::Scalar> {
        if index == 0 { return Event { site: &self.first, chord: self.first_meta, after: self.first_after }; }
        if index == self.last_index() { return Event { site: &self.last, chord: self.last_meta, after: self.last_after }; }
        let canonical = self.map.canonical_arcs();
        let arc = canonical[(self.offset + index - 1) % canonical.len()];
        Event { site: self.map.arc_sites(arc).unwrap().0, chord: Some(self.map.arc_endpoints(arc).unwrap()[0]), after: arc }
    }
    fn compare(&self, a: &Site<C::Scalar>, b: &Site<C::Scalar>, work: &mut Work) -> Ordering {
        work.predicates += 3;
        let a_late = self.boundary.compare_sites(a, &self.first) == Ordering::Less;
        let b_late = self.boundary.compare_sites(b, &self.first) == Ordering::Less;
        a_late.cmp(&b_late).then_with(|| self.boundary.compare_sites(a, b))
    }
}

fn raw_region<'a, C: Curve, Q: FusionQueries<'a, C>>(queries: &mut Q,
    map: &Submap<'a, C>, region: RegionId, point: &Point<C::Scalar>,
    direction: Direction, work: &mut Work)
    -> Result<Option<ArcShot<C::Scalar>>, FusionError<Q::Error>>
{
    let boundary = Boundary::new(map.input(), map.chain())?;
    let anchor = Site::Vertex { vertex: map.chain().start, side: Side::Left, slot: Slot::Single };
    let mut best: Option<ArcShot<C::Scalar>> = None;
    for &arc in map.region_arcs(region)? {
        work.retained_visits += 1;
        let (start, end, full) = map.arc_sites(arc).unwrap_or((&anchor, &anchor, true));
        let Some(hit) = queries.shoot(boundary, start, end, full, point, direction, work).map_err(FusionError::Query)? else { continue };
        work.predicates += 1;
        let order = best.as_ref().map_or(Ordering::Less, |old| ray_order(&point.x, direction, &hit.x, &old.x));
        if order == Ordering::Less { best = Some(hit); }
        else if order == Ordering::Equal {
            let old = best.as_mut().unwrap();
            for site in hit.into_contacts() { old.push_contact(site); }
        }
    }
    Ok(best)
}

/// Select a sector at the already settled first coordinate. Failure is not
/// permission to continue the ray through this geometric blocker.
fn arrival<'a, C: Curve, E: fmt::Debug>(join: Join<'a, C>, scope: Scope,
    shot: &ArcShot<C::Scalar>, direction: Direction, work: &mut Work)
    -> Result<Option<Site<C::Scalar>>, FusionError<E>>
{
    let union = join.boundary(); let mut result = None;
    for raw in shot.contacts() {
        let site = join.contact_site(scope, raw.clone())?;
        work.predicates += 2;
        if union.direction(&site)? != direction.opposite() || union.inside_null_pair(&site)? { continue; }
        if let Some(old) = &result { if old != &site { return Err(FusionError::AmbiguousArrival); } }
        else { result = Some(site); }
    }
    Ok(result)
}
fn old_arrival<C: Curve, E: fmt::Debug>(boundary: Boundary<'_, C>,
    shot: &ArcShot<C::Scalar>, direction: Direction, work: &mut Work)
    -> Result<Option<Site<C::Scalar>>, FusionError<E>>
{
    let mut result = None;
    for site in shot.contacts() {
        work.predicates += 2;
        if boundary.direction(site)? != direction.opposite() || boundary.inside_null_pair(site)? { continue; }
        if let Some(old) = &result { if old != site { return Err(FusionError::AmbiguousArrival); } }
        else { result = Some(site.clone()); }
    }
    Ok(result)
}

/// Formal contacts retain a support and source level, not an intersection
/// expression whose depth grows with the number of merges.
fn source_point<'a, C: Curve, E: fmt::Debug>(boundary: Boundary<'a, C>,
    site: &Site<C::Scalar>, level: &LevelSource<C::Scalar>, work: &mut Work)
    -> Result<Cow<'a, Point<C::Scalar>>, FusionError<E>>
{
    if C::Scalar::REBASE_SOURCE_CONTACTS {
        if let Site::Edge { edge, .. } = site {
            let y = boundary.input().level(level);
            work.predicates += 1;
            let (_, x) = boundary.input().horizontal_hit(*edge, &y).ok_or(FusionError::MissingArrival)?;
            return Ok(Cow::Owned(Point::new(x, y.into_owned())));
        }
    }
    Ok(boundary.point(site)?)
}

fn record<C: Curve, E: fmt::Debug>(boundary: Boundary<'_, C>, mut a: Site<C::Scalar>,
    mut b: Site<C::Scalar>, route: Route, mut level: LevelSource<C::Scalar>,
    records: &mut Vec<VisibleChord<C::Scalar>>, work: &mut Work)
    -> Result<(), FusionError<E>>
{
    if a == b { return Err(FusionError::ConflictingPartner); }
    // Any newly intrinsic endpoint fixes the shared source class, including a
    // formerly augmented endpoint that normalized onto an original vertex.
    if let Site::Vertex { vertex, .. } = &a { level = LevelSource::Vertex(*vertex); }
    else if let Site::Vertex { vertex, .. } = &b { level = LevelSource::Vertex(*vertex); }
    if C::Scalar::REBASE_SOURCE_CONTACTS {
        let value = boundary.input().level(&level);
        for site in [&mut a, &mut b] {
            if let Site::Edge { edge, side, .. } = site {
                work.predicates += 1;
                let (t, _) = boundary.input().horizontal_hit(*edge, &value).ok_or(FusionError::MissingArrival)?;
                *site = boundary.normalize_site(&Site::Edge { edge: *edge, t, side: *side })?;
            }
        }
        if a == b { return Err(FusionError::ConflictingPartner); }
    }
    let direction = boundary.direction(&a)?;
    boundary.validate_route(&a, &b, direction, route)?;
    work.predicates += 1;
    if boundary.compare_sites(&a, &b) == Ordering::Greater { std::mem::swap(&mut a, &mut b); }
    records.push(VisibleChord { endpoints: [a, b], route, level });
    Ok(())
}
struct Partner<S> { site: Site<S>, route: Route, level: LevelSource<S> }
fn old_partner<'a, C: Curve, Q: FusionQueries<'a, C>>(queries: &mut Q,
    tour: &Tour<'_, 'a, C>, join: Join<'a, C>, scope: Scope, index: usize,
    work: &mut Work) -> Result<Partner<C::Scalar>, FusionError<Q::Error>>
{
    let event = tour.event(index);
    let actual = join.source_site(scope, event.site.clone())?;
    if let Some(null) = join.boundary().null_contact(&actual)? {
        let Site::Vertex { vertex, .. } = actual else { unreachable!() };
        return Ok(Partner { site: null, route: Route::Null, level: LevelSource::Vertex(vertex) });
    }
    if let Some((id, slot)) = event.chord {
        let (ends, route) = tour.map.chord(id)?;
        return Ok(Partner { site: join.contact_site(scope, ends[1-slot].clone())?, route,
            level: tour.map.chord_level(id)?.clone() });
    }
    let point = tour.boundary.point(event.site)?;
    let direction = tour.boundary.direction(event.site)?;
    let region = tour.map.arc_region(event.after)?;
    let shot = raw_region(queries, tour.map, region, &point, direction, work)?.ok_or(FusionError::MissingArrival)?;
    let site = old_arrival(tour.boundary, &shot, direction, work)?.ok_or(FusionError::MissingArrival)?;
    let Site::Vertex { vertex, .. } = event.site else { unreachable!() };
    Ok(Partner { site: join.contact_site(scope, site)?, route: shot.route, level: LevelSource::Vertex(*vertex) })
}
fn settle<'a, C: Curve, Q: FusionQueries<'a, C>>(queries: &mut Q,
    tour: &Tour<'_, 'a, C>, join: Join<'a, C>, scope: Scope, index: usize,
    records: &mut Vec<VisibleChord<C::Scalar>>, work: &mut Work)
    -> Result<(), FusionError<Q::Error>>
{
    let partner = old_partner(queries, tour, join, scope, index, work)?;
    record(join.boundary(), join.source_site(scope, tour.event(index).site.clone())?,
        partner.site, partner.route, partner.level, records, work)
}

/// Shared level classes can put an endpoint event on an old exit. The
/// clockwise germ, not the incoming ray, chooses the next region in that case.
fn outgoing_region<C: Curve, E: fmt::Debug>(source: Boundary<'_, C>, target: &Submap<'_, C>,
    p: &Site<C::Scalar>, level: &LevelSource<C::Scalar>, region: RegionId,
    work: &mut Work) -> Result<RegionId, FusionError<E>>
{
    let boundary = Boundary::new(target.input(), target.chain())?;
    let point = source_point(source, p, level, work)?;
    let above = source.direction(p)? == Direction::Left;
    for &exit in target.region_exits(region)? {
        let (ends, route) = target.chord(exit)?;
        if route == Route::Null { continue; }
        let a = source_point(boundary, ends[0], target.chord_level(exit)?, work)?;
        work.predicates += 1;
        if a.y != point.y { continue; }
        let b = source_point(boundary, ends[1], target.chord_level(exit)?, work)?;
        let direction = boundary.direction(ends[0])?;
        work.predicates += 2;
        if route == Route::Finite && crate::geometry::contact_route(&a.x, &point.x, direction) != Route::Finite { continue; }
        if ray_order(&a.x, direction, &point.x, &b.x) == Ordering::Greater { continue; }
        let side = if above == (direction == Direction::Right) { 1 } else { 0 };
        return Ok(target.chord_regions(exit)?[side]);
    }
    Ok(region)
}

fn pass<'a, C: Curve, Q: FusionQueries<'a, C>>(queries: &mut Q,
    maps: [&Submap<'a, C>; 2], join: Join<'a, C>, scope: Scope,
    records: &mut Vec<VisibleChord<C::Scalar>>, work: &mut Work)
    -> Result<(), FusionError<Q::Error>>
{
    let source = maps[scope.index()]; let target = maps[scope.opposite().index()];
    let tour = Tour::new(source, join, scope, work)?;
    let target_boundary = join.scope(scope.opposite());
    let mut region = join.germ_region(scope, target)?;
    let mut p = tour.first.clone(); let mut settled = 1; let mut k = 1;
    let actual_first = join.first_source(scope)?;
    if let Some(null) = join.boundary().null_contact(&actual_first)? {
        record(join.boundary(), actual_first, null, Route::Null,
            LevelSource::Vertex(join.common()), records, work)?;
    } else {
        let point = tour.boundary.point(&tour.first)?;
        let direction = tour.boundary.direction(&tour.first)?;
        let own = raw_region(queries, source, source.arc_region(tour.first_after)?, &point, direction, work)?.ok_or(FusionError::MissingArrival)?;
        let other = raw_region(queries, target, region, &point, direction, work)?.ok_or(FusionError::MissingArrival)?;
        work.predicates += 1;
        if ray_order(&point.x, direction, &other.x, &own.x) != Ordering::Greater {
            let contact = arrival(join, scope.opposite(), &other, direction, work)?.ok_or(FusionError::MissingArrival)?;
            record(join.boundary(), actual_first, contact, other.route,
                LevelSource::Vertex(join.common()), records, work)?;
        } else {
            let contact = old_arrival(tour.boundary, &own, direction, work)?.ok_or(FusionError::MissingArrival)?;
            record(join.boundary(), actual_first, join.contact_site(scope, contact.clone())?, own.route,
                LevelSource::Vertex(join.common()), records, work)?;
            p = contact;
            while k <= tour.last_index() && tour.compare(tour.event(k).site, &p, work) != Ordering::Greater {
                settle(queries, &tour, join, scope, k, records, work)?;
                k += 1;
            }
            settled = k;
            region = outgoing_region(tour.boundary, target, &p, &LevelSource::Vertex(join.common()), region, work)?;
        }
    }
    while k <= tour.last_index() {
        let mut advanced = false;
        for j in k..=tour.last_index() {
            work.fusion_events += 1;
            let event = tour.event(j);
            let actual = join.source_site(scope, event.site.clone())?;
            let direction = join.boundary().direction(&actual)?;
            let old = old_partner(queries, &tour, join, scope, j, work)?;
            let point = source_point(tour.boundary, event.site, &old.level, work)?;
            if old.route != Route::Null {
                if let Some(hit) = raw_region(queries, target, region, &point, direction, work)? {
                    if let Some(contact) = arrival(join, scope.opposite(), &hit, direction, work)? {
                        let old_point = source_point(join.boundary(), &old.site, &old.level, work)?;
                        work.predicates += 1;
                        if ray_order(&point.x, direction, &hit.x, &old_point.x) == Ordering::Less {
                            for i in settled..j { settle(queries, &tour, join, scope, i, records, work)?; }
                            region = outgoing_region(tour.boundary, target, event.site, &old.level, region, work)?;
                            record(join.boundary(), actual, contact, hit.route, old.level, records, work)?;
                            p = event.site.clone(); settled = j+1; k = j+1;
                            advanced = true; break;
                        }
                    }
                }
            }
            // Endpoint event has priority. Exit crossings are considered only
            // after it fails, and the last clockwise admissible crossing wins.
            let previous = tour.event(j-1);
            let parent_region = source.arc_region(previous.after)?;
            let mut crossing: Option<(Site<C::Scalar>, Site<C::Scalar>, Route, LevelSource<C::Scalar>, RegionId)> = None;
            for &exit in target.region_exits(region)? {
                let (ends, route) = target.chord(exit)?;
                if route == Route::Null { continue; }
                let regions = target.chord_regions(exit)?;
                for slot in 0..2 {
                    work.retained_visits += 1;
                    let a = ends[slot]; let b = ends[1-slot];
                    let a_point = source_point(target_boundary, a, target.chord_level(exit)?, work)?;
                    let b_point = source_point(target_boundary, b, target.chord_level(exit)?, work)?;
                    let d = target_boundary.direction(a)?;
                    let Some(hit) = queries.shoot(tour.boundary, previous.site, event.site, false,
                        &a_point, d, work).map_err(FusionError::Query)? else { continue };
                    if route == Route::Finite && hit.route != Route::Finite { continue; }
                    work.predicates += 1;
                    if ray_order(&a_point.x, d, &hit.x, &b_point.x) == Ordering::Greater { continue; }
                    let Some(contact) = old_arrival(tour.boundary, &hit, d, work)? else { continue };
                    if tour.compare(&contact, &p, work) != Ordering::Greater { continue; }
                    let contact_point = source_point(tour.boundary, &contact, target.chord_level(exit)?, work)?;
                    let reverse = raw_region(queries, source, parent_region, &contact_point, d.opposite(), work)?.ok_or(FusionError::MissingArrival)?;
                    work.predicates += 1;
                    if ray_order(&contact_point.x, d.opposite(), &reverse.x, &a_point.x) == Ordering::Less { continue; }
                    let replace = crossing.as_ref().is_none_or(|(old, _, _, _, _)| tour.compare(&contact, old, work) == Ordering::Greater);
                    if replace {
                        // CW outgoing germ enters the LEFT of a->b. It need
                        // not enter the other region; a wiggling arc can stay.
                        crossing = Some((contact, join.contact_site(scope.opposite(), a.clone())?, hit.route,
                            target.chord_level(exit)?.clone(), regions[1-slot]));
                    }
                }
            }
            if let Some((contact, a, route, level, next_region)) = crossing {
                for i in settled..j { settle(queries, &tour, join, scope, i, records, work)?; }
                record(join.boundary(), a, join.contact_site(scope, contact.clone())?, route, level, records, work)?;
                p = contact; settled = j; k = j; region = next_region;
                if tour.compare(&p, event.site, work) == Ordering::Equal { settled = j+1; k = j+1; }
                advanced = true; break;
            }
        }
        if !advanced {
            for i in settled..=tour.last_index() { settle(queries, &tour, join, scope, i, records, work)?; }
            break;
        }
    }
    Ok(())
}

/// Fusion only (§3.1): output regions may temporarily have more than four exits.
/// Conformality restoration is a separate constructive §3.2 operation.
pub fn fuse<'a, C: Curve, Q: FusionQueries<'a, C>>(left: &Submap<'a, C>,
    right: &Submap<'a, C>, queries: &mut Q, work: &mut Work)
    -> Result<Submap<'a, C>, FusionError<Q::Error>>
{
    if left.decomposition().is_none() || right.decomposition().is_none() {
        return Err(FusionError::Map(MapError::NonConformal));
    }
    let join = Join::new(left, right, work)?;
    let mut records = Vec::with_capacity(left.chord_ids().count() + right.chord_ids().count() + 4);
    for scope in [Scope::First, Scope::Second] { pass(queries, [left,right], join, scope, &mut records, work)?; }
    let boundary = join.boundary();
    records.sort_unstable_by(|a,b| {
        work.predicates += 1;
        boundary.compare_sites(&a.endpoints[0], &b.endpoints[0]).then_with(|| {
            work.predicates += 1; boundary.compare_sites(&a.endpoints[1], &b.endpoints[1])
        })
    });
    records.dedup_by(|a,b| a.endpoints == b.endpoints && a.route == b.route);
    Submap::from_verified_chords(&boundary, records, work).map_err(FusionError::Map)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::base::{BaseError, full_visibility};
    use crate::boundary::Chain;
    use crate::hierarchy::{Catalogue, MergeEngine, grade};
    use crate::input::VertexId;

    /// The fixtures fit in one real constant-size catalogue leaf.
    struct Leaves;
    impl<'a> MergeEngine<'a> for Leaves {
        type Error = BaseError;
        fn base_map(&mut self, boundary: Boundary<'a>, work: &mut Work) -> Result<Submap<'a>, BaseError> {
            full_visibility(boundary, work)
        }
        fn merge(&mut self, left: &Submap<'a>, right: &Submap<'a>, _: usize,
            _: &Catalogue<'a>, work: &mut Work) -> Result<Submap<'a>, BaseError>
        {
            let chain = Chain::new(left.input(), left.chain().start, right.chain().end)?;
            full_visibility(Boundary::new(left.input(), chain)?, work)
        }
    }

    fn partner<'s>(map: &'s Submap<'_>, site: &Site) -> Option<&'s Site> {
        map.chord_ids().find_map(|chord| {
            let (ends, _) = map.chord(chord).unwrap();
            if ends[0] == site { Some(ends[1]) }
            else if ends[1] == site { Some(ends[0]) } else { None }
        })
    }

    #[test]
    fn endpoint_event_on_remote_shared_level_exit_enters_outgoing_region() {
        let points = [(0,-6),(1,9),(2,7),(3,-7),(4,10)].map(|(x,y)| Point::integer(x,y));
        let input = Input::open(&points).unwrap();
        let mut work = Work::default();
        let catalogue = Catalogue::build(&input, 4, &mut Leaves, &mut work).unwrap();
        let whole = Boundary::new(&input, Chain::new(&input, VertexId(0), VertexId(4)).unwrap()).unwrap();
        let expected = full_visibility(whole, &mut work).unwrap();
        for gamma in [0,1,2,4,8] {
            let left_boundary = Boundary::new(&input, Chain::new(&input, VertexId(0), VertexId(2)).unwrap()).unwrap();
            let right_boundary = Boundary::new(&input, Chain::new(&input, VertexId(2), VertexId(4)).unwrap()).unwrap();
            let mut left = full_visibility(left_boundary, &mut work).unwrap();
            let mut right = full_visibility(right_boundary, &mut work).unwrap();
            if gamma != 0 {
                left.coarsen(&left_boundary, gamma, &mut work).unwrap();
                right.coarsen(&right_boundary, gamma, &mut work).unwrap();
            }
            let actual = fuse(&left, &right, &mut ArcQueries::new(&catalogue, grade(gamma.max(1))), &mut work).unwrap();
            if gamma == 0 {
                for site in whole.occurrences() {
                    assert_eq!(partner(&actual, &site), partner(&expected, &site), "{site:?}");
                }
            }
            // Even a coarse retained chord must end at the first blocker, not
            // an obsolete old-map partner left behind by the region transition.
            let anchor = whole.occurrences().next().unwrap();
            let circle = whole.arc(&anchor, &anchor, true).unwrap();
            for chord in actual.chord_ids() {
                let (ends, route) = actual.chord(chord).unwrap();
                if let Some(null) = whole.null_contact(ends[0]).unwrap() {
                    assert_eq!(route, Route::Null);
                    assert_eq!(ends[1], &null);
                } else {
                    let nearest = whole.nearest_contacts(&circle, ends[0], whole.direction(ends[0]).unwrap()).unwrap().unwrap();
                    assert_eq!(route, nearest.route);
                    assert_eq!(whole.point(ends[1]).unwrap().x, nearest.x);
                }
            }
        }
    }
}
