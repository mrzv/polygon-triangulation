//! Sparse chord topology on a curve's implicit clockwise double boundary.
//!
//! Callers certify geometric visibility. This module checks boundary identity
//! and noncrossing topology; it never scans the input to manufacture an oracle.
use std::cmp::Ordering;
use std::fmt;

use crate::boundary::{Boundary, BoundaryError, Chain, Site};
use crate::decomposition::{Decomposition, DecompositionError, Node};
use crate::geometry::Route;
use crate::input::Input;
use crate::work::Work;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegionId(pub usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChordId(pub usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ArcId(pub usize);

/// A chord whose visibility and chosen spherical route the caller has proved.
#[derive(Debug)]
pub struct VisibleChord {
    pub endpoints: [Site; 2],
    pub route: Route,
}

#[derive(Debug)]
pub enum MapError {
    Boundary(BoundaryError),
    WrongCurve,
    OccupiedEndpoint,
    CrossingChords,
    InvalidRegion,
    InvalidChord,
    InvalidArc,
    PointOutsideRegion,
    NonConformal,
    NormalFormInvalid,
    Decomposition(DecompositionError),
}
impl fmt::Display for MapError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for MapError {}
impl From<BoundaryError> for MapError {
    fn from(error: BoundaryError) -> Self { Self::Boundary(error) }
}

#[derive(Clone, Debug)]
struct Endpoint {
    site: Site,
    mate: usize,
    chord: ChordId,
    slot: usize,
    before: ArcId,
    after: ArcId,
}
#[derive(Clone, Debug)]
struct Arc {
    start: Option<usize>,
    end: Option<usize>,
    full: bool,
    region: RegionId,
    live: bool,
}
#[derive(Clone, Debug)]
struct Region {
    arcs: Vec<ArcId>,
    exits: Vec<ChordId>,
    live: bool,
}
#[derive(Clone, Debug)]
struct Chord {
    endpoints: [usize; 2],
    route: Route,
    regions: [RegionId; 2],
    live: bool,
}

/// Normal form is explicitly rebuilt after a batch of local mutations.
#[derive(Clone, Debug)]
pub struct Submap<'a> {
    chain: Chain,
    input: &'a Input,
    endpoints: Vec<Endpoint>,
    arcs: Vec<Arc>,
    regions: Vec<Region>,
    chords: Vec<Chord>,
    dead_chords: usize,
    end_incidence: [[[ArcId; 2]; 2]; 2],
    canonical: Vec<ArcId>,
    decomposition: Option<Decomposition>,
}

impl<'a> Submap<'a> {
    /// Build in O(k log k) boundary comparisons and O(k) topology work.
    /// Input chords must be mutually visible with the supplied routes.
    pub fn from_verified_chords(
        boundary: &Boundary<'a>,
        input: Vec<VisibleChord>,
        work: &mut Work,
    ) -> Result<Self, MapError> {
        let mut map = Self {
            chain: boundary.chain(), input: boundary.input(),
            endpoints: Vec::with_capacity(2 * input.len()),
            arcs: Vec::new(), regions: Vec::new(), chords: Vec::with_capacity(input.len()),
            dead_chords: 0, end_incidence: [[[ArcId(0); 2]; 2]; 2],
            canonical: Vec::new(), decomposition: None,
        };
        for (i, chord) in input.into_iter().enumerate() {
            let [a, b] = chord.endpoints;
            boundary.validate_site(&a)?;
            boundary.validate_site(&b)?;
            let pair = [map.endpoints.len(), map.endpoints.len() + 1];
            for (slot, site) in [a, b].into_iter().enumerate() {
                map.endpoints.push(Endpoint {
                    site, mate: pair[1 - slot], chord: ChordId(i), slot,
                    before: ArcId(0), after: ArcId(0),
                });
            }
            map.chords.push(Chord {
                endpoints: pair, route: chord.route,
                regions: [RegionId(0); 2], live: true,
            });
        }
        if map.endpoints.is_empty() {
            map.arcs.push(Arc { start: None, end: None, full: true, region: RegionId(0), live: true });
            map.regions.push(Region { arcs: vec![ArcId(0)], exits: Vec::new(), live: true });
        } else {
            let mut order: Vec<usize> = (0..map.endpoints.len()).collect();
            order.sort_unstable_by(|&a, &b| {
                work.predicates += 1;
                boundary.compare_sites(&map.endpoints[a].site, &map.endpoints[b].site)
            });
            for adjacent in order.windows(2) {
                if boundary.compare_sites(&map.endpoints[adjacent[0]].site,
                    &map.endpoints[adjacent[1]].site) == Ordering::Equal {
                    return Err(MapError::OccupiedEndpoint);
                }
            }
            for i in 0..order.len() {
                let a = order[i];
                let b = order[(i + 1) % order.len()];
                let id = ArcId(map.arcs.len());
                map.arcs.push(Arc {
                    start: Some(a), end: Some(b), full: false,
                    region: RegionId(usize::MAX), live: true,
                });
                map.endpoints[a].after = id;
                map.endpoints[b].before = id;
            }
            for i in 0..map.arcs.len() {
                if map.arcs[i].region.0 != usize::MAX { continue; }
                let id = RegionId(map.regions.len());
                let cycle = map.face_cycle(ArcId(i));
                for &arc in &cycle { map.arcs[arc.0].region = id; }
                map.regions.push(Region { arcs: cycle, exits: Vec::new(), live: true });
            }
            // Noncrossing chords cut a disk into exactly k + 1 regions.
            if map.regions.len() != map.chords.len() + 1 {
                return Err(MapError::CrossingChords);
            }
            for i in 0..map.regions.len() { map.reassign_region(RegionId(i)); }
        }
        map.rebuild_normal_form(boundary, work)?;
        Ok(map)
    }

    pub fn chain(&self) -> Chain { self.chain }
    pub fn input(&self) -> &'a Input { self.input }
    pub fn region_ids(&self) -> impl Iterator<Item = RegionId> + '_ {
        self.regions.iter().enumerate().filter(|(_, r)| r.live).map(|(i, _)| RegionId(i))
    }
    pub fn chord_ids(&self) -> impl Iterator<Item = ChordId> + '_ {
        self.chords.iter().enumerate().filter(|(_, c)| c.live).map(|(i, _)| ChordId(i))
    }
    pub fn region_arcs(&self, region: RegionId) -> Result<&[ArcId], MapError> {
        Ok(&self.region(region)?.arcs)
    }
    pub fn region_exits(&self, region: RegionId) -> Result<&[ChordId], MapError> {
        Ok(&self.region(region)?.exits)
    }
    pub fn chord(&self, chord: ChordId) -> Result<([&Site; 2], Route), MapError> {
        let c = self.live_chord(chord)?;
        Ok(([&self.endpoints[c.endpoints[0]].site, &self.endpoints[c.endpoints[1]].site], c.route))
    }
    pub fn arc_sites(&self, arc: ArcId) -> Option<(&Site, &Site, bool)> {
        let a = self.arcs.get(arc.0)?;
        if !a.live { return None; }
        Some((&self.endpoints[a.start?].site, &self.endpoints[a.end?].site, a.full))
    }
    /// Chord/slot identities for an arc's retained endpoints, without site lookup.
    pub fn arc_endpoints(&self, arc: ArcId) -> Option<[(ChordId, usize); 2]> {
        let a = self.arcs.get(arc.0)?;
        if !a.live { return None; }
        Some([a.start?, a.end?].map(|id| {
            let endpoint = &self.endpoints[id];
            (endpoint.chord, endpoint.slot)
        }))
    }
    pub fn decomposition(&self) -> Option<&Decomposition> { self.decomposition.as_ref() }
    pub fn canonical_arcs(&self) -> &[ArcId] { &self.canonical }

    pub fn region_weight(&self, boundary: &Boundary<'_>, id: RegionId) -> Result<usize, MapError> {
        self.check_curve(boundary)?;
        let mut weight = 0;
        for &arc in &self.region(id)?.arcs {
            weight = weight.max(self.arc_weight(boundary, arc)?);
        }
        Ok(weight)
    }

    /// Local chord insertion; caller proves the open route stays in this region.
    /// Work is proportional to this region's degree, not the input-chain length.
    pub fn insert_verified(
        &mut self, boundary: &Boundary<'_>, region: RegionId, chord: VisibleChord,
    ) -> Result<ChordId, MapError> {
        self.check_curve(boundary)?;
        self.region(region)?;
        for site in &chord.endpoints { boundary.validate_site(site)?; }
        if boundary.compare_sites(&chord.endpoints[0], &chord.endpoints[1]) == Ordering::Equal {
            return Err(MapError::OccupiedEndpoint);
        }
        for site in &chord.endpoints { self.containing_arc(boundary, region, site)?; }
        let id = ChordId(self.chords.len());
        let pair = [self.endpoints.len(), self.endpoints.len() + 1];
        for (slot, site) in chord.endpoints.into_iter().enumerate() {
            self.endpoints.push(Endpoint {
                site, mate: pair[1 - slot], chord: id, slot,
                before: ArcId(0), after: ArcId(0),
            });
        }
        for endpoint in pair {
            let arc = self.containing_arc(boundary, region, &self.endpoints[endpoint].site)?;
            self.split_arc(region, arc, endpoint);
        }
        self.chords.push(Chord { endpoints: pair, route: chord.route, regions: [region; 2], live: true });
        let first = self.face_cycle(self.endpoints[pair[0]].after);
        let second = self.face_cycle(self.endpoints[pair[1]].after);
        self.regions[region.0].arcs = first;
        let new_region = RegionId(self.regions.len());
        self.regions.push(Region { arcs: second, exits: Vec::new(), live: true });
        self.reassign_region(region);
        self.reassign_region(new_region);
        self.invalidate();
        Ok(id)
    }

    /// Delete and clean up both nonintrinsic endpoints. Intrinsic sites remain
    /// in the implicit boundary even though they are no longer retained endpoints.
    pub fn delete(&mut self, chord: ChordId) -> Result<RegionId, MapError> {
        let c = self.live_chord(chord)?;
        let pair = c.endpoints;
        let [keep, drop] = c.regions;
        let mut joined = std::mem::take(&mut self.regions[keep.0].arcs);
        joined.append(&mut self.regions[drop.0].arcs);
        for endpoint in pair { self.join_at_endpoint(endpoint); }
        joined.retain(|a| self.arcs[a.0].live);
        self.chords[chord.0].live = false;
        self.dead_chords += 1;
        self.regions[drop.0].live = false;
        self.regions[drop.0].exits.clear();
        self.regions[keep.0].arcs = joined;
        self.reassign_region(keep);
        self.invalidate();
        Ok(keep)
    }

    /// Section 3.3's contraction predicate, with bounded-degree reconsideration.
    /// Removing a leaf can lower a previously ineligible neighbor's degree;
    /// each deletion queues at most four neighbors. No global geometry scans.
    /// Compacts storage after contraction; all previously issued IDs expire.
    pub fn coarsen(
        &mut self, boundary: &Boundary<'_>, gamma: usize, work: &mut Work,
    ) -> Result<(), MapError> {
        self.check_curve(boundary)?;
        for region in &self.regions {
            work.retained_visits += 1;
            if region.live && region.exits.len() > 4 { return Err(MapError::NonConformal); }
        }
        let mut pending: Vec<ChordId> = (0..self.chords.len()).rev().map(ChordId).collect();
        let mut queued = vec![true; self.chords.len()];
        while let Some(id) = pending.pop() {
            work.retained_visits += 1;
            queued[id.0] = false;
            if !self.chords[id.0].live { continue; }
            let regions = self.chords[id.0].regions;
            let degrees = regions.map(|r| self.regions[r.0].exits.len());
            if degrees[0] >= 3 && degrees[1] >= 3 { continue; }
            work.predicates += 1;
            work.retained_visits += (degrees[0] + degrees[1]) as u128;
            if self.contracted_weight(boundary, id)? <= gamma {
                let merged = self.delete(id)?;
                for &next in &self.regions[merged.0].exits {
                    work.retained_visits += 1;
                    if !queued[next.0] {
                        queued[next.0] = true;
                        pending.push(next);
                    }
                }
            }
        }
        self.rebuild_normal_form(boundary, work)
    }

    /// Publish compact normal form. Previously issued IDs expire.
    pub fn rebuild_normal_form(
        &mut self, boundary: &Boundary<'_>, work: &mut Work,
    ) -> Result<(), MapError> {
        self.check_curve(boundary)?;
        self.compact_arenas(work);
        self.canonical.clear();
        for (i, arc) in self.arcs.iter().enumerate() {
            work.retained_visits += 1;
            if arc.live { self.canonical.push(ArcId(i)); }
        }
        self.canonical.sort_unstable_by(|a, b| {
            work.predicates += 1;
            match (self.arcs[a.0].start, self.arcs[b.0].start) {
                (Some(a), Some(b)) => boundary.compare_sites(&self.endpoints[a].site, &self.endpoints[b].site),
                _ => Ordering::Equal,
            }
        });
        self.canonical.shrink_to_fit();
        for (i, vertex) in [self.chain.start, self.chain.end].into_iter().enumerate() {
            for (j, side) in [crate::boundary::Side::Left, crate::boundary::Side::Right].into_iter().enumerate() {
                let site = Site::Vertex { vertex, side, slot: crate::boundary::Slot::Single };
                self.end_incidence[i][j] = self.site_incidence(boundary, &site);
            }
        }
        self.decomposition = None;
        let mut regions = Vec::with_capacity(self.regions.len());
        for (i, region) in self.regions.iter().enumerate() {
            work.retained_visits += 1;
            if region.live {
                if region.exits.len() > 4 { return Ok(()); }
                regions.push(RegionId(i));
            }
        }
        let mut chords = Vec::with_capacity(self.chords.len());
        for (i, chord) in self.chords.iter().enumerate() {
            work.retained_visits += 1;
            if chord.live { chords.push(ChordId(i)); }
        }
        let mut dense = vec![usize::MAX; self.regions.len()];
        for (i, region) in regions.iter().enumerate() {
            work.retained_visits += 1;
            dense[region.0] = i;
        }
        let edges: Vec<(usize, usize)> = chords.iter().map(|id| {
            work.retained_visits += 1;
            let r = self.chords[id.0].regions;
            (dense[r[0].0], dense[r[1].0])
        }).collect();
        let mut decomposition = Decomposition::build(regions.len(), &edges, work)
            .map_err(MapError::Decomposition)?;
        for node in &mut decomposition.nodes {
            work.retained_visits += 1;
            match node {
                Node::Region(id) => *id = regions[*id].0,
                Node::Split { chord, .. } => *chord = chords[*chord].0,
            }
        }
        self.decomposition = Some(decomposition);
        Ok(())
    }

    fn check_curve(&self, boundary: &Boundary<'_>) -> Result<(), MapError> {
        if self.chain == boundary.chain() && std::ptr::eq(self.input, boundary.input()) {
            Ok(())
        } else {
            Err(MapError::WrongCurve)
        }
    }
    fn region(&self, id: RegionId) -> Result<&Region, MapError> {
        self.regions.get(id.0).filter(|r| r.live).ok_or(MapError::InvalidRegion)
    }
    fn live_chord(&self, id: ChordId) -> Result<&Chord, MapError> {
        self.chords.get(id.0).filter(|c| c.live).ok_or(MapError::InvalidChord)
    }
    fn invalidate(&mut self) { self.canonical.clear(); self.decomposition = None; }
    fn face_cycle(&self, start: ArcId) -> Vec<ArcId> {
        let mut result = Vec::new();
        let mut arc = start;
        loop {
            result.push(arc);
            let endpoint = self.arcs[arc.0].end.expect("a retained chord face has endpoints");
            arc = self.endpoints[self.endpoints[endpoint].mate].after;
            if arc == start { return result; }
        }
    }
    fn reassign_region(&mut self, id: RegionId) {
        let region = &mut self.regions[id.0];
        region.exits.clear();
        for &arc in &region.arcs {
            self.arcs[arc.0].region = id;
            if let Some(endpoint) = self.arcs[arc.0].start {
                let e = &self.endpoints[endpoint];
                self.chords[e.chord.0].regions[e.slot] = id;
                region.exits.push(e.chord);
            }
        }
    }
    fn arc_weight(&self, boundary: &Boundary<'_>, id: ArcId) -> Result<usize, MapError> {
        let arc = &self.arcs[id.0];
        match (arc.start, arc.end) {
            (Some(a), Some(b)) => Ok(boundary.arc_weight(&self.endpoints[a].site, &self.endpoints[b].site, arc.full)?),
            _ => Ok(2 * (self.chain.end.0 - self.chain.start.0)),
        }
    }
    fn containing_arc(&self, boundary: &Boundary<'_>, region: RegionId, site: &Site) -> Result<ArcId, MapError> {
        for &id in &self.regions[region.0].arcs {
            let arc = &self.arcs[id.0];
            let (Some(a), Some(b)) = (arc.start, arc.end) else { return Ok(id); };
            let from = boundary.compare_sites(&self.endpoints[a].site, site);
            let to = boundary.compare_sites(site, &self.endpoints[b].site);
            if from == Ordering::Equal || to == Ordering::Equal { return Err(MapError::OccupiedEndpoint); }
            let wraps = boundary.compare_sites(&self.endpoints[a].site, &self.endpoints[b].site) != Ordering::Less;
            if arc.full || if wraps { from == Ordering::Less || to == Ordering::Less }
                else { from == Ordering::Less && to == Ordering::Less } { return Ok(id); }
        }
        Err(MapError::PointOutsideRegion)
    }
    fn split_arc(&mut self, region: RegionId, id: ArcId, endpoint: usize) {
        if self.arcs[id.0].start.is_none() {
            self.arcs[id.0].start = Some(endpoint);
            self.arcs[id.0].end = Some(endpoint);
            self.endpoints[endpoint].before = id;
            self.endpoints[endpoint].after = id;
            return;
        }
        let end = self.arcs[id.0].end.unwrap();
        let next = ArcId(self.arcs.len());
        self.arcs.push(Arc { start: Some(endpoint), end: Some(end), full: false, region, live: true });
        self.arcs[id.0].end = Some(endpoint);
        self.arcs[id.0].full = false;
        self.endpoints[end].before = next;
        self.endpoints[endpoint].before = id;
        self.endpoints[endpoint].after = next;
        self.regions[region.0].arcs.push(next);
    }
    fn join_at_endpoint(&mut self, endpoint: usize) {
        let before = self.endpoints[endpoint].before;
        let after = self.endpoints[endpoint].after;
        if before == after {
            self.arcs[before.0].start = None;
            self.arcs[before.0].end = None;
            self.arcs[before.0].full = true;
        } else {
            let end = self.arcs[after.0].end.unwrap();
            self.arcs[before.0].end = Some(end);
            self.arcs[before.0].full = self.arcs[before.0].start == Some(end);
            self.endpoints[end].before = before;
            self.arcs[after.0].live = false;
        }
    }
    pub(crate) fn contracted_weight(&self, boundary: &Boundary<'_>, id: ChordId) -> Result<usize, MapError> {
        let chord = &self.chords[id.0];
        let removed = chord.endpoints;
        let mut weight = 0;
        let mut any = false;
        for region in chord.regions {
            for &arc in &self.regions[region.0].arcs {
                let a = &self.arcs[arc.0];
                let start = a.start.unwrap();
                if removed.contains(&start) { continue; }
                let mut end = a.end.unwrap();
                while removed.contains(&end) {
                    end = self.arcs[self.endpoints[end].after.0].end.unwrap();
                }
                any = true;
                weight = weight.max(boundary.arc_weight(
                    &self.endpoints[start].site, &self.endpoints[end].site, start == end,
                )?);
            }
        }
        if any { Ok(weight) } else { Ok(2 * (self.chain.end.0 - self.chain.start.0)) }
    }
}

/// At most six distinct arc incidences at one geometric boundary point.
#[derive(Debug)]
pub struct ArcMatches {
    arcs: [ArcId; 6],
    len: usize,
}
impl ArcMatches {
    pub fn as_slice(&self) -> &[ArcId] { &self.arcs[..self.len] }
    fn push(&mut self, id: ArcId) {
        if !self.as_slice().contains(&id) {
            assert!(self.len < self.arcs.len(), "double-boundary incidence bound");
            self.arcs[self.len] = id;
            self.len += 1;
        }
    }
}

impl Submap<'_> {
    /// Double identification, Section 2.4: O(log k) comparisons, no edge scan.
    /// Requires normal form; rebuild after mutations before calling this.
    pub fn double_identify(
        &self, boundary: &Boundary<'_>, edge: crate::input::EdgeId,
        t: &crate::geometry::Rational,
    ) -> Result<ArcMatches, MapError> {
        use crate::boundary::{Side, Slot};
        self.check_curve(boundary)?;
        if self.canonical.is_empty() { return Err(MapError::NormalFormInvalid); }
        let mut matches = ArcMatches { arcs: [ArcId(0); 6], len: 0 };
        for side in [Side::Left, Side::Right] {
            let site = boundary.normalize_site(&Site::Edge { edge, t: t.clone(), side })?;
            self.identify_site(boundary, &site, &mut matches);
            if let Site::Vertex { vertex, slot, .. } = site {
                if slot != Slot::Single {
                    let opposite = if slot == Slot::Incoming { Slot::Outgoing } else { Slot::Incoming };
                    self.identify_site(boundary, &Site::Vertex { vertex, side, slot: opposite }, &mut matches);
                }
            }
        }
        Ok(matches)
    }

    fn identify_site(&self, boundary: &Boundary<'_>, site: &Site, result: &mut ArcMatches) {
        for arc in self.site_incidence(boundary, site) { result.push(arc); }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boundary::{Side, Slot};
    use crate::geometry::Point;
    use crate::input::{EdgeId, VertexId};
    use num_traits::One;

    fn cap(vertex: usize, side: Side) -> Site {
        Site::Vertex { vertex: VertexId(vertex), side, slot: Slot::Single }
    }
    fn cap_chord(vertex: usize) -> VisibleChord {
        VisibleChord { endpoints: [cap(vertex, Side::Left), cap(vertex, Side::Right)], route: Route::Wrap }
    }
    fn one_edge() -> Input {
        Input::open(&[Point::integer(0, 0), Point::integer(0, 1)]).unwrap()
    }
    fn boundary(input: &Input) -> Boundary<'_> {
        Boundary::new(input, Chain::new(input, VertexId(0), VertexId(input.len() - 1)).unwrap()).unwrap()
    }

    #[test]
    fn deletion_coalesces_pieces_and_restores_whole_boundary() {
        let input = one_edge();
        let b = boundary(&input);
        let mut work = Work::default();
        let mut map = Submap::from_verified_chords(&b, vec![cap_chord(0), cap_chord(1)], &mut work).unwrap();
        let regions: Vec<_> = map.region_ids().collect();
        let mut weights: Vec<_> = regions.iter().map(|&r| map.region_weight(&b, r).unwrap()).collect();
        weights.sort_unstable();
        assert_eq!(weights, [0, 0, 1]);
        let identified = map.double_identify(&b, EdgeId(0), &crate::geometry::Rational::new(1.into(), 2.into())).unwrap();
        assert_eq!(identified.as_slice().len(), 2);
        map.coarsen(&b, 2, &mut work).unwrap();
        let remaining: Vec<_> = map.region_ids().collect();
        assert_eq!(remaining.len(), 1);
        assert_eq!(map.region_weight(&b, remaining[0]).unwrap(), 2);
        assert!(map.chord_ids().next().is_none());
        assert!(matches!(map.decomposition().unwrap().nodes[0], Node::Region(_)));
    }

    #[test]
    fn local_insert_and_delete_split_the_correct_faces() {
        let input = one_edge();
        let b = boundary(&input);
        let mut work = Work::default();
        let mut map = Submap::from_verified_chords(&b, vec![], &mut work).unwrap();
        let first = map.insert_verified(&b, RegionId(0), cap_chord(0)).unwrap();
        assert_eq!(map.region_ids().count(), 2);
        assert!(matches!(map.double_identify(&b, EdgeId(0), &crate::geometry::Rational::one()), Err(MapError::NormalFormInvalid)));
        let target = map.region_ids().find(|&r| map.region_weight(&b, r).unwrap() == 2).unwrap();
        let second = map.insert_verified(&b, target, cap_chord(1)).unwrap();
        map.rebuild_normal_form(&b, &mut work).unwrap();
        assert_eq!(map.region_ids().count(), 3);
        let merged = map.delete(first).unwrap();
        assert_eq!(map.region_ids().count(), 2);
        assert_eq!(map.region_weight(&b, merged).unwrap(), 2);
        let all = map.delete(second).unwrap();
        assert_eq!(map.region_weight(&b, all).unwrap(), 2);
        map.rebuild_normal_form(&b, &mut work).unwrap();
        assert_eq!(map.canonical_arcs().len(), 1);
    }

    #[test]
    fn topology_rejects_interleaving_chords_and_shared_endpoints() {
        let input = one_edge();
        let b = boundary(&input);
        let mut work = Work::default();
        let crossed = vec![
            VisibleChord { endpoints: [cap(0, Side::Left), cap(1, Side::Right)], route: Route::Finite },
            VisibleChord { endpoints: [cap(1, Side::Left), cap(0, Side::Right)], route: Route::Finite },
        ];
        assert!(matches!(Submap::from_verified_chords(&b, crossed, &mut work), Err(MapError::CrossingChords)));
        assert!(matches!(Submap::from_verified_chords(&b, vec![cap_chord(0), cap_chord(0)], &mut work), Err(MapError::OccupiedEndpoint)));
    }

    #[test]
    fn equal_indices_in_another_input_do_not_alias_a_map() {
        let input = one_edge();
        let other = one_edge();
        let b = boundary(&input);
        let other_b = boundary(&other);
        let map = Submap::from_verified_chords(&b, vec![], &mut Work::default()).unwrap();
        assert!(matches!(map.region_weight(&other_b, RegionId(0)), Err(MapError::WrongCurve)));
    }

    #[test]
    fn coarsening_rechecks_chords_after_null_leaf_degree_changes() {
        let points = [(0,0),(1,4),(2,2),(3,4),(4,2),(5,4),(6,0)]
            .map(|(x,y)| Point::integer(x,y));
        let input = Input::open(&points).unwrap();
        let b = boundary(&input);
        for reverse in [false, true] {
            let mut chords = vec![VisibleChord {
                endpoints: [
                    Site::Edge { edge: EdgeId(2), t: crate::geometry::Rational::new(19.into(),57.into()), side: Side::Right },
                    Site::Edge { edge: EdgeId(7), t: crate::geometry::Rational::new(23.into(),27.into()), side: Side::Right },
                ],
                route: Route::Finite,
            }];
            for source in b.occurrences() {
                if let Some(target) = b.null_contact(&source).unwrap() {
                    if b.compare_sites(&source,&target) == Ordering::Less {
                        chords.push(VisibleChord { endpoints: [source,target], route: Route::Null });
                    }
                }
            }
            if reverse { chords.reverse(); }
            let mut work = Work::default();
            let mut map = Submap::from_verified_chords(&b,chords,&mut work).unwrap();
            let id = if reverse { ChordId(5) } else { ChordId(0) };
            assert!(map.chord_regions(id).unwrap().into_iter().all(|r| map.region_exits(r).unwrap().len() >= 3));
            map.coarsen(&b,16,&mut work).unwrap();
            assert!(map.chord_ids().next().is_none());
            let oracle = crate::oracle::RayOracle::build(map,16,&mut work).unwrap();
            assert_eq!(oracle.map().region_ids().count(),1);
        }
    }

    #[test]
    fn coarse_storage_discards_fine_region_capacities() {
        let points: Vec<_> = (0..35).map(|i| Point::integer(i,if i % 2 == 0 { 0 } else { 2 })).collect();
        let input = Input::open(&points).unwrap();
        let b = boundary(&input);
        let mut chords = Vec::new();
        for source in b.occurrences() {
            if let Some(target) = b.null_contact(&source).unwrap() {
                if b.compare_sites(&source,&target) == Ordering::Less {
                    // Reversal makes deletion retain the large central region.
                    chords.push(VisibleChord { endpoints: [target,source], route: Route::Null });
                }
            }
        }
        let mut work = Work::default();
        let mut map = Submap::from_verified_chords(&b,chords,&mut work).unwrap();
        let central = map.region_ids().max_by_key(|&r| map.region_exits(r).unwrap().len()).unwrap();
        let ids: Vec<_> = map.chord_ids().collect();
        for id in ids.iter().take(ids.len()-4) {
            assert_eq!(map.delete(*id).unwrap(),central);
        }
        map.coarsen(&b,2*b.chain().edge_count(),&mut work).unwrap();
        assert_eq!(map.region_ids().count(),1);
        assert!(map.chord_ids().next().is_none());
        let allocation: usize = map.regions.iter().map(|r| r.arcs.capacity()+r.exits.capacity()).sum();
        let retained: usize = map.regions.iter().map(|r| r.arcs.len()+r.exits.len()).sum();
        assert!(allocation <= 8*retained.max(1),"coarse region kept fine allocations: {allocation}/{retained}");
    }
}

impl Submap<'_> {
    /// Reclaim obsolete retained records before publishing a saved coarse map.
    /// Otherwise tombstone capacities would retain the finer map at every grade.
    fn compact_arenas(&mut self, work: &mut Work) {
        if self.dead_chords == 0 { return; }
        let mut chords = vec![usize::MAX; self.chords.len()];
        let mut endpoints = vec![usize::MAX; self.endpoints.len()];
        let mut arcs = vec![usize::MAX; self.arcs.len()];
        let mut regions = vec![usize::MAX; self.regions.len()];
        let mut next = 0;
        for (i, chord) in self.chords.iter().enumerate() {
            work.retained_visits += 1;
            if chord.live { chords[i] = next; next += 1; }
        }
        next = 0;
        for (i, endpoint) in self.endpoints.iter().enumerate() {
            work.retained_visits += 1;
            if chords[endpoint.chord.0] != usize::MAX { endpoints[i] = next; next += 1; }
        }
        next = 0;
        for (i, arc) in self.arcs.iter().enumerate() {
            work.retained_visits += 1;
            if arc.live { arcs[i] = next; next += 1; }
        }
        next = 0;
        for (i, region) in self.regions.iter().enumerate() {
            work.retained_visits += 1;
            if region.live { regions[i] = next; next += 1; }
        }
        self.chords.retain(|chord| { work.retained_visits += 1; chord.live });
        self.endpoints.retain(|endpoint| {
            work.retained_visits += 1;
            chords[endpoint.chord.0] != usize::MAX
        });
        self.arcs.retain(|arc| { work.retained_visits += 1; arc.live });
        self.regions.retain(|region| { work.retained_visits += 1; region.live });
        for chord in &mut self.chords {
            work.retained_visits += 1;
            chord.endpoints = chord.endpoints.map(|id| endpoints[id]);
            chord.regions = chord.regions.map(|id| RegionId(regions[id.0]));
        }
        for endpoint in &mut self.endpoints {
            work.retained_visits += 1;
            endpoint.mate = endpoints[endpoint.mate];
            endpoint.chord = ChordId(chords[endpoint.chord.0]);
            endpoint.before = ArcId(arcs[endpoint.before.0]);
            endpoint.after = ArcId(arcs[endpoint.after.0]);
        }
        for arc in &mut self.arcs {
            work.retained_visits += 1;
            arc.start = arc.start.map(|id| endpoints[id]);
            arc.end = arc.end.map(|id| endpoints[id]);
            arc.region = RegionId(regions[arc.region.0]);
        }
        for region in &mut self.regions {
            work.retained_visits += 1;
            for id in &mut region.arcs { id.0 = arcs[id.0]; work.retained_visits += 1; }
            for id in &mut region.exits { id.0 = chords[id.0]; work.retained_visits += 1; }
            region.arcs.shrink_to_fit();
            region.exits.shrink_to_fit();
        }
        self.chords.shrink_to_fit();
        self.endpoints.shrink_to_fit();
        self.arcs.shrink_to_fit();
        self.regions.shrink_to_fit();
        self.dead_chords = 0;
        self.invalidate();
    }
}

impl Submap<'_> {
    pub fn arc_region(&self, arc: ArcId) -> Result<RegionId, MapError> {
        self.arcs.get(arc.0).filter(|a| a.live).map(|a| a.region).ok_or(MapError::InvalidArc)
    }
    /// Slot 0 is the right side of the dart from endpoint 0 to endpoint 1.
    pub fn chord_regions(&self, chord: ChordId) -> Result<[RegionId; 2], MapError> {
        Ok(self.live_chord(chord)?.regions)
    }
    /// Constant-time chain-end markers: [Left, Right] × [before, after].
    pub fn end_incident_arcs(&self, vertex: crate::input::VertexId) -> Result<[[ArcId; 2]; 2], MapError> {
        if self.canonical.is_empty() { return Err(MapError::NormalFormInvalid); }
        if vertex == self.chain.start { Ok(self.end_incidence[0]) }
        else if vertex == self.chain.end { Ok(self.end_incidence[1]) }
        else { Err(MapError::PointOutsideRegion) }
    }
    fn site_incidence(&self, boundary: &Boundary<'_>, site: &Site) -> [ArcId; 2] {
        if self.arcs[self.canonical[0].0].start.is_none() { return [self.canonical[0]; 2]; }
        let position = self.canonical.partition_point(|id| {
            boundary.compare_sites(&self.endpoints[self.arcs[id.0].start.unwrap()].site, site)
                != Ordering::Greater
        });
        let index = if position == 0 { self.canonical.len() - 1 } else { position - 1 };
        let after = self.canonical[index];
        let before = if boundary.compare_sites(
            &self.endpoints[self.arcs[after.0].start.unwrap()].site, site,
        ) == Ordering::Equal {
            self.canonical[(index + self.canonical.len() - 1) % self.canonical.len()]
        } else { after };
        [before, after]
    }
}
