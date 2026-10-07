//! Curve-local double boundary without an occurrence table. Clockwise order is
//! Left forward, end cap, Right backward, start cap. Arcs borrow their endpoints;
//! their positive edge pieces are described by at most three lazy side runs.
use crate::geometry::{Point, Rational, contact_route, ray_order};
pub use crate::geometry::{Direction, Route};
use crate::input::{EdgeId, Input, VertexId};
use crate::curve::Curve;
use crate::scalar::ExactScalar;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Side { Left, Right }
impl Side { pub fn opposite(self) -> Self { match self { Self::Left => Self::Right, Self::Right => Self::Left } } }
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Slot { Single, Incoming, Outgoing }
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Site<S = Rational> {
    Vertex { vertex: VertexId, side: Side, slot: Slot },
    Edge { edge: EdgeId, t: S, side: Side },
}
impl<S> Site<S> {
    pub fn side(&self) -> Side { match self { Self::Vertex { side, .. } | Self::Edge { side, .. } => *side } }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Chain { pub start: VertexId, pub end: VertexId }
impl Chain {
    pub fn new<C: Curve>(input: &C, start: VertexId, end: VertexId) -> Result<Self, BoundaryError> {
        if start.0 >= end.0 || end.0 >= input.len() { return Err(BoundaryError::InvalidChain); }
        Ok(Self { start, end })
    }
    pub fn edge_count(self) -> usize { self.end.0 - self.start.0 }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoundaryError {
    InvalidChain,
    OutsideChain,
    InvalidSlot,
    InvalidParameter,
    NoncanonicalSite,
    InvalidFullCircuit,
    DifferentInput,
    InvalidRoute,
}
impl fmt::Display for BoundaryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for BoundaryError {}

#[derive(Debug)]
pub struct Boundary<'a, C: Curve = Input> { input: &'a C, chain: Chain }
impl<C: Curve> Copy for Boundary<'_, C> {}
impl<C: Curve> Clone for Boundary<'_, C> { fn clone(&self) -> Self { *self } }

/// Exact point in forward input order; edge parameters remain forward on Right.
#[derive(Debug)]
pub enum Position<'s, S = Rational> { Vertex(VertexId), Edge { edge: EdgeId, t: &'s S } }
impl<S> Copy for Position<'_, S> {}
impl<S> Clone for Position<'_, S> { fn clone(&self) -> Self { *self } }
impl<'s, S: ExactScalar> Position<'s, S> {
    fn of(site: &'s Site<S>) -> Self {
        match site { Site::Vertex { vertex, .. } => Self::Vertex(*vertex), Site::Edge { edge, t, .. } => Self::Edge { edge: *edge, t } }
    }
    fn compare(self, other: Position<'_, S>) -> Ordering {
        match (self, other) {
            (Position::Vertex(a), Position::Vertex(b)) => a.cmp(&b),
            (Position::Vertex(a), Position::Edge { edge, .. }) => if a.0 <= edge.0 { Ordering::Less } else { Ordering::Greater },
            (Position::Edge { edge, .. }, Position::Vertex(b)) => if edge.0 < b.0 { Ordering::Less } else { Ordering::Greater },
            (Position::Edge { edge: a, t: at }, Position::Edge { edge: b, t: bt }) => a.cmp(&b).then_with(|| at.cmp(bt)),
        }
    }
    fn first_edge(self) -> usize { match self { Self::Vertex(v) => v.0, Self::Edge { edge, .. } => edge.0 } }
    fn last_edge(self) -> usize { match self { Self::Vertex(v) => v.0 - 1, Self::Edge { edge, .. } => edge.0 } }
}

#[derive(Debug)]
pub struct Arc<'s, S = Rational> { pub start: &'s Site<S>, pub end: &'s Site<S>, pub full_circuit: bool }
impl<S> Copy for Arc<'_, S> {}
impl<S> Clone for Arc<'_, S> { fn clone(&self) -> Self { *self } }
#[derive(Debug)]
pub struct SideRun<'s, S = Rational> { pub side: Side, pub from: Position<'s, S>, pub to: Position<'s, S> }
impl<S> Copy for SideRun<'_, S> {}
impl<S> Clone for SideRun<'_, S> { fn clone(&self) -> Self { *self } }
impl<'s, S: ExactScalar> SideRun<'s, S> {
    pub fn weight(self) -> usize {
        let (low, high) = if self.side == Side::Left { (self.from, self.to) } else { (self.to, self.from) };
        if low.compare(high) == Ordering::Equal { return 0; }
        high.last_edge() - low.first_edge() + 1
    }
    pub fn first_edge(self) -> Option<EdgeId> {
        if self.weight() == 0 { return None; }
        Some(EdgeId(if self.side == Side::Left { self.from.first_edge() } else { self.from.last_edge() }))
    }
    pub fn last_edge(self) -> Option<EdgeId> {
        if self.weight() == 0 { return None; }
        Some(EdgeId(if self.side == Side::Left { self.to.last_edge() } else { self.to.first_edge() }))
    }
    /// Owned closed clipping bounds. None means this edge has no
    /// positive-length piece in the run.
    pub fn clipped_interval(self, edge: EdgeId) -> Option<(S, S)> {
        if self.weight() == 0 { return None; }
        let (low, high) = if self.side == Side::Left { (self.from, self.to) } else { (self.to, self.from) };
        if edge.0 < low.first_edge() || edge.0 > high.last_edge() { return None; }
        let lo = match low { Position::Edge { edge: e, t } if e == edge => t.clone(), _ => S::zero_value() };
        let hi = match high { Position::Edge { edge: e, t } if e == edge => t.clone(), _ => S::one_value() };
        Some((lo, hi))
    }
    pub fn contains_parameter(self, edge: EdgeId, t: &S) -> bool {
        let position = Position::Edge { edge, t };
        let (low, high) = if self.side == Side::Left { (self.from, self.to) } else { (self.to, self.from) };
        low.compare(position) != Ordering::Greater && position.compare(high) != Ordering::Greater
    }
}

pub struct SideRuns<'s, S = Rational> { runs: [Option<SideRun<'s, S>>; 3], index: usize }
impl<'s, S: ExactScalar> Iterator for SideRuns<'s, S> {
    type Item = SideRun<'s, S>;
    fn next(&mut self) -> Option<Self::Item> {
        while self.index < 3 {
            let result = self.runs[self.index]; self.index += 1;
            if let Some(run) = result { if run.weight() != 0 { return Some(run); } }
        }
        None
    }
}

impl<'a, C: Curve> Boundary<'a, C> {
    pub fn new(input: &'a C, chain: Chain) -> Result<Self, BoundaryError> {
        Chain::new(input, chain.start, chain.end)?;
        Ok(Self { input, chain })
    }
    pub fn input(&self) -> &'a C { self.input }
    pub fn chain(&self) -> Chain { self.chain }
    pub fn is_extremum(&self, vertex: VertexId) -> bool {
        vertex.0 > self.chain.start.0 && vertex.0 < self.chain.end.0
            && self.input.edge_y_sign(EdgeId(vertex.0 - 1)) != self.input.edge_y_sign(EdgeId(vertex.0))
    }
    fn vertex_site(&self, vertex: VertexId, side: Side, incoming: bool) -> Site<C::Scalar> {
        let slot = if self.is_extremum(vertex) { if incoming { Slot::Incoming } else { Slot::Outgoing } } else { Slot::Single };
        Site::Vertex { vertex, side, slot }
    }
    pub fn normalize_site(&self, site: &Site<C::Scalar>) -> Result<Site<C::Scalar>, BoundaryError> {
        match site {
            Site::Vertex { vertex, slot, .. } => {
                if vertex.0 < self.chain.start.0 || vertex.0 > self.chain.end.0 { return Err(BoundaryError::OutsideChain); }
                let valid = if self.is_extremum(*vertex) { *slot != Slot::Single } else { *slot == Slot::Single };
                if !valid { return Err(BoundaryError::InvalidSlot); }
                Ok(site.clone())
            }
            Site::Edge { edge, t, side } => {
                if edge.0 < self.chain.start.0 || edge.0 >= self.chain.end.0 { return Err(BoundaryError::OutsideChain); }
                if t < &C::Scalar::zero_value() || t > &C::Scalar::one_value() { return Err(BoundaryError::InvalidParameter); }
                if t.is_zero_value() { Ok(self.vertex_site(VertexId(edge.0), *side, false)) }
                else if t.compare_one() == Ordering::Equal { Ok(self.vertex_site(VertexId(edge.0 + 1), *side, true)) }
                else { Ok(site.clone()) }
            }
        }
    }
    /// Validate an already canonical persistent identity, without cloning it.
    pub fn validate_site(&self, site: &Site<C::Scalar>) -> Result<(), BoundaryError> {
        match site {
            Site::Vertex { vertex, slot, .. } => {
                if vertex.0 < self.chain.start.0 || vertex.0 > self.chain.end.0 { return Err(BoundaryError::OutsideChain); }
                if (self.is_extremum(*vertex) && *slot == Slot::Single) || (!self.is_extremum(*vertex) && *slot != Slot::Single) { return Err(BoundaryError::InvalidSlot); }
            }
            Site::Edge { edge, t, .. } => {
                if edge.0 < self.chain.start.0 || edge.0 >= self.chain.end.0 { return Err(BoundaryError::OutsideChain); }
                if t <= &C::Scalar::zero_value() || t >= &C::Scalar::one_value() { return Err(BoundaryError::NoncanonicalSite); }
            }
        }
        Ok(())
    }
    /// Intrinsic coordinates stay borrowed; computed contacts use actual curve geometry.
    pub fn point(&self, site: &Site<C::Scalar>) -> Result<Cow<'a, Point<C::Scalar>>, BoundaryError> {
        self.validate_site(site)?;
        Ok(match site {
            Site::Vertex { vertex, .. } => self.input.vertex(*vertex),
            Site::Edge { edge, t, .. } => Cow::Owned(self.input.edge_point(*edge, t)),
        })
    }
    /// Sites must already be validated for this curve scope.
    pub fn compare_sites(&self, a: &Site<C::Scalar>, b: &Site<C::Scalar>) -> Ordering {
        if a.side() != b.side() { return if a.side() == Side::Left { Ordering::Less } else { Ordering::Greater }; }
        let order = Position::of(a).compare(Position::of(b)).then_with(|| {
            fn rank<S>(site: &Site<S>) -> u8 { match site { Site::Vertex { slot: Slot::Incoming, .. } => 0, Site::Vertex { slot: Slot::Outgoing, .. } => 2, _ => 1 } }
            rank(a).cmp(&rank(b))
        });
        if a.side() == Side::Left { order } else { order.reverse() }
    }
    pub fn companion(&self, site: &Site<C::Scalar>) -> Result<Option<Site<C::Scalar>>, BoundaryError> {
        self.validate_site(site)?;
        Ok(match site {
            Site::Edge { .. } => None,
            Site::Vertex { vertex, side, slot } => Some(Site::Vertex { vertex: *vertex,
                side: if *slot == Slot::Single { side.opposite() } else { *side },
                slot: match slot { Slot::Incoming => Slot::Outgoing, Slot::Outgoing => Slot::Incoming, Slot::Single => Slot::Single },
            }),
        })
    }
    pub fn direction(&self, site: &Site<C::Scalar>) -> Result<Direction, BoundaryError> {
        self.validate_site(site)?;
        let edge = match site {
            Site::Edge { edge, .. } => *edge,
            Site::Vertex { vertex, slot, .. } => EdgeId(if *slot == Slot::Incoming || vertex.0 == self.chain.end.0 { vertex.0 - 1 } else { vertex.0 }),
        };
        let rises = self.input.edge_y_sign(edge) == Ordering::Greater;
        Ok(if rises == (site.side() == Side::Left) { Direction::Left } else { Direction::Right })
    }
    pub fn inside_null_pair(&self, site: &Site<C::Scalar>) -> Result<bool, BoundaryError> {
        self.validate_site(site)?;
        let Site::Vertex { vertex, side, .. } = site else { return Ok(false); };
        if !self.is_extremum(*vertex) { return Ok(false); }
        let turn = self.input.turn(*vertex);
        Ok(match turn { Ordering::Greater => *side == Side::Left, Ordering::Less => *side == Side::Right,
            Ordering::Equal => unreachable!("simple input excludes a collinear extremum") })
    }
    pub fn null_contact(&self, site: &Site<C::Scalar>) -> Result<Option<Site<C::Scalar>>, BoundaryError> {
        if self.inside_null_pair(site)? { self.companion(site) } else { Ok(None) }
    }
    /// Scope remapping for a join. Endpoint slots acquire the union's incidence;
    /// this does not decide whether a chord survives fusion.
    pub fn remap_site(&self, source: &Boundary<'_, C>, site: &Site<C::Scalar>) -> Result<Site<C::Scalar>, BoundaryError> {
        if !std::ptr::eq(self.input, source.input) { return Err(BoundaryError::DifferentInput); }
        source.validate_site(site)?;
        match site {
            Site::Vertex { vertex, side, slot } => {
                let mapped = if self.is_extremum(*vertex) {
                    if vertex == &source.chain.end { self.vertex_site(*vertex, *side, true) }
                    else if vertex == &source.chain.start { self.vertex_site(*vertex, *side, false) }
                    else { Site::Vertex { vertex: *vertex, side: *side, slot: *slot } }
                } else { Site::Vertex { vertex: *vertex, side: *side, slot: Slot::Single } };
                self.validate_site(&mapped)?; Ok(mapped)
            }
            Site::Edge { .. } => self.normalize_site(site),
        }
    }
    pub fn arc<'s>(&self, start: &'s Site<C::Scalar>, end: &'s Site<C::Scalar>, full_circuit: bool) -> Result<Arc<'s, C::Scalar>, BoundaryError> {
        self.validate_site(start)?; self.validate_site(end)?;
        if full_circuit && start != end { return Err(BoundaryError::InvalidFullCircuit); }
        Ok(Arc { start, end, full_circuit })
    }
    pub fn arc_weight(&self, start: &Site<C::Scalar>, end: &Site<C::Scalar>, full: bool) -> Result<usize, BoundaryError> {
        let arc = self.arc(start, end, full)?;
        Ok(self.runs(&arc).map(SideRun::weight).sum())
    }
    /// Constant-size index arithmetic; no scan over supporting input edges.
    pub fn runs<'s>(&self, arc: &Arc<'s, C::Scalar>) -> SideRuns<'s, C::Scalar> {
        let mut runs = [None; 3];
        if arc.start == arc.end && !arc.full_circuit { return SideRuns { runs, index: 0 }; }
        let side = arc.start.side(); let from = Position::of(arc.start); let to = Position::of(arc.end);
        let side_start = |s| Position::Vertex(if s == Side::Left { self.chain.start } else { self.chain.end });
        let side_end = |s| Position::Vertex(if s == Side::Left { self.chain.end } else { self.chain.start });
        if side == arc.end.side() && !arc.full_circuit && self.compare_sites(arc.start, arc.end) == Ordering::Less {
            runs[0] = Some(SideRun { side, from, to });
        } else {
            runs[0] = Some(SideRun { side, from, to: side_end(side) });
            let other = side.opposite();
            if other == arc.end.side() {
                runs[1] = Some(SideRun { side: other, from: side_start(other), to });
            } else {
                runs[1] = Some(SideRun { side: other, from: side_start(other), to: side_end(other) });
                runs[2] = Some(SideRun { side, from: side_start(side), to });
            }
        }
        SideRuns { runs, index: 0 }
    }
    pub fn contains_site(&self, arc: &Arc<'_, C::Scalar>, site: &Site<C::Scalar>) -> bool {
        if arc.full_circuit { return true; }
        if arc.start == arc.end { return false; }
        let from = self.compare_sites(arc.start, site) != Ordering::Greater;
        let to = self.compare_sites(site, arc.end) != Ordering::Greater;
        if self.compare_sites(arc.start, arc.end) == Ordering::Less { from && to } else { from || to }
    }
    fn successor(&self, site: &Site<C::Scalar>) -> Site<C::Scalar> {
        let Site::Vertex { vertex, side, slot } = site else { unreachable!("successor operates on intrinsic sites") };
        match side {
            Side::Left if *slot == Slot::Incoming => self.vertex_site(*vertex, *side, false),
            Side::Left if *vertex == self.chain.end => self.vertex_site(*vertex, Side::Right, true),
            Side::Left => self.vertex_site(VertexId(vertex.0 + 1), *side, true),
            Side::Right if *slot == Slot::Outgoing => self.vertex_site(*vertex, *side, true),
            Side::Right if *vertex == self.chain.start => self.vertex_site(*vertex, Side::Left, false),
            Side::Right => self.vertex_site(VertexId(vertex.0 - 1), *side, false),
        }
    }
    pub fn occurrences(&self) -> Occurrences<'a, C> {
        let first = self.vertex_site(self.chain.start, Side::Left, false);
        Occurrences { boundary: *self, next: Some(first.clone()), first }
    }
    pub fn arc_occurrences<'b, 's>(&'b self, arc: &'b Arc<'s, C::Scalar>) -> ArcOccurrences<'a, 'b, 's, C> {
        let first = match arc.start {
            Site::Vertex { .. } => arc.start.clone(),
            Site::Edge { edge, side, .. } => self.vertex_site(VertexId(if *side == Side::Left { edge.0 + 1 } else { edge.0 }), *side, *side == Side::Left),
        };
        let next = if self.contains_site(arc, &first) { Some(first.clone()) } else { None };
        ArcOccurrences { boundary: *self, arc, next, first }
    }
    pub fn validate_route(&self, start: &Site<C::Scalar>, end: &Site<C::Scalar>, direction: Direction, route: Route) -> Result<(), BoundaryError> {
        self.validate_site(start)?; self.validate_site(end)?;
        if start == end { return Err(BoundaryError::InvalidRoute); }
        let a = self.point(start)?; let b = self.point(end)?;
        if a.y != b.y { return Err(BoundaryError::InvalidRoute); }
        let valid = match route {
            Route::Null => self.inside_null_pair(start)? && self.companion(start)?.as_ref() == Some(end),
            Route::Finite => a.x != b.x && contact_route(&a.x, &b.x, direction) == Route::Finite,
            Route::Wrap => contact_route(&a.x, &b.x, direction) == Route::Wrap,
        };
        if valid { Ok(()) } else { Err(BoundaryError::InvalidRoute) }
    }
    pub fn contact_faces_ray(&self, site: &Site<C::Scalar>, direction: Direction) -> Result<bool, BoundaryError> {
        Ok(self.direction(site)? == direction.opposite())
    }
}

pub struct Occurrences<'a, C: Curve = Input> { boundary: Boundary<'a, C>, next: Option<Site<C::Scalar>>, first: Site<C::Scalar> }
impl<C: Curve> Iterator for Occurrences<'_, C> {
    type Item = Site<C::Scalar>;
    fn next(&mut self) -> Option<Self::Item> {
        let site = self.next.take()?;
        let successor = self.boundary.successor(&site);
        if successor != self.first { self.next = Some(successor); }
        Some(site)
    }
}
pub struct ArcOccurrences<'a, 'b, 's, C: Curve = Input> { boundary: Boundary<'a, C>, arc: &'b Arc<'s, C::Scalar>, next: Option<Site<C::Scalar>>, first: Site<C::Scalar> }
impl<C: Curve> Iterator for ArcOccurrences<'_, '_, '_, C> {
    type Item = Site<C::Scalar>;
    fn next(&mut self) -> Option<Self::Item> {
        let site = self.next.take()?;
        if !self.arc.full_circuit && &site == self.arc.end { return Some(site); }
        let successor = self.boundary.successor(&site);
        if successor != self.first && self.boundary.contains_site(self.arc, &successor) { self.next = Some(successor); }
        Some(site)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Contact<S = Rational> { pub site: Site<S>, pub x: S }

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chord<S = Rational> {
    pub start: Site<S>,
    pub end: Site<S>,
    pub direction: Direction,
    pub route: Route,
}
impl<S: Clone> Chord<S> {
    pub fn reversed(&self) -> Self {
        Self { start: self.end.clone(), end: self.start.clone(),
            direction: self.direction.opposite(), route: self.route }
    }
}

impl<'a, C: Curve> Boundary<'a, C> {
    /// All exact contacts on a clipped arc. Intrinsic occurrences are emitted
    /// first, followed by interior-edge contacts in run order. This is not a
    /// visibility decision and makes no assumption about arrival sectors.
    pub fn hits<'b, 's, 'l>(&'b self, arc: &'b Arc<'s, C::Scalar>, level: &'l C::Scalar) -> Hits<'a, 'b, 's, 'l, C> {
        Hits { boundary: *self, arc, level, occurrences: self.arc_occurrences(arc),
            runs: self.runs(arc), active_run: None, next_edge: None, seen_start: false }
    }
    /// The geometric nearest contact, with *all* tied incidences retained by a
    /// lazy second pass. The exact source identity alone is excluded. An
    /// inadmissible arrival must not be skipped to obtain a farther contact.
    /// Resolve `null_contact` before invoking this nonnull ray operation.
    pub fn nearest_contacts<'b, 's>(
        &'b self, arc: &'b Arc<'s, C::Scalar>, source: &Site<C::Scalar>, direction: Direction,
    ) -> Result<Option<NearestContacts<'a, 'b, 's, C>>, BoundaryError> {
        let point = self.point(source)?;
        let mut best: Option<C::Scalar> = None;
        for hit in self.hits(arc, &point.y) {
            if &hit.site == source { continue; }
            if best.as_ref().is_none_or(|x| ray_order(&point.x, direction, &hit.x, x) == Ordering::Less) {
                best = Some(hit.x);
            }
        }
        Ok(best.map(|x| {
            let route = contact_route(&point.x, &x, direction);
            let level = match point { Cow::Borrowed(point) => point.y.clone(), Cow::Owned(point) => point.y };
            NearestContacts { boundary: *self, arc, level, x, route,
                source: source.clone(), occurrence: self.arc_occurrences(arc),
                runs: self.runs(arc), active_run: None, next_edge: None, seen_start: false }
        }))
    }
}

pub struct Hits<'a, 'b, 's, 'l, C: Curve = Input> {
    boundary: Boundary<'a, C>,
    arc: &'b Arc<'s, C::Scalar>,
    level: &'l C::Scalar,
    occurrences: ArcOccurrences<'a, 'b, 's, C>,
    runs: SideRuns<'s, C::Scalar>,
    active_run: Option<SideRun<'s, C::Scalar>>,
    next_edge: Option<EdgeId>,
    seen_start: bool,
}

fn next_interior_hit<'s, C: Curve>(
    boundary: &Boundary<'_, C>, arc: &Arc<'_, C::Scalar>, level: &C::Scalar,
    runs: &mut SideRuns<'s, C::Scalar>, active_run: &mut Option<SideRun<'s, C::Scalar>>,
    next_edge: &mut Option<EdgeId>, seen_start: &mut bool,
) -> Option<Contact<C::Scalar>> {
    loop {
        if next_edge.is_none() {
            *active_run = runs.next();
            *next_edge = (*active_run)?.first_edge();
        }
        let run = (*active_run)?;
        let edge = next_edge.take()?;
        if Some(edge) != run.last_edge() {
            *next_edge = Some(EdgeId(if run.side == Side::Left { edge.0 + 1 } else { edge.0 - 1 }));
        }
        let Some((t, x)) = boundary.input.horizontal_hit(edge, level) else { continue; };
        // Vertices are enumerated by occurrence, not by their supporting edges.
        if t.is_zero_value() || t.compare_one() == Ordering::Equal { continue; }
        if !run.contains_parameter(edge, &t) { continue; }
        let site = Site::Edge { edge, t, side: run.side };
        if arc.full_circuit && &site == arc.start {
            if *seen_start { continue; }
            *seen_start = true;
        }
        return Some(Contact { site, x });
    }
}

impl<C: Curve> Iterator for Hits<'_, '_, '_, '_, C> {
    type Item = Contact<C::Scalar>;
    fn next(&mut self) -> Option<Self::Item> {
        for site in self.occurrences.by_ref() {
            let Site::Vertex { vertex, .. } = &site else { unreachable!() };
            let point = self.boundary.input.vertex(*vertex);
            if &point.y == self.level { return Some(Contact { site, x: point.x.clone() }); }
        }
        next_interior_hit(&self.boundary, self.arc, self.level, &mut self.runs,
            &mut self.active_run, &mut self.next_edge, &mut self.seen_start)
    }
}

/// Every item has this object's stored route, including a full wrapping return
/// at the source coordinates. No allocated contact list is required.
pub struct NearestContacts<'a, 'b, 's, C: Curve = Input> {
    boundary: Boundary<'a, C>,
    arc: &'b Arc<'s, C::Scalar>,
    level: C::Scalar,
    pub x: C::Scalar,
    pub route: Route,
    source: Site<C::Scalar>,
    occurrence: ArcOccurrences<'a, 'b, 's, C>,
    runs: SideRuns<'s, C::Scalar>,
    active_run: Option<SideRun<'s, C::Scalar>>,
    next_edge: Option<EdgeId>,
    seen_start: bool,
}
impl<C: Curve> Iterator for NearestContacts<'_, '_, '_, C> {
    type Item = Contact<C::Scalar>;
    fn next(&mut self) -> Option<Self::Item> {
        for site in self.occurrence.by_ref() {
            let Site::Vertex { vertex, .. } = &site else { unreachable!() };
            let point = self.boundary.input.vertex(*vertex);
            if point.y == self.level && point.x == self.x && site != self.source {
                return Some(Contact { site, x: point.x.clone() });
            }
        }
        loop {
            let hit = next_interior_hit(&self.boundary, self.arc, &self.level, &mut self.runs,
                &mut self.active_run, &mut self.next_edge, &mut self.seen_start)?;
            if hit.x == self.x && hit.site != self.source { return Some(hit); }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::Symbolic;

    // Deliberately neither Copy nor Clone: iterators borrow this actual curved
    // symbolic geometry rather than copying a backend or straightening its edges.
    struct SymbolicPeak {
        points: [Point<Symbolic<'static>>; 3],
    }
    impl Curve for SymbolicPeak {
        type Scalar = Symbolic<'static>;
        const MAX_LEAF_EDGES: usize = 2;
        fn len(&self) -> usize { self.points.len() }
        fn vertex(&self, vertex: VertexId) -> Cow<'_, Point<Self::Scalar>> {
            Cow::Borrowed(&self.points[vertex.0])
        }
        fn edge_y_sign(&self, edge: EdgeId) -> Ordering {
            self.points[edge.0 + 1].y.cmp(&self.points[edge.0].y)
        }
        fn turn(&self, _: VertexId) -> Ordering { Ordering::Less }
        fn horizontal_hit(&self, edge: EdgeId, level: &Self::Scalar) -> Option<(Self::Scalar, Self::Scalar)> {
            let a = &self.points[edge.0];
            let b = &self.points[edge.0 + 1];
            let t = level.minus(&a.y).over(&b.y.minus(&a.y));
            if t < Self::Scalar::zero_value() || t > Self::Scalar::one_value() { return None; }
            let x = self.edge_point(edge, &t).x;
            Some((t, x))
        }
        fn edge_point(&self, edge: EdgeId, t: &Self::Scalar) -> Point<Self::Scalar> {
            let a = &self.points[edge.0];
            let b = &self.points[edge.0 + 1];
            Point::new(a.x.plus(&t.times(t).times(&b.x.minus(&a.x))),
                a.y.plus(&t.times(&b.y.minus(&a.y))))
        }
        fn edge_tangent(&self, edge: EdgeId, t: &Self::Scalar) -> Point<Self::Scalar> {
            let a = &self.points[edge.0];
            let b = &self.points[edge.0 + 1];
            Point::new(Self::Scalar::from_usize_value(2).times(t).times(&b.x.minus(&a.x)),
                b.y.minus(&a.y))
        }
    }

    #[test]
    fn symbolic_occurrences_and_clipped_contacts_use_actual_curved_edges() {
        type S = Symbolic<'static>;
        let scalar = |n: usize| S::from_usize_value(n);
        let height = scalar(2).plus(&S::variable(0));
        let curve = SymbolicPeak { points: [
            Point::new(scalar(0), scalar(0)),
            Point::new(scalar(1), height.clone()),
            Point::new(scalar(2), scalar(1).negative()),
        ] };
        let boundary = Boundary::new(&curve, Chain::new(&curve, VertexId(0), VertexId(2)).unwrap()).unwrap();
        let vertex = |index, side, slot| Site::<S>::Vertex { vertex: VertexId(index), side, slot };
        let incoming = vertex(1, Side::Left, Slot::Incoming);
        let outgoing = vertex(1, Side::Left, Slot::Outgoing);
        assert_eq!(boundary.occurrences().count(), 8);
        assert_eq!(boundary.direction(&incoming).unwrap(), Direction::Left);
        assert_eq!(boundary.direction(&outgoing).unwrap(), Direction::Right);
        let inside = vertex(1, Side::Right, Slot::Incoming);
        assert_eq!(boundary.null_contact(&inside).unwrap(), Some(vertex(1, Side::Right, Slot::Outgoing)));
        assert!(matches!(boundary.point(&incoming).unwrap(), Cow::Borrowed(_)));

        let edge_site = |n, d| Site::Edge { edge: EdgeId(1), t: scalar(n).over(&scalar(d)), side: Side::Left };
        let start = edge_site(1, 4);
        let end = edge_site(1, 2);
        let arc = boundary.arc(&start, &end, false).unwrap();
        let contact = edge_site(3, 8);
        let point = boundary.point(&contact).unwrap();
        assert!(matches!(&point, Cow::Owned(_)));
        assert_eq!(point.x, scalar(73).over(&scalar(64)));
        assert_eq!(point.y, height.times(&scalar(5).over(&scalar(8))).minus(&scalar(3).over(&scalar(8))));
        assert_eq!(boundary.hits(&arc, &point.y).collect::<Vec<_>>(),
            vec![Contact { site: contact.clone(), x: point.x.clone() }]);
        let excluded = boundary.point(&edge_site(3, 4)).unwrap();
        assert_eq!(boundary.hits(&arc, &excluded.y).count(), 0);
        assert_eq!(boundary.runs(&arc).map(SideRun::weight).sum::<usize>(), 1);
        assert_eq!(boundary.runs(&arc).next().unwrap().clipped_interval(EdgeId(1)),
            Some((scalar(1).over(&scalar(4)), scalar(1).over(&scalar(2)))));

        let full = boundary.arc(&contact, &contact, true).unwrap();
        assert_eq!(boundary.hits(&full, &point.y).filter(|hit| hit.site == contact).count(), 1);
        let right_start = vertex(2, Side::Right, Slot::Single);
        let right_end = vertex(1, Side::Right, Slot::Outgoing);
        let right = boundary.arc(&right_start, &right_end, false).unwrap();
        let nearest = boundary.nearest_contacts(&right, &contact, Direction::Right).unwrap().unwrap();
        assert_eq!(nearest.route, Route::Wrap);
        assert_eq!(nearest.map(|hit| hit.site).collect::<Vec<_>>(),
            vec![Site::Edge { edge: EdgeId(1), t: scalar(3).over(&scalar(8)), side: Side::Right }]);
    }

    fn v(index: usize, side: Side, slot: Slot) -> Site {
        Site::Vertex { vertex: VertexId(index), side, slot }
    }
    fn e(index: usize, numerator: i64, denominator: i64, side: Side) -> Site {
        Site::Edge { edge: EdgeId(index), t: Rational::new(numerator.into(), denominator.into()), side }
    }
    fn peak() -> Input {
        Input::open(&[Point::integer(0,0), Point::integer(1,2), Point::integer(2,0)]).unwrap()
    }
    fn whole(input: &Input) -> Boundary<'_> {
        Boundary::new(input, Chain::new(input, VertexId(0), VertexId(input.len()-1)).unwrap()).unwrap()
    }

    #[test]
    fn extrema_have_same_side_companions_and_incident_directions() {
        let input = peak(); let boundary = whole(&input);
        let occurrences: Vec<_> = boundary.occurrences().collect();
        assert_eq!(occurrences, vec![
            v(0,Side::Left,Slot::Single), v(1,Side::Left,Slot::Incoming),
            v(1,Side::Left,Slot::Outgoing), v(2,Side::Left,Slot::Single),
            v(2,Side::Right,Slot::Single), v(1,Side::Right,Slot::Outgoing),
            v(1,Side::Right,Slot::Incoming), v(0,Side::Right,Slot::Single),
        ]);
        for site in &occurrences {
            let companion = boundary.companion(site).unwrap().unwrap();
            assert_eq!(boundary.companion(&companion).unwrap().as_ref(), Some(site));
            assert_ne!(&companion, site);
        }
        assert_eq!(boundary.direction(&v(1,Side::Left,Slot::Incoming)).unwrap(), Direction::Left);
        assert_eq!(boundary.direction(&v(1,Side::Left,Slot::Outgoing)).unwrap(), Direction::Right);
        assert!(boundary.inside_null_pair(&v(1,Side::Right,Slot::Incoming)).unwrap());
        assert!(!boundary.inside_null_pair(&v(1,Side::Left,Slot::Incoming)).unwrap());
        assert_eq!(boundary.normalize_site(&e(0,1,1,Side::Left)).unwrap(), v(1,Side::Left,Slot::Incoming));
        assert_eq!(boundary.normalize_site(&e(1,0,1,Side::Left)).unwrap(), v(1,Side::Left,Slot::Outgoing));
        assert_eq!(boundary.normalize_site(&e(0,0,1,Side::Right)).unwrap(), v(0,Side::Right,Slot::Single));
    }

    #[test]
    fn ordinary_collinear_contacts_are_not_emitted_per_supporting_edge() {
        let input = Input::open(&[Point::integer(0,0),Point::integer(1,2),Point::integer(2,4)]).unwrap();
        let boundary = whole(&input);
        assert_eq!(boundary.occurrences().count(), 6);
        let anchor = v(0,Side::Left,Slot::Single);
        let arc = boundary.arc(&anchor,&anchor,true).unwrap();
        let contacts: Vec<_> = boundary.hits(&arc,&input.vertex(VertexId(1)).y).map(|hit| hit.site).collect();
        assert_eq!(contacts, vec![v(1,Side::Left,Slot::Single),v(1,Side::Right,Slot::Single)]);
        assert!(!boundary.inside_null_pair(&contacts[0]).unwrap());
    }

    #[test]
    fn reversing_exchanges_sides_and_incidence_slots() {
        let input = peak(); let forward = whole(&input);
        let reverse_input = Input::open(&[Point::integer(2,0),Point::integer(1,2),Point::integer(0,0)]).unwrap();
        let reverse = whole(&reverse_input);
        for (side, slot) in [(Side::Left,Slot::Incoming),(Side::Left,Slot::Outgoing),(Side::Right,Slot::Incoming),(Side::Right,Slot::Outgoing)] {
            let reversed_slot = if slot == Slot::Incoming { Slot::Outgoing } else { Slot::Incoming };
            let a = v(1,side,slot); let b = v(1,side.opposite(),reversed_slot);
            assert_eq!(forward.direction(&a).unwrap(),reverse.direction(&b).unwrap());
            assert_eq!(forward.inside_null_pair(&a).unwrap(),reverse.inside_null_pair(&b).unwrap());
        }
    }

    #[test]
    fn join_reclassifies_endpoint_singletons_without_changing_input() {
        let input = peak(); let union = whole(&input);
        let a = Boundary::new(&input,Chain::new(&input,VertexId(0),VertexId(1)).unwrap()).unwrap();
        let b = Boundary::new(&input,Chain::new(&input,VertexId(1),VertexId(2)).unwrap()).unwrap();
        for side in [Side::Left,Side::Right] {
            let singleton = v(1,side,Slot::Single);
            assert_eq!(union.remap_site(&a,&singleton).unwrap(),v(1,side,Slot::Incoming));
            assert_eq!(union.remap_site(&b,&singleton).unwrap(),v(1,side,Slot::Outgoing));
            assert!(a.validate_site(&singleton).is_ok());
        }
        let monotone = Input::open(&[Point::integer(0,0),Point::integer(1,1),Point::integer(2,2)]).unwrap();
        let union = whole(&monotone);
        let a = Boundary::new(&monotone,Chain::new(&monotone,VertexId(0),VertexId(1)).unwrap()).unwrap();
        assert_eq!(union.remap_site(&a,&v(1,Side::Left,Slot::Single)).unwrap(),v(1,Side::Left,Slot::Single));
    }

    #[test]
    fn three_run_arcs_count_positive_pieces_and_both_caps() {
        let input = peak(); let boundary = whole(&input);
        let a = e(1,1,2,Side::Left); let b = e(0,1,2,Side::Left);
        let arc = boundary.arc(&a,&b,false).unwrap();
        assert_eq!(boundary.runs(&arc).map(|run|run.weight()).collect::<Vec<_>>(),vec![1,2,1]);
        assert_eq!(boundary.arc_weight(&a,&b,false).unwrap(),4);
        assert_eq!(boundary.arc_weight(&a,&a,true).unwrap(),5);
        assert_eq!(boundary.arc_weight(&a,&a,false).unwrap(),0);
        let anchor = v(0,Side::Left,Slot::Single);
        assert_eq!(boundary.arc_weight(&anchor,&anchor,true).unwrap(),4);
        assert_eq!(boundary.arc_weight(&v(1,Side::Right,Slot::Outgoing),&v(1,Side::Right,Slot::Incoming),false).unwrap(),0);
        assert_eq!(boundary.arc_weight(&v(2,Side::Left,Slot::Single),&v(2,Side::Right,Slot::Single),false).unwrap(),0);
        // Removing a retained cut rejoins two pieces of the same edge; old
        // weights cannot simply be added to obtain the contracted weight.
        let start = v(0,Side::Left,Slot::Single); let cut = e(0,1,2,Side::Left);
        let end = v(1,Side::Left,Slot::Incoming);
        assert_eq!(boundary.arc_weight(&start,&cut,false).unwrap()+boundary.arc_weight(&cut,&end,false).unwrap(),2);
        assert_eq!(boundary.arc_weight(&start,&end,false).unwrap(),1);
    }

    #[test]
    fn clipped_hits_and_coincident_routes_retain_identity() {
        let input = peak(); let boundary = whole(&input);
        let start = e(1,1,4,Side::Left); let end = e(1,1,2,Side::Left);
        let arc = boundary.arc(&start,&end,false).unwrap();
        let inside = e(1,3,8,Side::Left); let outside = e(1,3,4,Side::Left);
        let inside_point = boundary.point(&inside).unwrap(); let outside_point = boundary.point(&outside).unwrap();
        assert_eq!(boundary.hits(&arc,&inside_point.y).map(|hit|hit.site).collect::<Vec<_>>(),vec![inside]);
        assert_eq!(boundary.hits(&arc,&outside_point.y).count(),0);
        let incoming = v(1,Side::Right,Slot::Incoming); let outgoing = v(1,Side::Right,Slot::Outgoing);
        assert!(boundary.validate_route(&incoming,&outgoing,Direction::Right,Route::Null).is_ok());
        assert!(boundary.validate_route(&incoming,&outgoing,Direction::Right,Route::Finite).is_err());
        let chord = Chord { start: incoming, end: outgoing, direction: Direction::Right, route: Route::Null };
        let reversed = chord.reversed();
        assert!(boundary.validate_route(&reversed.start,&reversed.end,reversed.direction,reversed.route).is_ok());
        let anchor = v(0,Side::Left,Slot::Single);
        let full = boundary.arc(&anchor,&anchor,true).unwrap();
        let source = v(1,Side::Left,Slot::Incoming);
        let contacts = boundary.nearest_contacts(&full,&source,Direction::Right).unwrap().unwrap();
        assert_eq!(contacts.route,Route::Wrap);
        assert_eq!(contacts.count(),3);
        let null_arc = boundary.arc(&chord.end,&chord.start,false).unwrap();
        assert_eq!(boundary.hits(&null_arc,&input.vertex(VertexId(1)).y).count(),2);
        let interior_anchor = e(0,1,2,Side::Left);
        let full = boundary.arc(&interior_anchor,&interior_anchor,true).unwrap();
        let point = boundary.point(&interior_anchor).unwrap();
        assert_eq!(boundary.hits(&full,&point.y).filter(|hit|hit.site==interior_anchor).count(),1);
    }
    #[test]
    fn minimum_null_sector_and_chord_route_reversal() {
        let trough = Input::open(&[Point::integer(0,2),Point::integer(1,0),Point::integer(2,2)]).unwrap();
        let boundary = whole(&trough);
        assert!(boundary.inside_null_pair(&v(1,Side::Left,Slot::Incoming)).unwrap());
        assert!(!boundary.inside_null_pair(&v(1,Side::Right,Slot::Incoming)).unwrap());
        assert_eq!(boundary.direction(&v(1,Side::Left,Slot::Incoming)).unwrap(),Direction::Right);
        assert_eq!(boundary.direction(&v(1,Side::Left,Slot::Outgoing)).unwrap(),Direction::Left);
        let input = peak(); let boundary = whole(&input);
        let a = e(0,1,2,Side::Right); let b = e(1,7,10,Side::Right);
        for (direction,route) in [(Direction::Right,Route::Finite),(Direction::Left,Route::Wrap)] {
            let chord = Chord { start:a.clone(),end:b.clone(),direction,route };
            assert!(boundary.validate_route(&chord.start,&chord.end,chord.direction,chord.route).is_ok());
            let reversed = chord.reversed();
            assert_eq!(reversed.route,route);
            assert!(boundary.validate_route(&reversed.start,&reversed.end,reversed.direction,reversed.route).is_ok());
        }
    }
}
