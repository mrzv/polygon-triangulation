//! Directed, constant-description ribbons of actual old region face words.
//!
//! Only the selected Left boundary is a quotient of the old region.  Long
//! original branches are lazy offset aliases; diamonds, exit bridges and the
//! helper puncture have bounded descriptions independent of Root length.
use crate::boundary::{Boundary, BoundaryError, Chain, Position, Side, Site, Slot};
use crate::curve::{Curve, LevelSource};
use crate::geometry::{Direction, Point, Rational, Route};
use crate::input::{EdgeId, Input, VertexId};
use crate::program::{Piece, Programme, ProgrammeError};
use crate::scalar::ExactScalar;
use crate::submap::{ArcId, MapError, RegionId, Submap, VisibleChord};
use crate::symbolic::{LimitError, Symbolic};
use crate::view::OffsetView;
use crate::work::Work;
use std::cmp::Ordering;
use std::fmt;

const MAX_DESCRIPTORS: usize = 512;
const MAX_STARS: usize = 10;

#[derive(Debug)]
pub enum RibbonError {
    Boundary(BoundaryError),
    Map(MapError),
    Programme(ProgrammeError),
    Limit(LimitError),
    InvalidFaceWord,
    NonconformalRegion,
    EmptyRegion,
    FrozenProductionSource,
    InvalidSource,
    InvalidStarIncidence,
    InvalidPort,
    InterleavingSectors,
    CoincidentPorts,
    DescriptorBound,
    OutsideProgramme,
    ProjectionOutsideArc,
    SeamAtVertexLevel,
}
impl fmt::Display for RibbonError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for RibbonError {}
impl From<BoundaryError> for RibbonError {
    fn from(error: BoundaryError) -> Self { Self::Boundary(error) }
}
impl From<MapError> for RibbonError {
    fn from(error: MapError) -> Self { Self::Map(error) }
}
impl From<ProgrammeError> for RibbonError {
    fn from(error: ProgrammeError) -> Self { Self::Programme(error) }
}
impl From<LimitError> for RibbonError {
    fn from(error: LimitError) -> Self { Self::Limit(error) }
}

pub struct ProjectedCut {
    pub site: Site,
    pub arc: ArcId,
}

pub struct Ribbon<'a> {
    pub programme: Programme<'a>,
    pub root_chain: Chain,
    pub region: RegionId,
    pub protected: Vec<VisibleChord>,
    pub star_flags: Vec<Site>,
    pub exceptional: Vec<Point>,
    root: &'a Input,
    tags: Vec<Tag>,
    arcs: Vec<OldArc>,
}

#[derive(Clone)]
enum Tag {
    Original { arc: ArcId, side: Side, start_source: VertexId, end_source: VertexId },
    Helper { source: VertexId },
}
struct OldArc { id: ArcId, start: Site, end: Site, full: bool }
#[derive(Clone, Debug)]
enum At { Vertex(VertexId), Edge(EdgeId, Rational) }
impl At {
    fn of(position: Position<'_>) -> Self {
        match position { Position::Vertex(v) => Self::Vertex(v), Position::Edge { edge, t } => Self::Edge(edge, t.clone()) }
    }
    fn site(site: &Site) -> Self {
        match site { Site::Vertex { vertex, .. } => Self::Vertex(*vertex), Site::Edge { edge, t, .. } => Self::Edge(*edge, t.clone()) }
    }
    fn compare(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Vertex(a), Self::Vertex(b)) => a.cmp(b),
            (Self::Vertex(a), Self::Edge(b, _)) => if a.0 <= b.0 { Ordering::Less } else { Ordering::Greater },
            (Self::Edge(a, _), Self::Vertex(b)) => if a.0 < b.0 { Ordering::Less } else { Ordering::Greater },
            (Self::Edge(a, at), Self::Edge(b, bt)) => a.cmp(b).then_with(|| at.cmp(bt)),
        }
    }
    fn departing(&self, reverse: bool) -> EdgeId {
        match self {
            Self::Vertex(v) if reverse => EdgeId(v.0 - 1),
            Self::Vertex(v) => EdgeId(v.0),
            Self::Edge(e, _) => *e,
        }
    }
    fn arriving(&self, reverse: bool) -> EdgeId { self.departing(!reverse) }
}
struct Star { point: Point, at: At, source: VertexId }
#[derive(Clone)]
struct Port<'a> { star: usize, point: Point<Symbolic<'a>>, angle: Symbolic<'a> }
struct Branch<'a> { pieces: Vec<(Piece<'a>, Tag)>, start: Port<'a>, end: Port<'a> }
struct Collar<'a> { start: Port<'a>, end: Port<'a>, depth: usize }

fn scalar<'a>(value: &Rational) -> Symbolic<'a> { Symbolic::owned(value.clone()) }
fn constant<'a>(n: usize) -> Symbolic<'a> { Symbolic::from_usize_value(n) }
fn interpolate<'a>(a: &Point<Symbolic<'a>>, b: &Point<Symbolic<'a>>, t: &Symbolic<'a>) -> Point<Symbolic<'a>> {
    Point::new(a.x.plus(&t.times(&b.x.minus(&a.x))), a.y.plus(&t.times(&b.y.minus(&a.y))))
}
fn shear<'a>(p: &Point<Symbolic<'a>>) -> Point<Symbolic<'a>> {
    Point::new(p.x.clone(), p.y.plus(&Symbolic::variable(32).times(&p.x)))
}
fn compact<'a>(x: &Symbolic<'a>) -> Symbolic<'a> { x.over(&Symbolic::one_value().plus(&x.absolute())) }
fn chart<'a>(p: &Point<Symbolic<'a>>) -> Point<Symbolic<'a>> { Point::new(compact(&p.x), p.y.clone()) }
fn cw_span<'a>(a: &Symbolic<'a>, b: &Symbolic<'a>) -> Symbolic<'a> {
    let d = b.minus(a);
    if d.sign() == Ordering::Greater { d } else { d.plus(&constant(4)) }
}
fn offset<'a>(a: &Symbolic<'a>, b: &Symbolic<'a>) -> Symbolic<'a> {
    let d = b.minus(a);
    if d.sign() == Ordering::Less { d.plus(&constant(4)) } else { d }
}

/// The chart is clockwise: top, right, bottom, left.  The port is the
/// outward intersection of an ACTUAL shifted support, not a slid nominal t.
fn port<'a>(star: usize, centre: &Point, a: &Point<Symbolic<'a>>, b: &Point<Symbolic<'a>>,
    germ: &Point, work: &mut Work) -> Result<(Port<'a>, Symbolic<'a>), RibbonError>
{
    let rho = Symbolic::variable(0);
    let cx = scalar(&centre.x);
    let cy = scalar(&centre.y);
    let dx = b.x.minus(&a.x);
    let dy = b.y.minus(&a.y);
    for (sx, sy) in [(true, true), (true, false), (false, false), (false, true)] {
        work.predicates += 1;
        let signed = |v: &Symbolic<'a>, positive| if positive { v.clone() } else { v.negative() };
        let denominator = signed(&dx, sx).plus(&signed(&dy, sy));
        if denominator.is_zero_value() { continue; }
        let numerator = rho.minus(&signed(&a.x.minus(&cx), sx)).minus(&signed(&a.y.minus(&cy), sy));
        let t = numerator.over(&denominator);
        let p = interpolate(a, b, &t);
        let x = p.x.minus(&cx);
        let y = p.y.minus(&cy);
        if signed(&x, sx).sign() == Ordering::Less || signed(&y, sy).sign() == Ordering::Less { continue; }
        if x.times(&scalar(&germ.x)).plus(&y.times(&scalar(&germ.y))).sign() != Ordering::Greater { continue; }
        let mut angle = match (sx, sy) {
            (true, true) => x.over(&rho),
            (true, false) => constant(1).minus(&y.over(&rho)),
            (false, false) => constant(2).minus(&x.over(&rho)),
            (false, true) => constant(3).plus(&y.over(&rho)),
        };
        if angle == constant(4) { angle = Symbolic::zero_value(); }
        // An axis belongs to two diamond charts, but both solve the same
        // support incidence; returning the first does not perturb its role.
        if angle >= Symbolic::zero_value() && angle < constant(4) {
            return Ok((Port { star, point: p, angle }, t));
        }
    }
    Err(RibbonError::InvalidPort)
}

fn add_star(stars: &mut Vec<Star>, boundary: Boundary<'_>, site: &Site, source: VertexId) -> Result<usize, RibbonError> {
    let point = boundary.point(site)?.into_owned();
    if boundary.input().vertex(source).y != point.y { return Err(RibbonError::InvalidSource); }
    if let Some(i) = stars.iter().position(|s| s.point == point) {
        // Distinct Root occurrences at the same physical star are never
        // deduplicated here: this table groups only physical geometry.
        if stars[i].source != source || stars[i].at.compare(&At::site(site)) != Ordering::Equal {
            return Err(RibbonError::InvalidStarIncidence);
        }
        return Ok(i);
    }
    if stars.len() == MAX_STARS { return Err(RibbonError::DescriptorBound); }
    stars.push(Star { point, at: At::site(site), source });
    Ok(stars.len() - 1)
}
fn star_index(stars: &[Star], at: &At) -> Result<usize, RibbonError> {
    stars.iter().position(|s| s.at.compare(at) == Ordering::Equal).ok_or(RibbonError::InvalidStarIncidence)
}
fn root_germ(input: &Input, edge: EdgeId, reverse: bool) -> Point {
    let a = input.vertex(VertexId(edge.0));
    let b = input.vertex(VertexId(edge.0 + 1));
    let d = Point::new(b.x.minus(&a.x), b.y.minus(&a.y));
    if reverse { Point::new(d.x.negative(), d.y.negative()) } else { d }
}

fn alias_port<'a>(star: usize, centre: &Point, view: &OffsetView<'a>, edge: EdgeId,
    reverse_germ: bool, work: &mut Work) -> Result<(Port<'a>, Symbolic<'a>), RibbonError>
{
    // Locate the diamond port on the rational Root SUPPORT. Miter endpoint
    // differences are used only afterwards for the view's canonical clip t;
    // they must not infect the sparse finite collar geometry.
    let d = root_germ(view.input(), edge, false);
    let norm = d.x.absolute().plus(&d.y.absolute());
    let a = Point::new(scalar(&centre.x).plus(&view.width().times(&scalar(&d.y.negative().over(&norm)))),
        scalar(&centre.y).plus(&view.width().times(&scalar(&d.x.over(&norm)))));
    let b = Point::new(a.x.plus(&scalar(&d.x)), a.y.plus(&scalar(&d.y)));
    let germ = if reverse_germ { Point::new(d.x.negative(), d.y.negative()) } else { d };
    let (port, _) = port(star, centre, &a, &b, &germ, work)?;
    let first = view.raw_vertex(VertexId(edge.0));
    let last = view.raw_vertex(VertexId(edge.0 + 1));
    let t = port.point.y.minus(&first.y).over(&last.y.minus(&first.y));
    Ok((port, t))
}

impl<'a> Ribbon<'a> {
    pub fn root_input(&self) -> &'a Input { self.root }

    pub fn compile(old: &Submap<'a>, region: RegionId, work: &mut Work) -> Result<Self, RibbonError> {
        let root = old.input();
        let root_chain = old.chain();
        let boundary = Boundary::new(root, root_chain)?;
        let ids = old.region_arcs(region)?;
        let exits = old.region_exits(region)?;
        if exits.len() > 4 || ids.is_empty() || ids.len() > 4 { return Err(RibbonError::NonconformalRegion); }
        let mut protected = Vec::with_capacity(exits.len());
        let mut stars = Vec::with_capacity(MAX_STARS);
        let mut exceptional = Vec::with_capacity(MAX_STARS + 4);
        for &exit in exits {
            let (sites, route) = old.chord(exit)?;
            let source = match old.chord_level(exit)? {
                LevelSource::Vertex(q) if q.0 < root.len() => *q,
                LevelSource::Vertex(_) => return Err(RibbonError::InvalidSource),
                LevelSource::Frozen(_) => return Err(RibbonError::FrozenProductionSource),
            };
            boundary.validate_route(sites[0], sites[1], boundary.direction(sites[0])?, route)?;
            for site in sites { add_star(&mut stars, boundary, site, source)?; }
            let point = root.vertex(source).clone();
            if !exceptional.contains(&point) { exceptional.push(point); }
            protected.push(VisibleChord { endpoints: sites.map(Clone::clone), route, level: LevelSource::Vertex(source) });
        }
        // Caps are physical stars even when they are not protected exits.
        // Membership below decides which occurrences actually face this R.
        for vertex in [root_chain.start, root_chain.end] {
            add_star(&mut stars, boundary, &Site::Vertex { vertex, side: Side::Left, slot: Slot::Single }, vertex)?;
        }
        let mut arcs = Vec::with_capacity(ids.len());
        let first = ids[0];
        let mut current = first;
        loop {
            if old.arc_region(current)? != region || arcs.iter().any(|a: &OldArc| a.id == current) {
                return Err(RibbonError::InvalidFaceWord);
            }
            let (start, end, full) = match old.arc_sites(current) {
                Some((a, b, full)) => (a.clone(), b.clone(), full),
                None if ids.len() == 1 && exits.is_empty() => {
                    let cap = Site::Vertex { vertex: root_chain.start, side: Side::Left, slot: Slot::Single };
                    (cap.clone(), cap, true)
                }
                None => return Err(RibbonError::InvalidFaceWord),
            };
            arcs.push(OldArc { id: current, start, end, full });
            current = old.arc_successor(current)?;
            if current == first { break; }
            if arcs.len() >= ids.len() { return Err(RibbonError::InvalidFaceWord); }
        }
        if arcs.len() != ids.len() { return Err(RibbonError::InvalidFaceWord); }
        let mut star_flags = Vec::with_capacity(8 * stars.len());
        for star in &stars {
            if !exceptional.contains(&star.point) { exceptional.push(star.point.clone()); }
            let mut candidates = Vec::with_capacity(4);
            for side in [Side::Left, Side::Right] {
                match &star.at {
                    At::Vertex(vertex) if boundary.is_extremum(*vertex) => {
                        for slot in [Slot::Incoming, Slot::Outgoing] { candidates.push(Site::Vertex { vertex: *vertex, side, slot }); }
                    }
                    At::Vertex(vertex) => candidates.push(Site::Vertex { vertex: *vertex, side, slot: Slot::Single }),
                    At::Edge(edge, t) => candidates.push(Site::Edge { edge: *edge, t: t.clone(), side }),
                }
            }
            for site in candidates {
                work.predicates += 1;
                // Zero arcs still own their exact transition endpoints.
                if arcs.iter().any(|a| a.start == site || a.end == site || boundary.contains_site(&boundary.arc(&a.start, &a.end, a.full).unwrap(), &site)) {
                    star_flags.push(site);
                }
            }
        }
        let mut views = Vec::with_capacity(12);
        let mut branches = Vec::new();
        for arc in &arcs {
            let root_arc = boundary.arc(&arc.start, &arc.end, arc.full)?;
            for run in boundary.runs(&root_arc) {
                if run.weight() == 0 { continue; }
                if views.len() == 12 { return Err(RibbonError::DescriptorBound); }
                let reverse = run.side == Side::Right;
                let lane = Symbolic::variable(1 + views.len());
                let view = OffsetView::new(root, if reverse { lane.negative() } else { lane }, Symbolic::variable(32));
                let view_index = views.len();
                let from = At::of(run.from);
                let to = At::of(run.to);
                let (low, high) = if reverse { (&to, &from) } else { (&from, &to) };
                let mut cuts: Vec<At> = stars.iter().filter(|s| low.compare(&s.at) != Ordering::Greater && s.at.compare(high) != Ordering::Greater)
                    .map(|s| s.at.clone()).collect();
                // This sorts only the constant star packet, never Root vertices.
                cuts.sort_by(|a, b| if reverse { b.compare(a) } else { a.compare(b) });
                if cuts.first().is_none_or(|a| a.compare(&from) != Ordering::Equal)
                    || cuts.last().is_none_or(|a| a.compare(&to) != Ordering::Equal) { return Err(RibbonError::InvalidStarIncidence); }
                for pair in cuts.windows(2) {
                    if pair[0].compare(&pair[1]) == Ordering::Equal { continue; }
                    let start_star = star_index(&stars, &pair[0])?;
                    let end_star = star_index(&stars, &pair[1])?;
                    let first_edge = pair[0].departing(reverse);
                    let last_edge = pair[1].arriving(reverse);
                    let (start, start_t) = alias_port(start_star, &stars[start_star].point, &view, first_edge, reverse, work)?;
                    let (end, end_t) = alias_port(end_star, &stars[end_star].point, &view, last_edge, !reverse, work)?;
                    let zero = Symbolic::zero_value();
                    let one = Symbolic::one_value();
                    if start_t < zero || start_t > one || end_t < zero || end_t > one { return Err(RibbonError::InvalidPort); }
                    branches.push(Branch { start, end, pieces: vec![(Piece::Alias {
                        view: view_index, first: first_edge, last: last_edge, start: start_t, end: end_t, reverse,
                    }, Tag::Original { arc: arc.id, side: run.side,
                        start_source: stars[start_star].source, end_source: stars[end_star].source })] });
                }
                views.push(view);
            }
            if let Some(endpoint_ids) = old.arc_endpoints(arc.id) {
                let (exit, end_slot) = endpoint_ids[1];
                let (sites, route) = old.chord(exit)?;
                if sites[end_slot] != &arc.end { return Err(RibbonError::InvalidFaceWord); }
                let next = old.arc_successor(arc.id)?;
                if arcs.iter().find(|a| a.id == next).is_none_or(|a| &a.start != sites[1 - end_slot]) {
                    return Err(RibbonError::InvalidFaceWord);
                }
                if route == Route::Null { continue; }
                let source = match old.chord_level(exit)? { LevelSource::Vertex(q) => *q, LevelSource::Frozen(_) => return Err(RibbonError::FrozenProductionSource) };
                let a = boundary.point(sites[end_slot])?.into_owned();
                let b = boundary.point(sites[1 - end_slot])?.into_owned();
                let start_star = star_index(&stars, &At::site(sites[end_slot]))?;
                let end_star = star_index(&stars, &At::site(sites[1 - end_slot]))?;
                let direction = boundary.direction(sites[end_slot])?;
                let right = direction == Direction::Right;
                let exit_index = exits.iter().position(|c| *c == exit).ok_or(RibbonError::InvalidFaceWord)?;
                let width = Symbolic::variable(13 + exit_index);
                let y = scalar(&a.y).plus(&if right { width } else { width.negative() });
                let support_a = Point::new(scalar(&a.x), y.clone());
                let support_b = Point::new(scalar(&a.x).plus(&if right { Symbolic::one_value() } else { Symbolic::one_value().negative() }), y.clone());
                let germ = Point::integer(if right { 1 } else { -1 }, 0);
                let (start, _) = port(start_star, &a, &support_a, &support_b, &germ, work)?;
                let terminal_a = Point::new(scalar(&b.x), y.clone());
                let terminal_b = Point::new(scalar(&b.x).plus(&if right { Symbolic::one_value() } else { Symbolic::one_value().negative() }), y);
                let reverse_germ = Point::new(germ.x.negative(), germ.y.negative());
                let (end, _) = port(end_star, &b, &terminal_a, &terminal_b, &reverse_germ, work)?;
                let tag = Tag::Helper { source };
                let pieces = if route == Route::Finite {
                    vec![(Piece::Finite { start: shear(&start.point), end: shear(&end.point) }, tag)]
                } else {
                    wrapping_bridge(&start.point, &end.point, direction, exit_index, source)?
                };
                branches.push(Branch { start, end, pieces });
            }
        }
        if branches.is_empty() { return Err(RibbonError::EmptyRegion); }
        let mut collars = Vec::with_capacity(branches.len());
        for i in 0..branches.len() {
            let start = branches[i].end.clone();
            let end = branches[(i + 1) % branches.len()].start.clone();
            if start.star != end.star { return Err(RibbonError::InvalidFaceWord); }
            if start.angle == end.angle { return Err(RibbonError::CoincidentPorts); }
            collars.push(Collar { start, end, depth: 0 });
        }
        nest_collars(&mut collars, work)?;
        let mut descriptors = Vec::new();
        for (branch, collar) in branches.into_iter().zip(&collars) {
            descriptors.extend(branch.pieces);
            descriptors.extend(collar_pieces(collar, &stars[collar.start.star])?);
        }
        if descriptors.len() > MAX_DESCRIPTORS { return Err(RibbonError::DescriptorBound); }
        puncture(&mut descriptors)?;
        let mut programme = Programme::new(views);
        let mut tags = Vec::with_capacity(descriptors.len());
        for (piece, tag) in descriptors { programme.append(piece)?; tags.push(tag); }
        let ribbon = Self { programme, root_chain, region, protected, star_flags, exceptional, root, tags, arcs };
        ribbon.check_seam_levels(work)?;
        Ok(ribbon)
    }

    /// Every actual Programme vertex has a known Vertex base source.  Interior
    /// alias vertices are mapped by descriptor index arithmetic, not searched.
    pub fn root_source(&self, programme_vertex: VertexId) -> Result<VertexId, RibbonError> {
        let v = programme_vertex.0;
        if v >= self.programme.len() { return Err(RibbonError::OutsideProgramme); }
        let piece_index = if v + 1 == self.programme.len() { self.programme.piece_count() - 1 }
            else { self.programme.piece_index(EdgeId(v)) };
        let (piece, chain) = self.programme.piece(piece_index);
        match &self.tags[piece_index] {
            Tag::Helper { source } => Ok(*source),
            Tag::Original { start_source, end_source, .. } => {
                if v == chain.start.0 { return Ok(*start_source); }
                if v == chain.end.0 { return Ok(*end_source); }
                let Piece::Alias { first, reverse, .. } = piece else { return Err(RibbonError::InvalidSource); };
                let offset = v - chain.start.0;
                Ok(VertexId(if *reverse { first.0 + 1 - offset } else { first.0 + offset }))
            }
        }
    }

    pub fn project_cut(&self, site: &Site<Symbolic<'a>>, work: &mut Work) -> Result<Option<ProjectedCut>, RibbonError> {
        let chain = Chain { start: VertexId(0), end: VertexId(self.programme.len() - 1) };
        let temporary = Boundary::new(&self.programme, chain)?;
        temporary.validate_site(site)?;
        if site.side() != Side::Left { return Ok(None); }
        let mut candidates = Vec::with_capacity(2);
        match site {
            Site::Edge { edge, t, .. } => candidates.push((*edge, t.clone())),
            Site::Vertex { vertex, slot, .. } => {
                // Alias-helper joins use the incident original support even
                // when the temporary extremum's other slot names the helper.
                // At a genuine alias interior turn, preserve the selected
                // incoming/outgoing incidence instead of choosing coordinates.
                let incoming = (vertex.0 > 0).then(|| EdgeId(vertex.0 - 1));
                let outgoing = (vertex.0 + 1 < self.programme.len()).then(|| EdgeId(vertex.0));
                let is_alias = |edge: Option<EdgeId>| edge.is_some_and(|e| self.programme.alias_edge(e).is_some());
                let join = is_alias(incoming) != is_alias(outgoing);
                if *slot != Slot::Outgoing || join {
                    if let Some(edge) = incoming { candidates.push((edge, Symbolic::one_value())); }
                }
                if *slot != Slot::Incoming || join {
                    if let Some(edge) = outgoing { candidates.push((edge, Symbolic::zero_value())); }
                }
            }
        }
        let boundary = Boundary::new(self.root, self.root_chain)?;
        let mut projected: Option<ProjectedCut> = None;
        for (edge, t) in candidates {
            let index = self.programme.piece_index(edge);
            let Tag::Original { arc, side, .. } = self.tags[index] else { continue; };
            let Some(alias) = self.programme.alias_edge(edge) else { return Err(RibbonError::InvalidSource); };
            let raw_t = alias.start.plus(&t.times(&alias.end.minus(&alias.start)));
            work.predicates += 1;
            let root_t = self.programme.view(alias.view).project_parameter(alias.edge, &raw_t)?;
            let root_site = boundary.normalize_site(&Site::Edge { edge: alias.edge, t: root_t, side })?;
            let owner = self.arcs.iter().find(|a| a.id == arc).ok_or(RibbonError::InvalidFaceWord)?;
            if root_site != owner.start && root_site != owner.end && !boundary.contains_site(&boundary.arc(&owner.start, &owner.end, owner.full)?, &root_site) {
                return Err(RibbonError::ProjectionOutsideArc);
            }
            if let Some(previous) = &projected {
                if previous.site != root_site || previous.arc != arc { return Err(RibbonError::InvalidStarIncidence); }
            } else { projected = Some(ProjectedCut { site: root_site, arc }); }
        }
        Ok(projected)
    }

    fn check_seam_levels(&self, work: &mut Work) -> Result<(), RibbonError> {
        for event in self.programme.cut_crossings() {
            let level = self.programme.level(&event.level);
            let source = self.root_source(VertexId(event.edge.0))?;
            for i in 0..self.programme.piece_count() {
                let (piece, chain) = self.programme.piece(i);
                for vertex in [chain.start, chain.end] {
                    work.predicates += 1;
                    if self.programme.vertex(vertex).y == *level { return Err(RibbonError::SeamAtVertexLevel); }
                }
                if let Piece::Alias { first, last, reverse, .. } = piece {
                    // Other Root vertices have distinct rational base Y.  The
                    // one possible equal-base vertex is source q, possibly
                    // remote from both old exit endpoints; check ALL copies.
                    let low = first.0.min(last.0);
                    let high = first.0.max(last.0) + 1;
                    if source.0 > low && source.0 < high {
                        let offset = if *reverse { first.0 + 1 - source.0 } else { source.0 - first.0 };
                        let vertex = VertexId(chain.start.0 + offset);
                        if vertex.0 > chain.start.0 && vertex.0 < chain.end.0 {
                            work.predicates += 1;
                            if self.programme.vertex(vertex).y == *level { return Err(RibbonError::SeamAtVertexLevel); }
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

fn wrapping_bridge<'a>(a: &Point<Symbolic<'a>>, b: &Point<Symbolic<'a>>, direction: Direction,
    index: usize, source: VertexId) -> Result<Vec<(Piece<'a>, Tag)>, RibbonError>
{
    // Finite shear is applied BEFORE compactification.  Infinity is never
    // passed to a finite X shear, including a full-circle return at one star.
    let start = chart(&shear(a));
    let end = chart(&shear(b));
    let right = direction == Direction::Right;
    let winding = if right { 1 } else { -1 };
    let unwrapped_x = if right { end.x.plus(&constant(2)) } else { end.x.minus(&constant(2)) };
    let span = unwrapped_x.minus(&start.x);
    if span.sign() != if right { Ordering::Greater } else { Ordering::Less } || span.absolute() >= constant(2) {
        return Err(RibbonError::InvalidPort);
    }
    let seam = if right { Symbolic::one_value() } else { Symbolic::one_value().negative() };
    let x = start.x.plus(&seam).over(&constant(2));
    let t = x.minus(&start.x).over(&span);
    let y = start.y.plus(&t.times(&end.y.minus(&start.y))).plus(&Symbolic::variable(96 + index));
    let auxiliary = Point::new(x, y);
    if start.y == end.y || auxiliary.y <= std::cmp::min(start.y.clone(), end.y.clone())
        || auxiliary.y >= std::cmp::max(start.y.clone(), end.y.clone()) { return Err(RibbonError::InvalidPort); }
    // The fresh variable occurs in the seam event with coefficient strictly
    // between 0 and 1, but in the auxiliary source with coefficient 1 and in
    // no finite vertex.  The event and EVERY actual source level differ.
    Ok(vec![(Piece::Projective { start, end: auxiliary.clone(), winding: 0 }, Tag::Helper { source }),
        (Piece::Projective { start: auxiliary, end, winding }, Tag::Helper { source })])
}

fn nest_collars(collars: &mut [Collar<'_>], work: &mut Work) -> Result<(), RibbonError> {
    for i in 0..collars.len() {
        let a = &collars[i];
        let length = cw_span(&a.start.angle, &a.end.angle);
        let mut depth = 0;
        for (j, b) in collars.iter().enumerate() {
            if i == j || a.start.star != b.start.star { continue; }
            work.predicates += 1;
            if a.start.angle == b.start.angle || a.start.angle == b.end.angle || a.end.angle == b.start.angle || a.end.angle == b.end.angle {
                return Err(RibbonError::CoincidentPorts);
            }
            let other_length = cw_span(&b.start.angle, &b.end.angle);
            let b0 = offset(&a.start.angle, &b.start.angle);
            let b1 = b0.plus(&other_length);
            let a0 = offset(&b.start.angle, &a.start.angle);
            let a1 = a0.plus(&length);
            let contains_b = b0 > Symbolic::zero_value() && b1 < length;
            let contains_a = a0 > Symbolic::zero_value() && a1 < other_length;
            if contains_a { depth += 1; }
            if contains_a || contains_b { continue; }
            // Test both lifts of the other circular interval.  Partial
            // overlap is interleaving, including two almost-full intervals.
            for lift in [b0.clone(), b0.minus(&constant(4))] {
                let end = lift.plus(&other_length);
                if lift < length && end > Symbolic::zero_value() { return Err(RibbonError::InterleavingSectors); }
            }
        }
        if depth >= 32 { return Err(RibbonError::DescriptorBound); }
        collars[i].depth = depth;
    }
    Ok(())
}

fn collar_pieces<'a>(collar: &Collar<'a>, star: &Star) -> Result<Vec<(Piece<'a>, Tag)>, RibbonError> {
    let rho = Symbolic::variable(0);
    // A containing interval has smaller nesting depth and hence GREATER
    // inward height.  Disjoint equal-depth intervals need no artificial tie.
    let height = Symbolic::variable(64 + collar.depth);
    let radius = rho.minus(&height);
    let scale = radius.over(&rho);
    let centre = Point::new(scalar(&star.point.x), scalar(&star.point.y));
    let inward = |p: &Point<Symbolic<'a>>| Point::new(centre.x.plus(&scale.times(&p.x.minus(&centre.x))),
        centre.y.plus(&scale.times(&p.y.minus(&centre.y))));
    let start = inward(&collar.start.point);
    let end = inward(&collar.end.point);
    let length = cw_span(&collar.start.angle, &collar.end.angle);
    let mut corners = Vec::with_capacity(4);
    for corner in 0..4 {
        let distance = offset(&collar.start.angle, &constant(corner));
        if distance > Symbolic::zero_value() && distance < length { corners.push((distance, corner)); }
    }
    corners.sort_by(|a, b| a.0.cmp(&b.0));
    let mut points = Vec::with_capacity(8);
    points.push(collar.start.point.clone());
    points.push(start);
    for (_, corner) in corners {
        let p = match corner {
            0 => Point::new(centre.x.clone(), centre.y.plus(&radius)),
            1 => Point::new(centre.x.plus(&radius), centre.y.clone()),
            2 => Point::new(centre.x.clone(), centre.y.minus(&radius)),
            _ => Point::new(centre.x.minus(&radius), centre.y.clone()),
        };
        points.push(p);
    }
    points.push(end);
    points.push(collar.end.point.clone());
    let mut pieces = Vec::with_capacity(points.len() - 1);
    for pair in points.windows(2) {
        if pair[0] == pair[1] { continue; }
        pieces.push((Piece::Finite { start: shear(&pair[0]), end: shear(&pair[1]) }, Tag::Helper { source: star.source }));
    }
    Ok(pieces)
}

fn puncture<'a>(descriptors: &mut Vec<(Piece<'a>, Tag)>) -> Result<(), RibbonError> {
    let i = descriptors.iter().position(|(piece, tag)| matches!(piece, Piece::Finite { .. }) && matches!(tag, Tag::Helper { .. }))
        .ok_or(RibbonError::InvalidFaceWord)?;
    let (Piece::Finite { start, end }, tag) = &descriptors[i] else { return Err(RibbonError::InvalidFaceWord); };
    let half = Symbolic::one_value().over(&constant(2));
    let epsilon = Symbolic::variable(112);
    let before = interpolate(start, end, &half.minus(&epsilon));
    let after = interpolate(start, end, &half.plus(&epsilon));
    let first = (Piece::Finite { start: after, end: end.clone() }, tag.clone());
    let last = (Piece::Finite { start: start.clone(), end: before }, tag.clone());
    descriptors.rotate_left(i + 1);
    descriptors.pop();
    descriptors.insert(0, first);
    descriptors.push(last);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hierarchy::{Catalogue, MergeEngine};
    use crate::input::VertexSource;
    use crate::merge::OriginalMerge;

    fn whole(input: &Input) -> Boundary<'_> {
        Boundary::new(input, Chain { start: VertexId(0), end: VertexId(input.len() - 1) }).unwrap()
    }
    fn uncompact<'a>(x: &Symbolic<'a>) -> Symbolic<'a> {
        x.over(&Symbolic::one_value().minus(&x.absolute()))
    }

    // Actual edge graphs in a chart are fractional linear in Y.  Splitting
    // finite X=0 and real projective seam events lets this checker detect
    // ALL intersections, including a tangency missed by endpoint order tests.
    struct Graph<'a> {
        edge: EdgeId,
        projective: bool,
        low: Symbolic<'a>,
        high: Symbolic<'a>,
        x_low: Symbolic<'a>,
        x_high: Symbolic<'a>,
        raw_x_low: Symbolic<'a>,
        raw_x_high: Symbolic<'a>,
        n: [Symbolic<'a>; 2],
        d: [Symbolic<'a>; 2],
        raw_d: Symbolic<'a>,
    }
    fn graphs<'a>(p: &Programme<'a>) -> Vec<Graph<'a>> {
        let mut graphs = Vec::new();
        for i in 0..p.edge_count() {
            let edge = EdgeId(i);
            let a = p.edge_point(edge, &Symbolic::zero_value());
            let b = p.edge_point(edge, &Symbolic::one_value());
            let (piece, _) = p.piece(p.piece_index(edge));
            let projective = matches!(piece, Piece::Projective { .. });
            let mut points = vec![a.clone(), b.clone()];
            if projective {
                if let Some(event) = p.cut_crossings().iter().find(|event| event.edge == edge) {
                    let y = p.level(&event.level).into_owned();
                    let x = if event.forward == Ordering::Greater { Symbolic::one_value() } else { Symbolic::one_value().negative() };
                    points = vec![a, Point::new(x.clone(), y.clone()), Point::new(x.negative(), y), b];
                }
            } else {
                points[0].x = uncompact(&points[0].x);
                points[1].x = uncompact(&points[1].x);
                if points[0].x.sign() != points[1].x.sign()
                    && !points[0].x.is_zero_value() && !points[1].x.is_zero_value()
                {
                    let t = points[0].x.negative().over(&points[1].x.minus(&points[0].x));
                    let q = interpolate(&points[0], &points[1], &t);
                    points.insert(1, q);
                }
            }
            for pair in points.windows(2) {
                if pair[0].y == pair[1].y { continue; } // two charts of ONE seam incidence
                // Homogeneous line coefficients avoid dividing by a symbolic
                // delta-Y before every subsequent intersection comparison.
                let dx = pair[1].x.minus(&pair[0].x);
                let dy = pair[1].y.minus(&pair[0].y);
                let intercept = pair[0].x.times(&dy).minus(&dx.times(&pair[0].y));
                let sign = pair[0].x.plus(&pair[1].x).sign();
                let d = if projective { [Symbolic::zero_value(), dy.clone()] }
                    else if sign == Ordering::Less { [dx.negative(), dy.minus(&intercept)] }
                    else { [dx.clone(), dy.plus(&intercept)] };
                let (raw_x_low, raw_x_high) = if pair[0].x <= pair[1].x {
                    (pair[0].x.clone(), pair[1].x.clone())
                } else {
                    (pair[1].x.clone(), pair[0].x.clone())
                };
                let (x_low, x_high) = if projective {
                    (raw_x_low.clone(), raw_x_high.clone())
                } else {
                    (compact(&raw_x_low), compact(&raw_x_high))
                };
                graphs.push(Graph { edge, projective, low: std::cmp::min(pair[0].y.clone(), pair[1].y.clone()),
                    high: std::cmp::max(pair[0].y.clone(), pair[1].y.clone()),
                    x_low, x_high, raw_x_low, raw_x_high, n: [dx, intercept], d, raw_d: dy });
            }
        }
        graphs
    }
    fn simple(p: &Programme<'_>) {
        let graphs = graphs(p);
        for (i, a) in graphs.iter().enumerate() {
            for b in &graphs[i + 1..] {
                // Endpoint bounds are exact for each monotone chart branch.
                // Finite pairs use their common injective preimage as well as
                // its affine equation, avoiding redundant chart denominators.
                let (a_low, a_high, b_low, b_high) = if !a.projective && !b.projective {
                    (&a.raw_x_low, &a.raw_x_high, &b.raw_x_low, &b.raw_x_high)
                } else {
                    (&a.x_low, &a.x_high, &b.x_low, &b.x_high)
                };
                // Strict disjointness only: touching boxes retain the audit.
                if a_high < b_low || b_high < a_low { continue; }
                let low = std::cmp::max(a.low.clone(), b.low.clone());
                let high = std::cmp::min(a.high.clone(), b.high.clone());
                if low > high { continue; }
                let (quadratic, linear, constant) = if !a.projective && !b.projective {
                    // Compactification is strictly increasing on finite X.
                    // Two finite branches intersect exactly when their affine
                    // preimages do; no chart-denominator products are needed.
                    (Symbolic::zero_value(),
                        a.n[0].times(&b.raw_d).minus(&b.n[0].times(&a.raw_d)),
                        a.n[1].times(&b.raw_d).minus(&b.n[1].times(&a.raw_d)))
                } else {
                    (a.n[0].times(&b.d[0]).minus(&b.n[0].times(&a.d[0])),
                        a.n[0].times(&b.d[1]).plus(&a.n[1].times(&b.d[0]))
                            .minus(&b.n[0].times(&a.d[1])).minus(&b.n[1].times(&a.d[0])),
                        a.n[1].times(&b.d[1]).minus(&b.n[1].times(&a.d[1])))
                };
                let evaluate = |y| quadratic.times(y).plus(&linear).times(y).plus(&constant);
                let at_low = evaluate(&low);
                let at_high = evaluate(&high);
                for (y, value) in [(&low, &at_low), (&high, &at_high)] {
                    if value.is_zero_value() {
                        let adjacent = a.edge.0.abs_diff(b.edge.0) == 1
                            && p.vertex(VertexId(a.edge.0.max(b.edge.0))).y == *y;
                        assert!(a.edge == b.edge || adjacent, "nonincident contact {:?} {:?} at {y:?}", a.edge, b.edge);
                    }
                }
                if low == high { continue; }
                assert!(!(quadratic.is_zero_value() && linear.is_zero_value() && constant.is_zero_value()), "overlapping edges");
                assert!(!(at_low.sign() != Ordering::Equal && at_high.sign() != Ordering::Equal && at_low.sign() != at_high.sign()),
                    "crossing {:?} {:?}", a.edge, b.edge);
                if !quadratic.is_zero_value() {
                    // Opposite endpoint derivative signs put the critical point
                    // strictly inside. Its value has sign (4*a*c - b*b)/(4*a);
                    // do not construct and substitute a nested symbolic ratio.
                    let derivative_slope = quadratic.times(&super::constant(2));
                    let low_derivative = derivative_slope.times(&low).plus(&linear).sign();
                    let high_derivative = derivative_slope.times(&high).plus(&linear).sign();
                    if low_derivative != Ordering::Equal && high_derivative != Ordering::Equal
                        && low_derivative != high_derivative {
                        let numerator = quadratic.times(&constant).times(&super::constant(4))
                            .minus(&linear.times(&linear));
                        let value_sign = if quadratic.sign() == Ordering::Less {
                            numerator.sign().reverse()
                        } else {
                            numerator.sign()
                        };
                        assert!(value_sign != Ordering::Equal, "tangent edges");
                        for endpoint in [&at_low, &at_high] {
                            assert!(endpoint.is_zero_value() || endpoint.sign() == value_sign, "interior double crossing");
                        }
                    }
                }
            }
        }
        for (i, event) in p.cut_crossings().iter().enumerate() {
            for other in &p.cut_crossings()[i + 1..] {
                assert_ne!(p.level(&event.level), p.level(&other.level), "two different seam incidences touch");
            }
        }
    }

    fn inspect(old: &Submap<'_>, ribbon: &Ribbon<'_>) {
        let p = &ribbon.programme;
        let root = whole(old.input());
        let local = Boundary::new(p, Chain { start: VertexId(0), end: VertexId(p.len() - 1) }).unwrap();
        assert!(p.piece_count() <= MAX_DESCRIPTORS + 1);
        assert!(p.views().len() <= 12);
        assert_ne!(p.vertex(VertexId(0)), p.vertex(VertexId(p.len() - 1)), "the helper puncture is actually open");
        let mut levels = Vec::new();
        for v in 0..p.len() {
            let point = p.vertex(VertexId(v));
            let q = ribbon.root_source(VertexId(v)).unwrap();
            assert_eq!(point.y.finite_limit().unwrap(), old.input().vertex(q).y);
            assert!(!levels.contains(&point.y), "actual Programme source levels must be distinct");
            levels.push(point.y.clone());
        }
        simple(p);
        for edge in 0..p.edge_count() {
            let edge = EdgeId(edge);
            let half = Symbolic::one_value().over(&constant(2));
            let point = p.edge_point(edge, &half);
            let (hit, x) = p.horizontal_hit(edge, &point.y).unwrap();
            assert_eq!(hit, half);
            assert_eq!(x, point.x);
            let selected = Site::Edge { edge, t: half.clone(), side: Side::Left };
            let projected = ribbon.project_cut(&selected, &mut Work::default()).unwrap();
            if let Some(cut) = projected {
                let actual = root.point(&cut.site).unwrap();
                assert_eq!(actual.x, uncompact(&point.x).finite_limit().unwrap());
                assert_eq!(actual.y, point.y.finite_limit().unwrap());
                assert!(old.region_arcs(ribbon.region).unwrap().contains(&cut.arc));
            } else {
                assert!(p.alias_edge(edge).is_none(), "no positive Original support may be erased");
            }
            assert!(ribbon.project_cut(&Site::Edge { edge, t: half, side: Side::Right }, &mut Work::default()).unwrap().is_none());
        }
        for site in local.occurrences().filter(|site| site.side() == Side::Left) {
            if let Some(cut) = ribbon.project_cut(&site, &mut Work::default()).unwrap() {
                root.validate_site(&cut.site).unwrap(); // exact Slot/germ, not coordinate equality
                assert!(old.region_arcs(ribbon.region).unwrap().contains(&cut.arc));
            }
        }
        for protected in &ribbon.protected {
            assert!(old.region_exits(ribbon.region).unwrap().iter().any(|&id| {
                let (sites, route) = old.chord(id).unwrap();
                route == protected.route && sites == protected.endpoints.each_ref()
                    && old.chord_level(id).unwrap() == &protected.level
            }));
        }
    }

    #[test]
    fn real_original_merge_faces_have_simple_directed_ribbons_and_exact_contacts() {
        let fixtures = [
            vec![(0,0),(0,5)],
            vec![(0,4),(1,0),(2,3),(3,1),(4,5),(5,0),(6,4)],
            vec![(0,-2),(0,2),(4,3),(4,-3)],
            vec![(0,0),(6,0),(6,5),(4,2),(2,5),(0,5)],
        ];
        let mut finite = false;
        let mut wrapping = false;
        let mut null = false;
        for coordinates in fixtures {
            let points: Vec<_> = coordinates.into_iter().map(|(x,y)| Point::integer(x,y)).collect();
            let input = Input::open(&points).unwrap();
            let mut work = Work::default();
            let actual = OriginalMerge.base_map(whole(&input), &mut work).unwrap();
            for id in actual.chord_ids() {
                match actual.chord(id).unwrap().1 { Route::Finite => finite = true, Route::Wrap => wrapping = true, Route::Null => null = true }
            }
            for region in actual.region_ids() {
                if actual.region_weight(&whole(&input), region).unwrap() == 0 { continue; }
                inspect(&actual, &Ribbon::compile(&actual, region, &mut work).unwrap());
            }
            let mut catalogue = Catalogue::build(&input, 1, &mut OriginalMerge, &mut work).unwrap();
            let mut old = catalogue.take_root().unwrap();
            for region in old.region_ids() {
                if old.region_weight(&whole(&input), region).unwrap() == 0 { continue; }
                inspect(&old, &Ribbon::compile(&old, region, &mut work).unwrap());
            }
            old.coarsen(&whole(&input), input.edge_count() * 2, &mut work).unwrap();
            for region in old.region_ids() {
                if old.region_weight(&whole(&input), region).unwrap() == 0 { continue; }
                let ribbon = Ribbon::compile(&old, region, &mut work).unwrap();
                inspect(&old, &ribbon);
                // Real same-germ cap sectors go around the obstacle, not
                // directly between independent slid lane endpoints.
                if old.chord_ids().next().is_none() {
                    for cap in [old.chain().start, old.chain().end] {
                        let centre = input.vertex(cap);
                        let mut corners = [false; 4];
                        for i in 0..ribbon.programme.piece_count() {
                            let (piece, _) = ribbon.programme.piece(i);
                            if let Piece::Finite { start, end } = piece {
                                for point in [start, end] {
                                    let y = point.y.minus(&Symbolic::variable(32).times(&point.x));
                                    let x = point.x.minus(&scalar(&centre.x));
                                    let y = y.minus(&scalar(&centre.y));
                                    if x.is_zero_value() && y.finite_limit().unwrap().is_zero_value() {
                                        corners[if y.sign() == Ordering::Greater { 0 } else { 2 }] = true;
                                    }
                                    if y.is_zero_value() && x.finite_limit().unwrap().is_zero_value() {
                                        corners[if x.sign() == Ordering::Greater { 1 } else { 3 }] = true;
                                    }
                                }
                            }
                        }
                        assert!(corners.into_iter().filter(|corner| *corner).count() >= 3, "cap must realize the almost-full clockwise sector");
                    }
                }
            }
        }
        assert!(finite && wrapping && null, "real fixtures must exercise finite, Null and wrapping old exits");
    }

    #[test]
    fn actual_augmented_transits_are_split_aliases_and_keep_remote_source_class() {
        let input = Input::open(&[
            Point::integer(-5,4), Point::integer(-5,-5), Point::integer(-1,-1),
            Point::integer(0,0), Point::integer(1,-2), Point::integer(5,-4),
            Point::integer(5,2), Point::integer(10,3), Point::integer(10,-3),
            Point::integer(12,-6), Point::integer(12,5),
        ]).unwrap();
        let boundary = whole(&input);
        let q = (0..input.len()).map(VertexId).find(|&v| input.source(v) == &VertexSource::Original(3)).unwrap();
        let contact = |original, side| (0..input.edge_count()).map(EdgeId).find_map(|edge| {
            if input.edge_source(edge).original != original { return None; }
            let (t, _) = input.horizontal_hit(edge, &input.vertex(q).y)?;
            (t > Rational::zero_value() && t < Rational::one_value()).then_some(Site::Edge { edge, t, side })
        }).unwrap();
        let a = contact(7, Side::Left);
        let b = contact(9, Side::Left);
        let old = Submap::from_verified_chords(&boundary, vec![VisibleChord {
            endpoints: [a.clone(), b.clone()], route: Route::Finite, level: LevelSource::Vertex(q),
        }], &mut Work::default()).unwrap();
        let mut transits = [false; 2];
        for region in old.region_ids() {
            let ribbon = Ribbon::compile(&old, region, &mut Work::default()).unwrap();
            inspect(&old, &ribbon);
            assert!(ribbon.exceptional.contains(input.vertex(q)));
            for (i, original) in [&a, &b].into_iter().enumerate() {
                let Site::Edge { edge, t, .. } = original else { unreachable!() };
                let transit = Site::Edge { edge: *edge, t: t.clone(), side: Side::Right };
                if ribbon.star_flags.contains(&transit) {
                    transits[i] = true;
                    let mut supports = 0;
                    for j in 0..ribbon.programme.piece_count() {
                        let (piece, chain) = ribbon.programme.piece(j);
                        if !matches!(piece, Piece::Alias { .. }) { continue; }
                        for (e, parameter) in [(EdgeId(chain.start.0), Symbolic::zero_value()), (EdgeId(chain.end.0 - 1), Symbolic::one_value())] {
                            let alias = ribbon.programme.alias_edge(e).unwrap();
                            let raw_t = alias.start.plus(&parameter.times(&alias.end.minus(&alias.start)));
                            let t = ribbon.programme.view(alias.view).project_parameter(alias.edge, &raw_t).unwrap();
                            let Tag::Original { side, .. } = ribbon.tags[j] else { unreachable!() };
                            let projected = boundary.normalize_site(&Site::Edge { edge: alias.edge, t, side }).unwrap();
                            if projected == transit { supports += 1; }
                        }
                    }
                    assert_eq!(supports, 2, "both positive transit branches remain labelled Original aliases");
                }
            }
        }
        assert!(transits.into_iter().all(|seen| seen));
    }
}
