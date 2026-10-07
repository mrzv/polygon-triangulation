//! Constant-description signed support offsets of the owning Root input.
//! Saved Root maps remain borrowed: callers must establish topology stability
//! for their infinitesimal lane and shear priorities before querying them.
use crate::boundary::Site;
use crate::curve::{Curve, LevelSource};
use crate::geometry::{ray_order, Direction, Point, Rational};
use crate::input::{EdgeId, Input, VertexId};
use crate::oracle::{PointHit, RayProbe};
use crate::scalar::ExactScalar;
use crate::symbolic::{LimitError, Symbolic};
use crate::work::Work;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ViewError { OutsideInput, HorizontalSupport, SourceOutsideSupport }
impl fmt::Display for ViewError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for ViewError {}

#[derive(Clone, Debug)]
pub struct OffsetView<'a> {
    input: &'a Input,
    width: Symbolic<'a>,
    shear: Symbolic<'a>,
}

fn cross<S: ExactScalar>(a: &Point<S>, b: &Point<S>) -> S {
    a.x.times(&b.y).minus(&a.y.times(&b.x))
}
fn compact<S: ExactScalar>(x: &S) -> S {
    x.over(&S::one_value().plus(&x.absolute()))
}

impl<'a> OffsetView<'a> {
    pub fn new(input: &'a Input, width: Symbolic<'a>, shear: Symbolic<'a>) -> Self {
        Self { input, width, shear }
    }
    pub fn input(&self) -> &'a Input { self.input }
    pub fn width(&self) -> &Symbolic<'a> { &self.width }
    pub fn shear(&self) -> &Symbolic<'a> { &self.shear }

    fn root_direction(&self, edge: EdgeId) -> Point<Rational> {
        let a = self.input.vertex(VertexId(edge.0));
        let b = self.input.vertex(VertexId(edge.0 + 1));
        Point::new(&b.x - &a.x, &b.y - &a.y)
    }
    fn shifted(&self, vertex: VertexId, d: &Point<Rational>) -> Point<Symbolic<'a>> {
        let p = self.input.vertex(vertex);
        let norm = d.x.absolute().plus(&d.y.absolute());
        let nx = Symbolic::owned(d.y.negative().over(&norm));
        let ny = Symbolic::owned(d.x.over(&norm));
        Point::new(Symbolic::borrowed(&p.x).plus(&self.width.times(&nx)),
            Symbolic::borrowed(&p.y).plus(&self.width.times(&ny)))
    }
    pub fn raw_vertex(&self, vertex: VertexId) -> Point<Symbolic<'a>> {
        assert!(vertex.0 < self.input.len(), "offset vertex outside Root input");
        if vertex.0 == 0 {
            return self.shifted(vertex, &self.root_direction(EdgeId(0)));
        }
        let incoming = self.root_direction(EdgeId(vertex.0 - 1));
        let a = self.shifted(vertex, &incoming);
        if vertex.0 + 1 == self.input.len() { return a; }
        let outgoing = self.root_direction(EdgeId(vertex.0));
        let determinant = cross(&incoming, &outgoing);
        // Positive collinear continuation has the same normalized normal.
        // Backtracking is excluded by the Root input's construction contract.
        if determinant.is_zero_value() { return a; }
        let b = self.shifted(vertex, &outgoing);
        let delta = Point::new(b.x.minus(&a.x), b.y.minus(&a.y));
        let outgoing = Point::new(Symbolic::owned(outgoing.x), Symbolic::owned(outgoing.y));
        let t = cross(&delta, &outgoing).over(&Symbolic::owned(determinant));
        Point::new(a.x.plus(&t.times(&Symbolic::owned(incoming.x))),
            a.y.plus(&t.times(&Symbolic::owned(incoming.y))))
    }
    pub fn raw_edge_point(&self, edge: EdgeId, t: &Symbolic<'a>) -> Point<Symbolic<'a>> {
        let a = self.raw_vertex(VertexId(edge.0));
        let b = self.raw_vertex(VertexId(edge.0 + 1));
        Point::new(a.x.plus(&t.times(&b.x.minus(&a.x))),
            a.y.plus(&t.times(&b.y.minus(&a.y))))
    }
    fn shear_point(&self, p: Point<Symbolic<'a>>) -> Point<Symbolic<'a>> {
        // X is finite here; compact/projective infinity is never sheared.
        let y = p.y.plus(&self.shear.times(&p.x));
        Point::new(p.x, y)
    }
    pub fn finite_vertex(&self, vertex: VertexId) -> Point<Symbolic<'a>> {
        self.shear_point(self.raw_vertex(vertex))
    }
    pub fn finite_edge_point(&self, edge: EdgeId, t: &Symbolic<'a>) -> Point<Symbolic<'a>> {
        self.shear_point(self.raw_edge_point(edge, t))
    }
    pub fn level_source(&self, source: &LevelSource<Rational>) -> Symbolic<'a> {
        match source {
            LevelSource::Vertex(vertex) => self.finite_vertex(*vertex).y,
            LevelSource::Frozen(value) => Symbolic::retained(value.clone()),
        }
    }
    // Deliberately unbounded parameter: saved-map clipping comparisons need
    // the actual supporting-line threshold even when it lies beyond an edge.
    fn support_parameter(&self, edge: EdgeId, level: &Symbolic<'a>) -> Result<Symbolic<'a>, ViewError> {
        if edge.0 >= self.input.edge_count() { return Err(ViewError::OutsideInput); }
        let a = self.finite_vertex(VertexId(edge.0));
        let b = self.finite_vertex(VertexId(edge.0 + 1));
        let dy = b.y.minus(&a.y);
        if dy.is_zero_value() { return Err(ViewError::HorizontalSupport); }
        Ok(level.minus(&a.y).over(&dy))
    }
    pub fn lift_site(&self, site: &Site<Rational>, source: &LevelSource<Rational>)
        -> Result<Site<Symbolic<'a>>, ViewError>
    {
        if let LevelSource::Vertex(vertex) = source {
            if vertex.0 >= self.input.len() { return Err(ViewError::OutsideInput); }
        }
        match site {
            Site::Vertex { vertex, side, slot } => {
                if vertex.0 >= self.input.len() { return Err(ViewError::OutsideInput); }
                Ok(Site::Vertex { vertex: *vertex, side: *side, slot: *slot })
            }
            Site::Edge { edge, side, .. } => {
                let t = self.support_parameter(*edge, &self.level_source(source))?;
                if t.sign() == Ordering::Less || t.compare_one() == Ordering::Greater {
                    return Err(ViewError::SourceOutsideSupport);
                }
                Ok(Site::Edge { edge: *edge, t, side: *side })
            }
        }
    }
    /// Recover the actual support residue, not the nominal view parameter.
    /// Miter endpoints can move along the Root support before taking the limit.
    pub fn project_parameter(&self, edge: EdgeId, t: &Symbolic<'a>) -> Result<Rational, LimitError> {
        let p = self.raw_edge_point(edge, t);
        let a = self.input.vertex(VertexId(edge.0));
        let b = self.input.vertex(VertexId(edge.0 + 1));
        p.y.minus(&Symbolic::borrowed(&a.y))
            .over(&Symbolic::owned(&b.y - &a.y)).finite_limit()
    }
}

impl<'a> Curve for OffsetView<'a> {
    type Scalar = Symbolic<'a>;
    const MAX_LEAF_EDGES: usize = 16;
    fn len(&self) -> usize { self.input.len() }
    fn vertex(&self, vertex: VertexId) -> Cow<'_, Point<Self::Scalar>> {
        let p = self.finite_vertex(vertex);
        Cow::Owned(Point::new(compact(&p.x), p.y))
    }
    fn edge_y_sign(&self, edge: EdgeId) -> Ordering {
        self.finite_vertex(VertexId(edge.0 + 1)).y
            .minus(&self.finite_vertex(VertexId(edge.0)).y).sign()
    }
    fn turn(&self, vertex: VertexId) -> Ordering {
        let incoming = self.edge_tangent(EdgeId(vertex.0 - 1), &Symbolic::one_value());
        let outgoing = self.edge_tangent(EdgeId(vertex.0), &Symbolic::zero_value());
        cross(&incoming, &outgoing).sign()
    }
    fn horizontal_hit(&self, edge: EdgeId, level: &Symbolic<'a>) -> Option<(Symbolic<'a>, Symbolic<'a>)> {
        if edge.0 >= self.input.edge_count() { return None; }
        let a = self.finite_vertex(VertexId(edge.0));
        let b = self.finite_vertex(VertexId(edge.0 + 1));
        let dy = b.y.minus(&a.y);
        if dy.is_zero_value() { return None; }
        let t = level.minus(&a.y).over(&dy);
        if t.sign() == Ordering::Less || t.compare_one() == Ordering::Greater { return None; }
        let x = a.x.plus(&t.times(&b.x.minus(&a.x)));
        Some((t, compact(&x)))
    }
    fn edge_point(&self, edge: EdgeId, t: &Symbolic<'a>) -> Point<Symbolic<'a>> {
        let p = self.finite_edge_point(edge, t);
        Point::new(compact(&p.x), p.y)
    }
    fn edge_tangent(&self, edge: EdgeId, t: &Symbolic<'a>) -> Point<Symbolic<'a>> {
        let a = self.raw_vertex(VertexId(edge.0));
        let b = self.raw_vertex(VertexId(edge.0 + 1));
        let dx = b.x.minus(&a.x);
        let dy = b.y.minus(&a.y).plus(&self.shear.times(&dx));
        let x = a.x.plus(&t.times(&dx));
        let denominator = Symbolic::one_value().plus(&x.absolute());
        Point::new(dx.over(&denominator.times(&denominator)), dy)
    }
}

/// A compact-coordinate query against an owning Root oracle's saved topology.
#[derive(Debug)]
pub struct OffsetProbe<'v, 'a> {
    view: &'v OffsetView<'a>,
    point: Point<Symbolic<'a>>,
    direction: Direction,
}
impl<'v, 'a> OffsetProbe<'v, 'a> {
    pub fn new(view: &'v OffsetView<'a>, point: &Point<Symbolic<'a>>, direction: Direction) -> Self {
        Self { view, point: point.clone(), direction }
    }
}
impl<'a> RayProbe<Input> for OffsetProbe<'_, 'a> {
    type Hit = PointHit<Symbolic<'a>>;
    fn edge_hit(&self, input: &Input, edge: EdgeId, work: &mut Work) -> Option<Self::Hit> {
        assert!(std::ptr::eq(input, self.view.input()), "offset probe uses a different Root input");
        // As with PointProbe, the owning oracle counts arc_edge_visits at the
        // attempt site, while the probe counts every predicate, including misses.
        work.predicates += 1;
        let (t, x) = self.view.horizontal_hit(edge, &self.point.y)?;
        Some(PointHit { edge, t, x })
    }
    fn edge(&self, hit: &Self::Hit) -> EdgeId { hit.edge }
    fn parameter_cmp(&self, hit: &Self::Hit, t: &Rational) -> Ordering {
        hit.t.cmp(&Symbolic::borrowed(t))
    }
    fn compare_hits(&self, a: &Self::Hit, b: &Self::Hit) -> Ordering {
        ray_order(&self.point.x, self.direction, &a.x, &b.x)
    }
    fn compare_level(&self, y: &Rational) -> Ordering { self.point.y.cmp(&Symbolic::borrowed(y)) }
    fn compare_endpoint(&self, _input: &Input, hit: &Self::Hit, endpoint: &Site<Rational>, source: &LevelSource<Rational>) -> Ordering {
        let threshold = match endpoint {
            Site::Edge { edge, .. } => self.view.support_parameter(*edge, &self.view.level_source(source))
                .expect("topology-stable offset support must remain nonhorizontal"),
            Site::Vertex { vertex, .. } => {
                if vertex.0 == hit.edge.0 { Symbolic::zero_value() }
                else { Symbolic::one_value() }
            }
        };
        hit.t.cmp(&threshold)
    }
    fn compare_source_level(&self, _input: &Input, source: &LevelSource<Rational>) -> Ordering {
        self.point.y.cmp(&self.view.level_source(source))
    }
    fn direction(&self) -> Direction { self.direction }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::boundary::{Boundary, Chain, Side, Slot};
    use crate::input::VertexSource;
    use crate::oracle::RayOracle;
    use crate::submap::Submap;

    fn q(n: i64, d: i64) -> Rational { Rational::new(n.into(), d.into()) }
    fn s(n: i64, d: i64) -> Symbolic<'static> { Symbolic::owned(q(n, d)) }
    fn original(input: &Input, index: usize) -> VertexId {
        VertexId((0..input.len()).find(|&i|
            matches!(input.source(VertexId(i)), VertexSource::Original(j) if *j == index)
        ).unwrap())
    }

    #[test]
    fn signed_miters_are_intersections_of_both_shifted_supports() {
        let input = Input::open(&[Point::integer(0, 0), Point::integer(2, 1),
            Point::integer(0, 2)]).unwrap();
        let vertex = original(&input, 1);
        for width in [s(1, 1), s(-1, 1), Symbolic::variable(0)] {
            let view = OffsetView::new(&input, width.clone(), Symbolic::zero_value());
            assert!(std::ptr::eq(view.input(), &input));
            let p = view.raw_vertex(vertex);
            assert_eq!(p.x, s(2, 1).minus(&width.times(&s(61, 63))));
            assert_eq!(p.y, s(5, 1).minus(&width.times(&s(22, 63))));
            for edge in [EdgeId(vertex.0 - 1), EdgeId(vertex.0)] {
                let d = view.root_direction(edge);
                let shifted = view.shifted(vertex, &d);
                let d = Point::new(Symbolic::owned(d.x), Symbolic::owned(d.y));
                assert!(cross(&Point::new(p.x.minus(&shifted.x),
                    p.y.minus(&shifted.y)), &d).is_zero_value());
            }
            let p = view.edge_point(EdgeId(vertex.0), &s(1, 3));
            assert!(p.x.absolute() < Symbolic::one_value());
        }
    }

    #[test]
    fn positive_collinear_continuations_share_normal_and_zero_turn() {
        let input = Input::open(&[Point::integer(0, 0), Point::integer(1, 1),
            Point::integer(3, 3)]).unwrap();
        let width = Symbolic::variable(0);
        let view = OffsetView::new(&input, width.clone(), Symbolic::variable(1));
        for i in 1..input.len() - 1 {
            let vertex = VertexId(i);
            let root = input.vertex(vertex);
            let expected = Point::new(Symbolic::borrowed(&root.x).minus(&width.times(&s(5, 6))),
                Symbolic::borrowed(&root.y).plus(&width.times(&s(1, 6))));
            assert_eq!(view.raw_vertex(vertex), expected);
            assert_eq!(view.turn(vertex), Ordering::Equal);
        }
    }

    #[test]
    fn compact_contacts_and_tangents_are_not_endpoint_secants() {
        let input = Input::open(&[Point::integer(0, 0), Point::integer(4, 3)]).unwrap();
        let shear = Symbolic::variable(1);
        let view = OffsetView::new(&input, Symbolic::zero_value(), shear.clone());
        let level = s(19, 2).plus(&shear.times(&s(2, 1)));
        let (t, u) = view.horizontal_hit(EdgeId(0), &level).unwrap();
        assert_eq!(t, s(1, 2));
        assert_eq!(u, s(2, 3));
        assert_ne!(u, s(2, 5));
        let tangent = view.edge_tangent(EdgeId(0), &t);
        assert_eq!(tangent.x, s(4, 9));
        assert_eq!(tangent.y, s(19, 1).plus(&shear.times(&s(4, 1))));
        assert_eq!(view.edge_point(EdgeId(0), &t), Point::new(u, level));
        let outside = view.finite_vertex(VertexId(1)).y.plus(&s(1, 1));
        assert!(view.horizontal_hit(EdgeId(0), &outside).is_none());
    }

    #[test]
    fn saved_source_replaces_stale_parameter_and_rejects_outside_level() {
        let input = Input::open(&[Point::integer(0, 0), Point::integer(4, 3)]).unwrap();
        let view = OffsetView::new(&input, Symbolic::variable(0), Symbolic::variable(1));
        let source = LevelSource::frozen(q(19, 2));
        let stale = Site::Edge { edge: EdgeId(0), t: q(9, 10), side: Side::Right };
        let Site::Edge { t, side, .. } = view.lift_site(&stale, &source).unwrap() else { panic!() };
        assert_eq!(side, Side::Right);
        assert_ne!(t, s(9, 10));
        assert_ne!(t, s(1, 2));
        assert_eq!(view.finite_edge_point(EdgeId(0), &t).y, s(19, 2));
        let point = view.edge_point(EdgeId(0), &t);
        let probe = OffsetProbe::new(&view, &point, Direction::Right);
        let mut work = Work::default();
        let hit = probe.edge_hit(&input, EdgeId(0), &mut work).unwrap();
        assert_eq!(probe.compare_endpoint(&input, &hit, &stale, &source), Ordering::Equal);
        assert_eq!(probe.parameter_cmp(&hit, &q(9, 10)), Ordering::Less);
        assert_eq!(view.lift_site(&stale, &LevelSource::frozen(q(30, 1))),
            Err(ViewError::SourceOutsideSupport));
        let vertex = Site::Vertex { vertex: VertexId(0), side: Side::Left, slot: Slot::Single };
        assert_eq!(view.lift_site(&vertex, &LevelSource::Vertex(VertexId(0))).unwrap(),
            Site::Vertex { vertex: VertexId(0), side: Side::Left, slot: Slot::Single });
        let displaced_level = view.level_source(&LevelSource::Vertex(VertexId(0)));
        assert_ne!(displaced_level, Symbolic::borrowed(&input.vertex(VertexId(0)).y));
        let point = Point::new(s(0, 1), displaced_level);
        let probe = OffsetProbe::new(&view, &point, Direction::Left);
        assert_eq!(probe.compare_source_level(&input, &LevelSource::Vertex(VertexId(0))),
            Ordering::Equal);
        assert_ne!(probe.compare_level(&input.vertex(VertexId(0)).y), Ordering::Equal);
        assert!(probe.edge_hit(&input, EdgeId(0), &mut work).is_some());
        let outside = Point::new(s(0, 1), s(30, 1));
        assert!(OffsetProbe::new(&view, &outside, Direction::Right)
            .edge_hit(&input, EdgeId(0), &mut work).is_none());
        assert_eq!(work.predicates, 3);
        assert_eq!(work.arc_edge_visits, 0); // Counts belong to the owning oracle.
    }

    #[test]
    fn projection_uses_actual_support_point_and_cancels_symbolic_factors() {
        let input = Input::open(&[Point::integer(0, 0), Point::integer(2, 1),
            Point::integer(0, 2)]).unwrap();
        let vertex = original(&input, 1);
        let edge = EdgeId(vertex.0);
        let view = OffsetView::new(&input, s(1, 1), Symbolic::zero_value());
        let p = view.raw_edge_point(edge, &s(0, 1));
        let a = input.vertex(vertex);
        let b = input.vertex(VertexId(vertex.0 + 1));
        assert_eq!(view.project_parameter(edge, &s(0, 1)).unwrap(),
            p.y.finite_limit().unwrap().minus(&a.y).over(&b.y.minus(&a.y)));
        assert_ne!(view.project_parameter(edge, &s(0, 1)).unwrap(), q(0, 1));
        let eps = Symbolic::variable(0);
        let t = eps.times(&s(2, 1)).over(&eps.times(&s(3, 1)));
        let infinitesimal = OffsetView::new(&input, eps, Symbolic::variable(1));
        assert_eq!(infinitesimal.project_parameter(edge, &t).unwrap(), q(2, 3));
    }

    #[test]
    fn owning_root_oracle_shoots_actual_displaced_support_without_rebuild() {
        let input = Input::open(&[Point::integer(0, 0), Point::integer(4, 3)]).unwrap();
        let chain = Chain::new(&input, VertexId(0), VertexId(1)).unwrap();
        let boundary = Boundary::new(&input, chain).unwrap();
        let mut work = Work::default();
        let map = Submap::from_verified_chords(&boundary, vec![], &mut work).unwrap();
        let oracle = RayOracle::build(map, 2, &mut work).unwrap();
        let view = OffsetView::new(&input, Symbolic::variable(0), Symbolic::variable(1));
        let expected = view.edge_point(EdgeId(0), &s(1, 2));
        for direction in [Direction::Left, Direction::Right] {
            let point = Point::new(s(0, 1), expected.y.clone());
            let probe = OffsetProbe::new(&view, &point, direction);
            let hit = oracle.shoot(&probe, &mut work).unwrap().unwrap();
            assert_eq!(hit.t, s(1, 2));
            assert_eq!(hit.x, expected.x);
        }
        assert!(std::ptr::eq(oracle.map().input(), view.input()));
        assert!(work.arc_edge_visits > 0);
    }
}
