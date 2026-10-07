//! Read-only indexed curves. A local view can alias long input runs without
//! copying coordinates; its horizontal chart may be compactified at infinity.
use crate::geometry::{orientation, horizontal_hit, Point, Rational};
use crate::input::{EdgeId, Input, VertexId};
use crate::scalar::ExactScalar;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::rc::Rc;

/// A normalized source of a horizontal level, independent of stored contact
/// parameters. Descendant chords inherit this source instead of nesting
/// intersection expressions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LevelSource<S = Rational> {
    Vertex(VertexId),
    Frozen(Rc<S>),
}
impl<S> LevelSource<S> {
    pub fn frozen(value: S) -> Self { Self::Frozen(Rc::new(value)) }
}

/// An interior crossing of the horizontal chart cut by an input edge.
/// Curves store only a bounded number of these events, independently of length.
#[derive(Clone, Debug)]
pub struct CutCrossing<S = Rational> {
    pub edge: EdgeId,
    pub parameter: S,
    pub level: LevelSource<S>,
    /// Increasing circle coordinate crosses from the right chart end to left.
    pub forward: Ordering,
}

/// Primitive operations for a simple open curve with nonhorizontal edges and
/// distinct vertex levels. Each operation must have bounded description cost.
/// `horizontal_hit` returns a normalized forward edge parameter and the
/// horizontal-circle chart coordinate. Curved/wrapping edges must implement
/// actual intersections and tangents, not the chord of their endpoints.
pub trait Curve {
    type Scalar: ExactScalar;
    const MAX_LEAF_EDGES: usize;
    fn len(&self) -> usize;
    fn vertex(&self, vertex: VertexId) -> Cow<'_, Point<Self::Scalar>>;
    fn edge_y_sign(&self, edge: EdgeId) -> Ordering;
    fn turn(&self, vertex: VertexId) -> Ordering;
    fn horizontal_hit(&self, edge: EdgeId, level: &Self::Scalar)
        -> Option<(Self::Scalar, Self::Scalar)>;
    fn edge_point(&self, edge: EdgeId, t: &Self::Scalar) -> Point<Self::Scalar>;
    /// Forward tangent in the actual local chart, not an endpoint secant.
    fn edge_tangent(&self, edge: EdgeId, t: &Self::Scalar) -> Point<Self::Scalar>;
    /// All chart-cut events; the slice length has a curve-independent bound.
    fn cut_crossings(&self) -> &[CutCrossing<Self::Scalar>] { &[] }
    fn edge_count(&self) -> usize { self.len() - 1 }
    fn level<'s>(&'s self, source: &'s LevelSource<Self::Scalar>) -> Cow<'s, Self::Scalar> {
        match source {
            LevelSource::Vertex(vertex) => match self.vertex(*vertex) {
                Cow::Borrowed(point) => Cow::Borrowed(&point.y),
                Cow::Owned(point) => Cow::Owned(point.y),
            },
            LevelSource::Frozen(value) => Cow::Borrowed(value.as_ref()),
        }
    }
}

impl Curve for Input {
    type Scalar = Rational;
    const MAX_LEAF_EDGES: usize = 16;
    fn len(&self) -> usize { Input::len(self) }
    fn vertex(&self, vertex: VertexId) -> Cow<'_, Point> {
        Cow::Borrowed(Input::vertex(self, vertex))
    }
    fn edge_y_sign(&self, edge: EdgeId) -> Ordering { Input::edge_y_sign(self, edge) }
    fn turn(&self, vertex: VertexId) -> Ordering {
        orientation(Input::vertex(self, VertexId(vertex.0 - 1)),
            Input::vertex(self, vertex), Input::vertex(self, VertexId(vertex.0 + 1)))
    }
    fn horizontal_hit(&self, edge: EdgeId, level: &Rational) -> Option<(Rational, Rational)> {
        horizontal_hit(Input::vertex(self, VertexId(edge.0)),
            Input::vertex(self, VertexId(edge.0 + 1)), level)
    }
    fn edge_point(&self, edge: EdgeId, t: &Rational) -> Point {
        let a = Input::vertex(self, VertexId(edge.0));
        let b = Input::vertex(self, VertexId(edge.0 + 1));
        Point::new(&a.x + t * (&b.x - &a.x), &a.y + t * (&b.y - &a.y))
    }
    fn edge_tangent(&self, edge: EdgeId, _: &Rational) -> Point {
        let a = Input::vertex(self, VertexId(edge.0));
        let b = Input::vertex(self, VertexId(edge.0 + 1));
        Point::new(&b.x - &a.x, &b.y - &a.y)
    }
}
