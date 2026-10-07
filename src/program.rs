//! Bounded-description local curves: long root runs stay lazy, and chart-cut
//! events belong to projective edges rather than synthetic seam vertices.
use crate::boundary::Chain;
use crate::curve::{Curve, CutCrossing, LevelSource};
use crate::geometry::Point;
use crate::input::{EdgeId, VertexId};
use crate::scalar::ExactScalar;
use crate::symbolic::Symbolic;
use crate::view::OffsetView;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Debug)]
pub enum Piece<'a> {
    Alias { view: usize, first: EdgeId, last: EdgeId, start: Symbolic<'a>, end: Symbolic<'a>, reverse: bool },
    Finite { start: Point<Symbolic<'a>>, end: Point<Symbolic<'a>> },
    Projective { start: Point<Symbolic<'a>>, end: Point<Symbolic<'a>>, winding: i8 },
}

#[derive(Clone, Debug)]
pub struct AliasEdge<'a> {
    pub view: usize,
    pub edge: EdgeId,
    pub start: Symbolic<'a>,
    pub end: Symbolic<'a>,
    pub reverse: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProgrammeError {
    InvalidView,
    OutsideView,
    InvalidClipping,
    InvalidWinding,
    Horizontal,
    Disconnected,
    SizeOverflow,
}
impl fmt::Display for ProgrammeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InvalidView => "alias names a missing offset view",
            Self::OutsideView => "alias edge lies outside its offset view",
            Self::InvalidClipping => "alias has invalid traversal or a nonpositive clipped interval",
            Self::InvalidWinding => "projective route is not a positive span of at most one circuit",
            Self::Horizontal => "piece has a horizontal physical edge",
            Self::Disconnected => "piece start differs exactly from the preceding endpoint",
            Self::SizeOverflow => "programme index range overflows usize",
        })
    }
}
impl std::error::Error for ProgrammeError {}

struct StoredPiece<'a> {
    piece: Piece<'a>,
    chain: Chain,
}

/// Storage scales with the caller's bounded number of descriptors, never with
/// the length of an alias. Interior alias nonhorizontalness is the offset-view
/// contract; append checks only the clipped boundary edges, without a root scan.
pub struct Programme<'a> {
    views: Vec<OffsetView<'a>>,
    pieces: Vec<StoredPiece<'a>>,
    cuts: Vec<CutCrossing<Symbolic<'a>>>,
    len: usize,
}

fn compact<'a>(x: &Symbolic<'a>) -> Symbolic<'a> {
    x.over(&Symbolic::one_value().plus(&x.absolute()))
}
fn fold<'a>(x: Symbolic<'a>) -> Symbolic<'a> {
    let one = Symbolic::one_value();
    let two = Symbolic::from_usize_value(2);
    if x > one { x.minus(&two) }
    else if x < one.negative() { x.plus(&two) }
    else { x }
}
fn interpolate<'a>(a: &Point<Symbolic<'a>>, b: &Point<Symbolic<'a>>, t: &Symbolic<'a>) -> Point<Symbolic<'a>> {
    Point::new(a.x.plus(&t.times(&b.x.minus(&a.x))), a.y.plus(&t.times(&b.y.minus(&a.y))))
}
fn unwrapped_end<'a>(end: &Point<Symbolic<'a>>, winding: i8) -> Point<Symbolic<'a>> {
    let two = Symbolic::from_usize_value(2);
    let x = match winding { -1 => end.x.minus(&two), 0 => end.x.clone(), 1 => end.x.plus(&two), _ => unreachable!() };
    Point::new(x, end.y.clone())
}

impl<'a> Programme<'a> {
    pub fn new(views: Vec<OffsetView<'a>>) -> Self {
        Self { views, pieces: Vec::new(), cuts: Vec::new(), len: 0 }
    }
    pub fn views(&self) -> &[OffsetView<'a>] { &self.views }
    pub fn view(&self, index: usize) -> &OffsetView<'a> { &self.views[index] }
    pub fn piece_count(&self) -> usize { self.pieces.len() }
    pub fn piece(&self, index: usize) -> (&Piece<'a>, Chain) {
        let stored = &self.pieces[index];
        (&stored.piece, stored.chain)
    }

    pub fn piece_index(&self, edge: EdgeId) -> usize {
        assert!(edge.0 < self.len.saturating_sub(1), "programme edge out of range");
        self.pieces.partition_point(|piece| piece.chain.end.0 <= edge.0)
    }
    pub fn alias_edge(&self, edge: EdgeId) -> Option<AliasEdge<'a>> {
        let stored = &self.pieces[self.piece_index(edge)];
        Self::alias_at(&stored.piece, edge.0 - stored.chain.start.0)
    }
    fn alias_at(piece: &Piece<'a>, offset: usize) -> Option<AliasEdge<'a>> {
        let Piece::Alias { view, first, last, start, end, reverse } = piece else { return None; };
        let edge = EdgeId(if *reverse { first.0 - offset } else { first.0 + offset });
        let from = if offset == 0 { start.clone() } else if *reverse { Symbolic::one_value() } else { Symbolic::zero_value() };
        let to = if edge == *last { end.clone() } else if *reverse { Symbolic::zero_value() } else { Symbolic::one_value() };
        Some(AliasEdge { view: *view, edge, start: from, end: to, reverse: *reverse })
    }
    fn endpoint(&self, piece: &Piece<'a>, end_point: bool) -> Point<Symbolic<'a>> {
        match piece {
            Piece::Alias { view, first, last, start, end, .. } => self.views[*view].edge_point(
                if end_point { *last } else { *first }, if end_point { end } else { start }),
            Piece::Finite { start, end } => {
                let p = if end_point { end } else { start };
                Point::new(compact(&p.x), p.y.clone())
            },
            Piece::Projective { start, end, .. } => if end_point { end.clone() } else { start.clone() },
        }
    }
    pub fn append(&mut self, piece: Piece<'a>) -> Result<Chain, ProgrammeError> {
        let edges = match &piece {
            Piece::Alias { view, first, last, start, end, reverse } => {
                let v = self.views.get(*view).ok_or(ProgrammeError::InvalidView)?;
                if first.0 >= v.input().edge_count() || last.0 >= v.input().edge_count() { return Err(ProgrammeError::OutsideView); }
                let zero = Symbolic::zero_value();
                let one = Symbolic::one_value();
                if start < &zero || start > &one || end < &zero || end > &one
                    || (!reverse && first > last) || (*reverse && first < last)
                    || (first == last && if *reverse { start <= end } else { start >= end })
                    || (first != last && if *reverse { start == &zero || end == &one } else { start == &one || end == &zero }) {
                    return Err(ProgrammeError::InvalidClipping);
                }
                if v.edge_y_sign(*first) == Ordering::Equal || v.edge_y_sign(*last) == Ordering::Equal { return Err(ProgrammeError::Horizontal); }
                first.0.abs_diff(last.0).checked_add(1).ok_or(ProgrammeError::SizeOverflow)?
            },
            Piece::Finite { start, end } => {
                if start.y == end.y { return Err(ProgrammeError::Horizontal); }
                1
            },
            Piece::Projective { start, end, winding } => {
                let one = Symbolic::one_value();
                if !(-1..=1).contains(winding) || start.x.absolute() > one || end.x.absolute() > one { return Err(ProgrammeError::InvalidWinding); }
                let span = unwrapped_end(end, *winding).x.minus(&start.x).absolute();
                if span.is_zero_value() || span > Symbolic::from_usize_value(2) { return Err(ProgrammeError::InvalidWinding); }
                if start.y == end.y { return Err(ProgrammeError::Horizontal); }
                1
            },
        };
        let start = self.len.saturating_sub(1);
        let end = start.checked_add(edges).ok_or(ProgrammeError::SizeOverflow)?;
        let len = end.checked_add(1).ok_or(ProgrammeError::SizeOverflow)?;
        if let Some(previous) = self.pieces.last() {
            if self.endpoint(&previous.piece, true) != self.endpoint(&piece, false) { return Err(ProgrammeError::Disconnected); }
        }
        if let Piece::Projective { start: a, end: b, winding } = &piece {
            let b = unwrapped_end(b, *winding);
            let dx = b.x.minus(&a.x);
            let seam = if dx.sign() == Ordering::Greater { Symbolic::one_value() } else { Symbolic::one_value().negative() };
            let t = seam.minus(&a.x).over(&dx);
            if t > Symbolic::zero_value() && t < Symbolic::one_value() {
                self.cuts.push(CutCrossing { edge: EdgeId(start), parameter: t.clone(),
                    level: LevelSource::frozen(a.y.plus(&t.times(&b.y.minus(&a.y)))), forward: dx.sign() });
            }
        }
        let chain = Chain { start: VertexId(start), end: VertexId(end) };
        self.pieces.push(StoredPiece { piece, chain });
        self.len = len;
        Ok(chain)
    }
}

impl<'a> Curve for Programme<'a> {
    type Scalar = Symbolic<'a>;
    const MAX_LEAF_EDGES: usize = 16;
    fn len(&self) -> usize { self.len }
    fn edge_count(&self) -> usize { self.len.saturating_sub(1) }
    fn vertex(&self, vertex: VertexId) -> Cow<'_, Point<Self::Scalar>> {
        assert!(vertex.0 < self.len, "programme vertex out of range");
        if vertex.0 == self.len - 1 {
            return Cow::Owned(self.endpoint(&self.pieces.last().unwrap().piece, true));
        }
        Cow::Owned(self.edge_point(EdgeId(vertex.0), &Symbolic::zero_value()))
    }
    fn edge_y_sign(&self, edge: EdgeId) -> Ordering {
        self.edge_tangent(edge, &Symbolic::zero_value()).y.sign()
    }
    fn turn(&self, vertex: VertexId) -> Ordering {
        assert!(vertex.0 > 0 && vertex.0 + 1 < self.len, "turn requires an interior vertex");
        let incoming = self.edge_tangent(EdgeId(vertex.0 - 1), &Symbolic::one_value());
        let outgoing = self.edge_tangent(EdgeId(vertex.0), &Symbolic::zero_value());
        incoming.x.times(&outgoing.y).minus(&incoming.y.times(&outgoing.x)).sign()
    }
    fn horizontal_hit(&self, edge: EdgeId, level: &Self::Scalar) -> Option<(Self::Scalar, Self::Scalar)> {
        let a = self.edge_point(edge, &Symbolic::zero_value());
        let b = self.edge_point(edge, &Symbolic::one_value());
        if level < std::cmp::min(&a.y, &b.y) || level > std::cmp::max(&a.y, &b.y) { return None; }
        let t = level.minus(&a.y).over(&b.y.minus(&a.y));
        Some((t.clone(), self.edge_point(edge, &t).x))
    }
    fn edge_point(&self, edge: EdgeId, t: &Self::Scalar) -> Point<Self::Scalar> {
        let stored = &self.pieces[self.piece_index(edge)];
        if let Some(alias) = Self::alias_at(&stored.piece, edge.0 - stored.chain.start.0) {
            let root_t = alias.start.plus(&t.times(&alias.end.minus(&alias.start)));
            return self.views[alias.view].edge_point(alias.edge, &root_t);
        }
        match &stored.piece {
            Piece::Finite { start, end } => {
                let p = interpolate(start, end, t);
                Point::new(compact(&p.x), p.y)
            },
            Piece::Projective { start, end, winding } => {
                if t.is_zero_value() { return start.clone(); }
                if t.compare_one() == Ordering::Equal { return end.clone(); }
                let p = interpolate(start, &unwrapped_end(end, *winding), t);
                Point::new(fold(p.x), p.y)
            },
            Piece::Alias { .. } => unreachable!(),
        }
    }
    fn edge_tangent(&self, edge: EdgeId, t: &Self::Scalar) -> Point<Self::Scalar> {
        let stored = &self.pieces[self.piece_index(edge)];
        if let Some(alias) = Self::alias_at(&stored.piece, edge.0 - stored.chain.start.0) {
            let interval = alias.end.minus(&alias.start);
            let root_t = alias.start.plus(&t.times(&interval));
            let tangent = self.views[alias.view].edge_tangent(alias.edge, &root_t);
            return Point::new(tangent.x.times(&interval), tangent.y.times(&interval));
        }
        match &stored.piece {
            Piece::Finite { start, end } => {
                let x = start.x.plus(&t.times(&end.x.minus(&start.x)));
                let denominator = Symbolic::one_value().plus(&x.absolute());
                Point::new(end.x.minus(&start.x).over(&denominator.times(&denominator)), end.y.minus(&start.y))
            },
            Piece::Projective { start, end, winding } => {
                Point::new(unwrapped_end(end, *winding).x.minus(&start.x), end.y.minus(&start.y))
            },
            Piece::Alias { .. } => unreachable!(),
        }
    }
    fn cut_crossings(&self) -> &[CutCrossing<Self::Scalar>] { &self.cuts }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geometry::Rational;
    use crate::input::Input;

    fn number(value: i64) -> Symbolic<'static> {
        Symbolic::owned(Rational::from_integer(value.into()))
    }
    fn fraction(numerator: i64, denominator: i64) -> Symbolic<'static> {
        Symbolic::owned(Rational::new(numerator.into(), denominator.into()))
    }
    fn point(x: i64, y: i64) -> Point<Symbolic<'static>> {
        Point::new(number(x), number(y))
    }

    #[test]
    fn long_aliases_keep_one_descriptor_and_reverse_clipping() {
        let points: Vec<_> = (0..4097).map(|i| Point::integer(i, i)).collect();
        let input = Input::open(&points).unwrap();
        let view = OffsetView::new(&input, Symbolic::variable(0), Symbolic::variable(1));
        let last = EdgeId(input.edge_count() - 1);
        let low = fraction(1, 4);
        let high = fraction(3, 4);
        let beginning = view.edge_point(EdgeId(0), &low);
        let ending = view.edge_point(last, &high);
        let mut programme = Programme::new(vec![view]);
        let forward = programme.append(Piece::Alias {
            view: 0, first: EdgeId(0), last, start: low.clone(), end: high.clone(), reverse: false,
        }).unwrap();
        assert_eq!(programme.pieces.len(), 1);
        assert_eq!(programme.len(), input.edge_count() + 1);
        assert_eq!(programme.vertex(forward.start).as_ref(), &beginning);
        assert_eq!(programme.vertex(forward.end).as_ref(), &ending);
        let backward = programme.append(Piece::Alias {
            view: 0, first: last, last: EdgeId(0), start: high.clone(), end: low.clone(), reverse: true,
        }).unwrap();
        assert_eq!(forward.end, backward.start);
        assert_eq!(programme.pieces.len(), 2);
        assert_eq!(programme.len(), input.edge_count() * 2 + 1);
        assert_eq!(programme.vertex(backward.end).as_ref(), &beginning);
        let first_reverse = programme.alias_edge(EdgeId(backward.start.0)).unwrap();
        assert_eq!(first_reverse.edge, last);
        assert!(first_reverse.reverse);
        assert_eq!(first_reverse.start, high);
        assert_eq!(first_reverse.end, number(0));
        let last_reverse = programme.alias_edge(EdgeId(backward.end.0 - 1)).unwrap();
        assert_eq!(last_reverse.edge, EdgeId(0));
        assert_eq!(last_reverse.start, number(1));
        assert_eq!(last_reverse.end, low);
        let internal = VertexId(backward.start.0 + 1);
        assert_eq!(programme.vertex(internal).as_ref(),
            programme.view(0).vertex(VertexId(last.0)).as_ref());
        let tangent = programme.edge_tangent(EdgeId(backward.start.0), &number(0));
        let expected = programme.view(0).edge_tangent(last, &first_reverse.start);
        let interval = first_reverse.end.minus(&first_reverse.start);
        assert_eq!(tangent, Point::new(expected.x.times(&interval), expected.y.times(&interval)));
        assert_eq!(programme.turn(backward.start), Ordering::Equal);
        assert!(programme.cut_crossings().is_empty());
    }

    #[test]
    fn single_reverse_edge_maps_both_clipped_endpoints() {
        let input = Input::open(&[Point::integer(0, 0), Point::integer(8, 2)]).unwrap();
        let view = OffsetView::new(&input, Symbolic::variable(0), Symbolic::variable(1));
        let start = fraction(4, 5);
        let end = fraction(1, 5);
        let midpoint = view.edge_point(EdgeId(0), &fraction(1, 2));
        let mut programme = Programme::new(vec![view]);
        programme.append(Piece::Alias {
            view: 0, first: EdgeId(0), last: EdgeId(0), start, end, reverse: true,
        }).unwrap();
        assert_eq!(programme.edge_point(EdgeId(0), &fraction(1, 2)), midpoint);
        assert_eq!(programme.edge_y_sign(EdgeId(0)), Ordering::Less);
        let level = midpoint.y;
        assert_eq!(programme.horizontal_hit(EdgeId(0), &level).unwrap().0, fraction(1, 2));
    }

    #[test]
    fn finite_contacts_and_tangents_are_not_compact_secants() {
        let mut programme = Programme::new(vec![]);
        programme.append(Piece::Finite { start: point(0, 0), end: point(4, 2) }).unwrap();
        assert_eq!(programme.horizontal_hit(EdgeId(0), &number(1)),
            Some((fraction(1, 2), fraction(2, 3))));
        assert_ne!(fraction(2, 3), fraction(2, 5));
        assert_eq!(programme.edge_tangent(EdgeId(0), &fraction(1, 2)),
            Point::new(fraction(4, 9), number(2)));
        programme.append(Piece::Finite { start: point(4, 2), end: point(3, 4) }).unwrap();
        assert_eq!(programme.len(), 3);
        assert_eq!(programme.turn(VertexId(1)), Ordering::Greater);
        assert_eq!(programme.piece_index(EdgeId(1)), 1);
        assert!(programme.alias_edge(EdgeId(1)).is_none());
    }

    #[test]
    fn projective_route_crosses_once_without_a_seam_vertex() {
        let mut programme = Programme::new(vec![]);
        let a = Point::new(fraction(3, 4), number(0));
        let b = Point::new(fraction(-3, 4), number(4));
        programme.append(Piece::Projective { start: a.clone(), end: b.clone(), winding: 1 }).unwrap();
        assert_eq!(programme.len(), 2);
        assert_eq!(programme.vertex(VertexId(0)).as_ref(), &a);
        assert_eq!(programme.vertex(VertexId(1)).as_ref(), &b);
        assert_eq!(programme.horizontal_hit(EdgeId(0), &number(3)),
            Some((fraction(3, 4), fraction(-7, 8))));
        assert_eq!(programme.edge_tangent(EdgeId(0), &fraction(3, 4)),
            Point::new(fraction(1, 2), number(4)));
        let cuts = programme.cut_crossings();
        assert_eq!(cuts.len(), 1);
        assert_eq!(cuts[0].edge, EdgeId(0));
        assert_eq!(cuts[0].parameter, fraction(1, 2));
        assert_eq!(cuts[0].forward, Ordering::Greater);
        assert!(matches!(cuts[0].level, LevelSource::Frozen(_)));
        assert_eq!(programme.level(&cuts[0].level).as_ref(), &number(2));
        programme.append(Piece::Projective { start: b, end: a, winding: -1 }).unwrap();
        assert_eq!(programme.len(), 3);
        assert_eq!(programme.cut_crossings().len(), 2);
        assert_eq!(programme.cut_crossings()[1].forward, Ordering::Less);
        assert_eq!(programme.turn(VertexId(1)), Ordering::Equal);
    }

    #[test]
    fn joined_piece_turn_uses_endpoint_derivative_not_secant() {
        let mut programme = Programme::new(vec![]);
        programme.append(Piece::Finite { start: point(0, 0), end: point(4, 2) }).unwrap();
        programme.append(Piece::Projective {
            start: Point::new(fraction(4, 5), number(2)),
            end: Point::new(fraction(9, 10), number(3)),
            winding: 0,
        }).unwrap();
        assert_eq!(programme.turn(VertexId(1)), Ordering::Less);
        assert_eq!(programme.edge_tangent(EdgeId(0), &number(1)),
            Point::new(fraction(4, 25), number(2)));
        assert_eq!(programme.horizontal_hit(EdgeId(1), &fraction(5, 2)),
            Some((fraction(1, 2), fraction(17, 20))));
        assert!(programme.cut_crossings().is_empty());
    }

    #[test]
    fn clipping_connectivity_and_winding_errors_leave_storage_unchanged() {
        let input = Input::open(&[Point::integer(0, 0), Point::integer(2, 1)]).unwrap();
        let mut programme = Programme::new(vec![OffsetView::new(&input, number(0), number(0))]);
        assert_eq!(programme.append(Piece::Alias {
            view: 0, first: EdgeId(0), last: EdgeId(0), start: number(1), end: number(0), reverse: false,
        }), Err(ProgrammeError::InvalidClipping));
        assert_eq!(programme.append(Piece::Alias {
            view: 0, first: EdgeId(input.edge_count()), last: EdgeId(0),
            start: number(1), end: number(0), reverse: true,
        }), Err(ProgrammeError::OutsideView));
        assert_eq!(programme.append(Piece::Finite { start: point(0, 0), end: point(2, 0) }),
            Err(ProgrammeError::Horizontal));
        assert_eq!(programme.append(Piece::Projective { start: point(0, 0), end: point(1, 1), winding: 1 }),
            Err(ProgrammeError::InvalidWinding));
        assert_eq!(programme.len(), 0);
        programme.append(Piece::Finite { start: point(0, 0), end: point(2, 1) }).unwrap();
        assert_eq!(programme.append(Piece::Finite { start: point(3, 1), end: point(4, 2) }),
            Err(ProgrammeError::Disconnected));
        assert_eq!(programme.len(), 2);
        assert_eq!(programme.pieces.len(), 1);
        assert!(programme.cut_crossings().is_empty());
    }
}
