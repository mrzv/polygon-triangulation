//! One affine-normalized, padded open input table shared by every curve scope.
//! Simplicity and pairwise vertex distinctness are caller promises.
//! Construction checks local preconditions and nonzero polygon signed area.
use crate::geometry::{Point, Rational, orientation};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VertexId(pub usize);
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EdgeId(pub usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SeamEndpoint { A, B }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VertexSource {
    Original(usize),
    Seam { edge: usize, t: Rational, endpoint: SeamEndpoint },
    Padding { edge: usize, t: Rational },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EdgeSource {
    pub original: usize,
    pub start: Rational,
    pub end: Rational,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InputError {
    TooFewVertices,
    RepeatedVertex { first: usize, second: usize },
    CollinearBacktrack { vertex: usize },
    ZeroArea,
    SizeOverflow,
}
impl fmt::Display for InputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for InputError {}

#[derive(Debug)]
pub struct Input {
    vertices: Vec<Point>,
    sources: Vec<VertexSource>,
    edge_sources: Vec<EdgeSource>,
    edge_y_signs: Vec<Ordering>,
    shear: Rational,
    original_len: usize,
    polygon: bool,
}

impl Input {
    /// Simple polygon with distinct vertices and an implicit closing edge.
    /// Either winding is accepted; do not repeat the first vertex at the end.
    pub fn polygon(points: &[Point]) -> Result<Self, InputError> { Self::construct(points, true) }
    /// Simple open chain with pairwise distinct vertices.
    pub fn open(points: &[Point]) -> Result<Self, InputError> { Self::construct(points, false) }
    pub fn vertex(&self, id: VertexId) -> &Point { &self.vertices[id.0] }
    pub fn len(&self) -> usize { self.vertices.len() }
    pub fn is_empty(&self) -> bool { self.vertices.is_empty() }
    pub fn edge_count(&self) -> usize { self.edge_sources.len() }
    pub fn source(&self, id: VertexId) -> &VertexSource { &self.sources[id.0] }
    pub fn edge_source(&self, id: EdgeId) -> &EdgeSource { &self.edge_sources[id.0] }
    pub fn edge_y_sign(&self, id: EdgeId) -> Ordering { self.edge_y_signs[id.0] }
    pub fn shear_factor(&self) -> &Rational { &self.shear }
    pub fn original_len(&self) -> usize { self.original_len }
    pub fn is_polygon(&self) -> bool { self.polygon }
    pub fn inverse(&self, point: &Point) -> Point {
        Point::new(point.x.clone(), (&point.y - &point.x) / &self.shear)
    }
    /// Relabel a normalized table-edge contact in the caller's original edge.
    pub fn original_contact(&self, edge: EdgeId, t: &Rational) -> (usize, Rational) {
        let source = self.edge_source(edge);
        (source.original, &source.start + t * (&source.end - &source.start))
    }

    fn construct(points: &[Point], polygon: bool) -> Result<Self, InputError> {
        let n = points.len();
        if n < if polygon { 3 } else { 2 } { return Err(InputError::TooFewVertices); }
        let edges = if polygon { n } else { n-1 };
        for first in 0..edges {
            let second = (first+1)%n;
            if points[first] == points[second] {
                return Err(InputError::RepeatedVertex { first: first.min(second), second: first.max(second) });
            }
        }
        for i in 0..n {
            if !polygon && (i == 0 || i + 1 == n) { continue; }
            let a = &points[(i + n - 1) % n];
            let b = &points[i];
            let c = &points[(i + 1) % n];
            if orientation(a, b, c) == Ordering::Equal
                && ((&b.x - &a.x) * (&c.x - &b.x) + (&b.y - &a.y) * (&c.y - &b.y)).is_negative()
            { return Err(InputError::CollinearBacktrack { vertex: i }); }
        }
        if polygon {
            let mut twice_area = Rational::zero();
            for i in 0..n {
                let a = &points[i]; let b = &points[(i + 1) % n];
                twice_area += &a.x * &b.y - &a.y * &b.x;
            }
            if twice_area.is_zero() { return Err(InputError::ZeroArea); }
        }
        let min_x = points.iter().map(|p| &p.x).min().unwrap();
        let max_x = points.iter().map(|p| &p.x).max().unwrap();
        let denominator = points.iter().map(|p| p.y.denom()).max().unwrap();
        let shear = (max_x - min_x + Rational::one())
            * Rational::from_integer(denominator * denominator);
        let transformed: Vec<Point> = points.iter().map(|p| Point::new(p.x.clone(), &shear * &p.y + &p.x)).collect();
        let y0 = transformed[0].y.clone();
        let delta = transformed[1..].iter().map(|p| (&p.y - &y0).abs()).min().unwrap()
            / Rational::from_integer(4.into());
        let dy = &transformed[1].y - &y0;
        let sign = if dy.is_positive() { Rational::one() } else { -Rational::one() };
        let needed_edges = if polygon { n.checked_add(1).ok_or(InputError::SizeOverflow)? } else { n - 1 };
        let edge_count = needed_edges.checked_next_power_of_two().ok_or(InputError::SizeOverflow)?;
        let count = edge_count.checked_add(1).ok_or(InputError::SizeOverflow)?;
        let padding = count - if polygon { n + 2 } else { n };
        let mut vertices = Vec::with_capacity(count);
        let mut sources = Vec::with_capacity(count);
        let mut edge_sources = Vec::with_capacity(edge_count);
        let interpolate = |t: &Rational| Point::new(
            &points[0].x + t * (&points[1].x - &points[0].x),
            &y0 + t * &dy,
        );
        let parameter = |q: Rational| &sign * q / &dy;
        let t_a = polygon.then(|| parameter(&delta / Rational::from_integer(2.into())));
        let mut last_t = Rational::zero();
        let mut transformed = transformed.into_iter();
        let first = transformed.next().unwrap();
        if polygon {
            let t_b = parameter(&delta * Rational::new(3.into(), 4.into()));
            vertices.push(interpolate(&t_b));
            sources.push(VertexSource::Seam { edge: 0, t: t_b.clone(), endpoint: SeamEndpoint::B });
            edge_sources.push(EdgeSource { original: 0, start: t_b, end: Rational::one() });
            for (offset, point) in transformed.by_ref().enumerate() {
                let i = offset + 1;
                vertices.push(point); sources.push(VertexSource::Original(i));
                edge_sources.push(EdgeSource { original: i, start: Rational::zero(), end: Rational::one() });
            }
            vertices.push(first); sources.push(VertexSource::Original(0));
        } else {
            vertices.push(first); sources.push(VertexSource::Original(0));
        }
        let padding_divisor = BigInt::from(if polygon { 4usize } else { 2usize }) * BigInt::from(padding + 1);
        for j in 1..=padding {
            let t = parameter(&delta * Rational::new(BigInt::from(j), padding_divisor.clone()));
            edge_sources.push(EdgeSource { original: 0, start: last_t, end: t.clone() });
            vertices.push(interpolate(&t));
            sources.push(VertexSource::Padding { edge: 0, t: t.clone() });
            last_t = t;
        }
        if polygon {
            let t_a = t_a.unwrap();
            edge_sources.push(EdgeSource { original: 0, start: last_t, end: t_a.clone() });
            vertices.push(interpolate(&t_a));
            sources.push(VertexSource::Seam { edge: 0, t: t_a, endpoint: SeamEndpoint::A });
        } else {
            edge_sources.push(EdgeSource { original: 0, start: last_t, end: Rational::one() });
            for (offset, point) in transformed.enumerate() {
                let i = offset + 1;
                vertices.push(point); sources.push(VertexSource::Original(i));
                if i + 1 < n { edge_sources.push(EdgeSource { original: i, start: Rational::zero(), end: Rational::one() }); }
            }
        }
        let edge_y_signs = vertices.windows(2).map(|pair| pair[1].y.cmp(&pair[0].y)).collect();
        Ok(Self { vertices, sources, edge_sources, edge_y_signs, shear, original_len: n, polygon })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geometry::horizontal_hit;
    use std::collections::HashSet;
    #[test]
    fn equal_levels_are_sheared_without_changing_turns() {
        let points = [Point::integer(0,0), Point::integer(3,0), Point::integer(3,2), Point::integer(0,2)];
        let input = Input::open(&points).unwrap();
        assert_eq!(input.shear_factor(), &Rational::from_integer(4.into()));
        let originals: Vec<_> = (0..input.len()).filter(|&i| matches!(input.source(VertexId(i)), VertexSource::Original(_))).collect();
        for pair in originals.windows(2) { assert_ne!(input.vertex(VertexId(pair[0])).y, input.vertex(VertexId(pair[1])).y); }
        assert_eq!(orientation(&points[0], &points[1], &points[2]), orientation(input.vertex(VertexId(originals[0])), input.vertex(VertexId(originals[1])), input.vertex(VertexId(originals[2]))));
        for i in originals { let VertexSource::Original(original) = input.source(VertexId(i)) else { unreachable!() }; assert_eq!(input.inverse(input.vertex(VertexId(i))), points[*original]); }
    }
    #[test]
    fn seam_and_padding_preserve_original_level_contacts() {
        let points = [Point::integer(0,0), Point::integer(4,0), Point::integer(4,3), Point::integer(2,4), Point::integer(0,3)];
        let input = Input::polygon(&points).unwrap();
        assert_eq!(input.len(), 9);
        let mut levels = HashSet::new();
        let mut originals = HashSet::new();
        for i in 0..input.len() {
            assert!(levels.insert(input.vertex(VertexId(i)).y.clone()));
            if let VertexSource::Original(id) = input.source(VertexId(i)) { originals.insert(*id); }
        }
        assert_eq!(originals.len(), points.len());
        let original_zero = (0..input.len()).find(|&i| input.source(VertexId(i)) == &VertexSource::Original(0)).unwrap();
        let original_one = (0..input.len()).find(|&i| input.source(VertexId(i)) == &VertexSource::Original(1)).unwrap();
        let a = input.vertex(VertexId(original_zero)); let b = input.vertex(VertexId(original_one));
        for i in 0..input.len() {
            if !matches!(input.source(VertexId(i)), VertexSource::Original(_)) { continue; }
            let level = &input.vertex(VertexId(i)).y;
            let expected = horizontal_hit(a,b,level).map(|(_,x)| x);
            let contacts: Vec<_> = (0..input.edge_count()).filter(|&e| input.edge_source(EdgeId(e)).original == 0)
                .filter_map(|e| horizontal_hit(input.vertex(VertexId(e)), input.vertex(VertexId(e+1)),level).map(|(t,x)| (input.original_contact(EdgeId(e),&t).1,x))).collect();
            assert_eq!(contacts.first().map(|(_,x)|x), expected.as_ref());
            for (t,x) in contacts { assert_eq!(x, &a.x + t * (&b.x-&a.x)); }
        }
        assert!(matches!(input.source(VertexId(0)), VertexSource::Seam { endpoint: SeamEndpoint::B, .. }));
        assert!(matches!(input.source(VertexId(input.len()-1)), VertexSource::Seam { endpoint: SeamEndpoint::A, .. }));
    }
    #[test]
    fn invalid_local_geometry_is_not_repaired() {
        assert!(matches!(Input::open(&[Point::integer(0,0),Point::integer(2,0),Point::integer(1,0)]), Err(InputError::CollinearBacktrack { vertex:1 })));
        assert!(matches!(Input::polygon(&[Point::integer(0,0),Point::integer(1,0),Point::integer(2,0)]), Err(InputError::CollinearBacktrack { .. }) | Err(InputError::ZeroArea)));
    }
    #[test]
    fn rational_denominator_bound_preserves_unequal_y_order() {
        let points = [
            Point::new(Rational::from_integer(100.into()),Rational::new(1.into(),11.into())),
            Point::new(Rational::zero(),Rational::new(1.into(),10.into())),
            Point::new(Rational::one(),Rational::new(1.into(),10.into())),
        ];
        let input = Input::open(&points).unwrap();
        assert_eq!(input.shear_factor(),&Rational::from_integer(12221.into()));
        assert!(input.vertex(VertexId(0)).y < input.vertex(VertexId(1)).y);
        assert!(input.vertex(VertexId(1)).y < input.vertex(VertexId(2)).y);
        assert_eq!(orientation(&points[0],&points[1],&points[2]),orientation(input.vertex(VertexId(0)),input.vertex(VertexId(1)),input.vertex(VertexId(2))));
    }
}
