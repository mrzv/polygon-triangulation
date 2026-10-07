//! Exact finite-chart geometry. Horizontal infinity is represented by a route,
//! never by a synthetic coordinate.
use num_rational::BigRational;
use crate::scalar::ExactScalar;
use std::cmp::Ordering;

pub type Rational = BigRational;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Point<S = Rational> {
    pub x: S,
    pub y: S,
}

impl<S> Point<S> {
    pub fn new(x: S, y: S) -> Self { Self { x, y } }
}

impl Point {
    pub fn integer(x: i64, y: i64) -> Self {
        Self::new(Rational::from_integer(x.into()), Rational::from_integer(y.into()))
    }
}

pub fn orientation<S: ExactScalar>(a: &Point<S>, b: &Point<S>, c: &Point<S>) -> Ordering {
    b.x.minus(&a.x).times(&c.y.minus(&a.y))
        .minus(&b.y.minus(&a.y).times(&c.x.minus(&a.x))).sign()
}

/// Closed-edge intersection. The caller must supply a nonhorizontal edge.
pub fn horizontal_hit<S: ExactScalar>(a: &Point<S>, b: &Point<S>, level: &S) -> Option<(S, S)> {
    assert_ne!(a.y, b.y, "horizontal_hit requires a nonhorizontal edge");
    if level < std::cmp::min(&a.y, &b.y) || level > std::cmp::max(&a.y, &b.y) {
        return None;
    }
    let t = level.minus(&a.y).over(&b.y.minus(&a.y));
    let x = a.x.plus(&t.times(&b.x.minus(&a.x)));
    Some((t, x))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Direction { Left, Right }
impl Direction {
    pub fn opposite(self) -> Self { match self { Self::Left => Self::Right, Self::Right => Self::Left } }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Route { Finite, Wrap, Null }

/// Contact order on the horizontal circle: strict finite contacts precede
/// wrapping contacts, including a different occurrence at the source X.
pub fn ray_order<S: Ord>(source: &S, direction: Direction, a: &S, b: &S) -> Ordering {
    let finite = |x: &S| match direction { Direction::Left => x < source, Direction::Right => x > source };
    match finite(b).cmp(&finite(a)) {
        Ordering::Equal => match direction { Direction::Right => a.cmp(b), Direction::Left => b.cmp(a) },
        order => order,
    }
}

pub fn contact_route<S: Ord>(source: &S, target: &S, direction: Direction) -> Route {
    if match direction { Direction::Left => target < source, Direction::Right => target > source } {
        Route::Finite
    } else { Route::Wrap }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;
    #[test]
    fn exact_clipping_and_circular_contact_order() {
        let a = Point::integer(0, 0);
        let b = Point::integer(3, 2);
        let (t, x) = horizontal_hit(&a, &b, &Rational::from_integer(1.into())).unwrap();
        assert_eq!(t, Rational::new(1.into(), 2.into()));
        assert_eq!(x, Rational::new(3.into(), 2.into()));
        assert!(horizontal_hit(&a, &b, &Rational::from_integer(3.into())).is_none());
        let zero = Rational::zero();
        assert_eq!(ray_order(&zero, Direction::Right, &x, &zero), Ordering::Less);
        assert_eq!(contact_route(&zero, &zero, Direction::Right), Route::Wrap);
        assert_eq!(orientation(&a, &b, &Point::integer(4, 3)), Ordering::Greater);
    }
}
