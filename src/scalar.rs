//! Arithmetic shared by rational input geometry and bounded local symbolic views.
use crate::geometry::Rational;
use std::cmp::Ordering;
use std::fmt::Debug;

/// Ordered-field operations; arithmetic bit costs are not unit-cost RAM work.
/// Borrowed operands avoid copying exact coefficients merely to perform an operation.
pub trait ExactScalar: Clone + Debug + Eq + Ord {
    /// Contacts over formal variables must be re-evaluated from their normalized
    /// support and level source, rather than nesting earlier intersections.
    const REBASE_SOURCE_CONTACTS: bool = false;
    fn zero_value() -> Self;
    fn one_value() -> Self;
    fn from_usize_value(value: usize) -> Self;
    fn plus(&self, other: &Self) -> Self;
    fn minus(&self, other: &Self) -> Self;
    fn times(&self, other: &Self) -> Self;
    fn over(&self, other: &Self) -> Self;
    fn negative(&self) -> Self;
    fn sign(&self) -> Ordering;
    fn compare_one(&self) -> Ordering;
    fn absolute(&self) -> Self {
        if self.sign() == Ordering::Less { self.negative() } else { self.clone() }
    }
    fn is_zero_value(&self) -> bool { self.sign() == Ordering::Equal }
}

impl ExactScalar for Rational {
    fn zero_value() -> Self { Self::from_integer(0.into()) }
    fn one_value() -> Self { Self::from_integer(1.into()) }
    fn from_usize_value(value: usize) -> Self { Self::from_integer(value.into()) }
    fn plus(&self, other: &Self) -> Self { self + other }
    fn minus(&self, other: &Self) -> Self { self - other }
    fn times(&self, other: &Self) -> Self { self * other }
    fn over(&self, other: &Self) -> Self { self / other }
    fn negative(&self) -> Self { -self }
    fn sign(&self) -> Ordering { self.numer().cmp(&0.into()) }
    fn compare_one(&self) -> Ordering { self.numer().cmp(self.denom()) }
}
