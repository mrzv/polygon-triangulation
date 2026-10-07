//! Exact rational functions in a fixed hierarchy of positive infinitesimals.
//!
//! `variable(i + 1)` is smaller than every positive power of `variable(i)`.
//! Sparse monomials are ordered by exponents from the last variable to the first;
//! the smallest exponent vector supplies a polynomial's leading coefficient.
//! Fractions need no polynomial gcd: equality clears denominators exactly, and
//! the residue compares leading monomials after common monomial cancellation.
//! Expression size and coefficient/exponent bit costs are not constant-time.
use crate::geometry::Rational;
use crate::scalar::ExactScalar;
use num_bigint::BigUint;
use num_traits::{One, ToPrimitive, Zero};
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;
use std::rc::Rc;
use std::sync::{Arc, LazyLock};

pub const MAX_VARIABLES: usize = 128;

static ZERO: LazyLock<Rational> = LazyLock::new(Rational::zero);
static ONE: LazyLock<Rational> = LazyLock::new(Rational::one);

/// The two possible failures of taking a finite hierarchical residue.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitError {
    PositiveInfinity,
    NegativeInfinity,
}

impl fmt::Display for LimitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::PositiveInfinity => "positive nonfinite symbolic limit",
            Self::NegativeInfinity => "negative nonfinite symbolic limit",
        })
    }
}

impl std::error::Error for LimitError {}

/// Input coefficients can borrow coordinates; computed coefficients are shared.
#[derive(Clone, Debug)]
enum Coefficient<'a> {
    Zero,
    One,
    Borrowed(&'a Rational),
    Shared(Arc<Rational>),
    Retained(Rc<Rational>),
}

impl<'a> Coefficient<'a> {
    fn owned(value: Rational) -> Self {
        if value.is_zero() {
            Self::Zero
        } else if value.is_one() {
            Self::One
        } else {
            Self::Shared(Arc::new(value))
        }
    }

    fn value(&self) -> &Rational {
        match self {
            Self::Zero => &ZERO,
            Self::One => &ONE,
            Self::Borrowed(value) => value,
            Self::Shared(value) => value,
            Self::Retained(value) => value,
        }
    }

    fn is_zero(&self) -> bool { self.value().is_zero() }
    fn is_one(&self) -> bool { self.value().is_one() }
    fn sign(&self) -> Ordering { self.value().numer().cmp(&0.into()) }

    fn plus(&self, other: &Self) -> Self {
        if self.is_zero() { return other.clone(); }
        if other.is_zero() { return self.clone(); }
        Self::owned(self.value() + other.value())
    }

    fn minus(&self, other: &Self) -> Self {
        if other.is_zero() { return self.clone(); }
        if self.value() == other.value() { return Self::Zero; }
        if self.is_zero() { return other.negative(); }
        Self::owned(self.value() - other.value())
    }

    fn times(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() { return Self::Zero; }
        if self.is_one() { return other.clone(); }
        if other.is_one() { return self.clone(); }
        Self::owned(self.value() * other.value())
    }

    fn over(&self, other: &Self) -> Self {
        assert!(!other.is_zero(), "division by zero in symbolic field");
        if self.is_zero() { return Self::Zero; }
        if other.is_one() { return self.clone(); }
        if self.value() == other.value() { return Self::One; }
        Self::owned(self.value() / other.value())
    }

    fn negative(&self) -> Self {
        if self.is_zero() { return Self::Zero; }
        Self::owned(-self.value())
    }
}

/// Bounded local programs keep degrees inline. Only overflow promotes an
/// exponent, preserving exact field behavior even for deeper external programs.
/// A promoted exponent is canonical (strictly greater than `u32::MAX`).
#[derive(Clone, Debug, PartialEq, Eq)]
enum Exponent {
    Small(u32),
    Large(Arc<BigUint>),
}

impl Exponent {
    fn from_big(value: BigUint) -> Self {
        match value.to_u32() {
            Some(value) => Self::Small(value),
            None => Self::Large(Arc::new(value)),
        }
    }

    fn is_zero(&self) -> bool { matches!(self, Self::Small(0)) }

    fn plus(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Small(a), Self::Small(b)) => match a.checked_add(*b) {
                Some(value) => Self::Small(value),
                None => Self::Large(Arc::new(BigUint::from(*a) + *b)),
            },
            (Self::Large(a), Self::Small(b)) => Self::Large(Arc::new(a.as_ref() + *b)),
            (Self::Small(a), Self::Large(b)) => Self::Large(Arc::new(b.as_ref() + *a)),
            (Self::Large(a), Self::Large(b)) => Self::Large(Arc::new(a.as_ref() + b.as_ref())),
        }
    }

    fn minus(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Small(a), Self::Small(b)) => Self::Small(a.checked_sub(*b).expect("monomial factor must divide")),
            (Self::Large(a), Self::Small(b)) => Self::from_big(a.as_ref() - *b),
            (Self::Large(a), Self::Large(b)) => Self::from_big(a.as_ref() - b.as_ref()),
            (Self::Small(_), Self::Large(_)) => panic!("monomial factor must divide"),
        }
    }
}

impl Ord for Exponent {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Small(a), Self::Small(b)) => a.cmp(b),
            (Self::Small(_), Self::Large(_)) => Ordering::Less,
            (Self::Large(_), Self::Small(_)) => Ordering::Greater,
            (Self::Large(a), Self::Large(b)) => a.cmp(b),
        }
    }
}

impl PartialOrd for Exponent {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

/// Sorted, nonzero powers with inline degrees and exact overflow promotion.
/// The empty monomial needs no allocation.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Monomial(Option<Arc<[(u8, Exponent)]>>);

impl Monomial {
    fn powers(&self) -> &[(u8, Exponent)] { self.0.as_deref().unwrap_or(&[]) }
    fn is_one(&self) -> bool { self.0.is_none() }

    fn from_powers(powers: Vec<(u8, Exponent)>) -> Self {
        if powers.is_empty() { Self::default() } else { Self(Some(powers.into())) }
    }

    fn variable(index: usize) -> Self {
        assert!(index < MAX_VARIABLES, "symbolic variable index exceeds MAX_VARIABLES");
        Self::from_powers(vec![(index as u8, Exponent::Small(1))])
    }

    fn times(&self, other: &Self) -> Self {
        if self.is_one() { return other.clone(); }
        if other.is_one() { return self.clone(); }
        let mut powers = Vec::with_capacity(self.powers().len() + other.powers().len());
        let mut left = self.powers().iter().peekable();
        let mut right = other.powers().iter().peekable();
        while let (Some(a), Some(b)) = (left.peek(), right.peek()) {
            match a.0.cmp(&b.0) {
                Ordering::Less => powers.push(left.next().unwrap().clone()),
                Ordering::Greater => powers.push(right.next().unwrap().clone()),
                Ordering::Equal => {
                    powers.push((a.0, a.1.plus(&b.1)));
                    left.next();
                    right.next();
                }
            }
        }
        powers.extend(left.cloned());
        powers.extend(right.cloned());
        Self::from_powers(powers)
    }

    fn common_factor(&self, other: &Self) -> Self {
        if self.is_one() || other.is_one() { return Self::default(); }
        let mut powers = Vec::with_capacity(self.powers().len().min(other.powers().len()));
        let mut left = self.powers().iter().peekable();
        let mut right = other.powers().iter().peekable();
        while let (Some(a), Some(b)) = (left.peek(), right.peek()) {
            match a.0.cmp(&b.0) {
                Ordering::Less => { left.next(); }
                Ordering::Greater => { right.next(); }
                Ordering::Equal => {
                    powers.push((a.0, std::cmp::min(&a.1, &b.1).clone()));
                    left.next();
                    right.next();
                }
            }
        }
        Self::from_powers(powers)
    }

    /// `factor` must divide this monomial; callers compute it componentwise.
    fn divide_factor(&self, factor: &Self) -> Self {
        if factor.is_one() { return self.clone(); }
        let mut powers = Vec::with_capacity(self.powers().len());
        let mut divisors = factor.powers().iter().peekable();
        for (index, exponent) in self.powers() {
            if divisors.peek().is_some_and(|power| power.0 == *index) {
                let (_, divisor) = divisors.next().unwrap();
                let remainder = exponent.minus(divisor);
                if !remainder.is_zero() { powers.push((*index, remainder)); }
            } else {
                powers.push((*index, exponent.clone()));
            }
        }
        debug_assert!(divisors.next().is_none());
        Self::from_powers(powers)
    }
}

impl Ord for Monomial {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut left = self.powers().iter().rev().peekable();
        let mut right = other.powers().iter().rev().peekable();
        loop {
            match (left.peek(), right.peek()) {
                (None, None) => return Ordering::Equal,
                (Some(_), None) => return Ordering::Greater,
                (None, Some(_)) => return Ordering::Less,
                (Some(a), Some(b)) => match a.0.cmp(&b.0) {
                    Ordering::Less => return Ordering::Less,
                    Ordering::Greater => return Ordering::Greater,
                    Ordering::Equal => {
                        let order = a.1.cmp(&b.1);
                        if order != Ordering::Equal { return order; }
                        left.next();
                        right.next();
                    }
                },
            }
        }
    }
}

impl PartialOrd for Monomial {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

#[derive(Clone, Debug)]
struct Term<'a> {
    monomial: Monomial,
    coefficient: Coefficient<'a>,
}

/// Canonical sparse polynomials: sorted distinct monomials, nonzero coefficients.
/// Constants have no polynomial allocation, including during constant arithmetic.
#[derive(Clone, Debug)]
enum Polynomial<'a> {
    Constant(Coefficient<'a>),
    Terms(Arc<[Term<'a>]>),
}

impl<'a> Polynomial<'a> {
    fn zero() -> Self { Self::Constant(Coefficient::Zero) }
    fn one() -> Self { Self::Constant(Coefficient::One) }

    fn from_terms(terms: Vec<Term<'a>>) -> Self {
        if terms.is_empty() { return Self::zero(); }
        if terms.len() == 1 && terms[0].monomial.is_one() {
            return Self::Constant(terms.into_iter().next().unwrap().coefficient);
        }
        Self::Terms(terms.into())
    }

    fn is_zero(&self) -> bool {
        matches!(self, Self::Constant(coefficient) if coefficient.is_zero())
    }

    fn leading(&self) -> (Monomial, &Coefficient<'a>) {
        match self {
            Self::Constant(coefficient) => (Monomial::default(), coefficient),
            Self::Terms(terms) => (terms[0].monomial.clone(), &terms[0].coefficient),
        }
    }

    fn sign(&self) -> Ordering { self.leading().1.sign() }

    fn terms(&self) -> impl Iterator<Item = Term<'a>> + '_ {
        let (terms, constant): (&[Term<'a>], Option<Term<'a>>) = match self {
            Self::Constant(coefficient) => (&[], (!coefficient.is_zero()).then(|| Term {
                monomial: Monomial::default(), coefficient: coefficient.clone(),
            })),
            Self::Terms(terms) => (terms, None),
        };
        terms.iter().cloned().chain(constant)
    }

    fn same(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Constant(a), Self::Constant(b)) => a.value() == b.value(),
            (Self::Terms(a), Self::Terms(b)) => Arc::ptr_eq(a, b) || (
                a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| {
                    a.monomial == b.monomial && a.coefficient.value() == b.coefficient.value()
                })
            ),
            _ => false,
        }
    }

    fn plus(&self, other: &Self) -> Self {
        if self.is_zero() { return other.clone(); }
        if other.is_zero() { return self.clone(); }
        if let (Self::Constant(a), Self::Constant(b)) = (self, other) {
            return Self::Constant(a.plus(b));
        }
        let mut terms = Vec::new();
        let mut left = self.terms().peekable();
        let mut right = other.terms().peekable();
        while let (Some(a), Some(b)) = (left.peek(), right.peek()) {
            match a.monomial.cmp(&b.monomial) {
                Ordering::Less => terms.push(left.next().unwrap()),
                Ordering::Greater => terms.push(right.next().unwrap()),
                Ordering::Equal => {
                    let coefficient = a.coefficient.plus(&b.coefficient);
                    if !coefficient.is_zero() {
                        terms.push(Term { monomial: a.monomial.clone(), coefficient });
                    }
                    left.next();
                    right.next();
                }
            }
        }
        terms.extend(left);
        terms.extend(right);
        Self::from_terms(terms)
    }

    fn minus(&self, other: &Self) -> Self {
        if self.same(other) { return Self::zero(); }
        if let (Self::Constant(a), Self::Constant(b)) = (self, other) {
            return Self::Constant(a.minus(b));
        }
        self.plus(&other.negative())
    }

    fn times(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() { return Self::zero(); }
        if let Self::Constant(coefficient) = self { return other.scale(coefficient, false); }
        if let Self::Constant(coefficient) = other { return self.scale(coefficient, false); }
        let mut terms: BTreeMap<Monomial, Coefficient<'a>> = BTreeMap::new();
        for a in self.terms() {
            for b in other.terms() {
                let monomial = a.monomial.times(&b.monomial);
                let product = a.coefficient.times(&b.coefficient);
                match terms.entry(monomial) {
                    std::collections::btree_map::Entry::Vacant(entry) => { entry.insert(product); }
                    std::collections::btree_map::Entry::Occupied(mut entry) => {
                        let coefficient = entry.get().plus(&product);
                        if coefficient.is_zero() { entry.remove(); } else { *entry.get_mut() = coefficient; }
                    }
                }
            }
        }
        Self::from_terms(terms.into_iter().map(|(monomial, coefficient)| Term {
            monomial, coefficient,
        }).collect())
    }

    fn negative(&self) -> Self {
        match self {
            Self::Constant(coefficient) => Self::Constant(coefficient.negative()),
            Self::Terms(_) => Self::from_terms(self.terms().map(|term| Term {
                monomial: term.monomial, coefficient: term.coefficient.negative(),
            }).collect()),
        }
    }

    fn scale(&self, coefficient: &Coefficient<'a>, divide: bool) -> Self {
        if divide { assert!(!coefficient.is_zero(), "division by zero in symbolic field"); }
        if coefficient.is_one() { return self.clone(); }
        if self.is_zero() || (!divide && coefficient.is_zero()) { return Self::zero(); }
        let scale = |value: &Coefficient<'a>| {
            if divide { value.over(coefficient) } else { value.times(coefficient) }
        };
        match self {
            Self::Constant(value) => Self::Constant(scale(value)),
            Self::Terms(_) => Self::from_terms(self.terms().map(|term| Term {
                monomial: term.monomial, coefficient: scale(&term.coefficient),
            }).collect()),
        }
    }

    fn common_factor(&self) -> Monomial {
        match self {
            Self::Constant(_) => Monomial::default(),
            Self::Terms(terms) => {
                let mut factor = terms[0].monomial.clone();
                for term in &terms[1..] {
                    if factor.is_one() { break; }
                    factor = factor.common_factor(&term.monomial);
                }
                factor
            }
        }
    }

    fn divide_factor(&self, factor: &Monomial) -> Self {
        if factor.is_one() { return self.clone(); }
        Self::from_terms(self.terms().map(|term| Term {
            monomial: term.monomial.divide_factor(factor), coefficient: term.coefficient,
        }).collect())
    }
}

#[derive(Clone, Debug)]
enum Value<'a> {
    Constant(Coefficient<'a>),
    Fraction { numerator: Polynomial<'a>, denominator: Polynomial<'a> },
}

/// An ordered-field element, with borrowed roots and shared immutable results.
///
/// `Clone` only copies references/Arc handles, never coordinates, exponents, or
/// coefficient vectors. Division by exact zero panics, as for `Rational`.
#[derive(Clone, Debug)]
pub struct Symbolic<'a> {
    value: Value<'a>,
}

impl<'a> Symbolic<'a> {
    pub fn borrowed(value: &'a Rational) -> Self {
        Self { value: Value::Constant(Coefficient::Borrowed(value)) }
    }

    pub fn owned(value: Rational) -> Self {
        Self::constant(Coefficient::owned(value))
    }

    /// Share a retained exact level without copying its rational coefficient.
    pub fn retained(value: Rc<Rational>) -> Self {
        Self::constant(Coefficient::Retained(value))
    }

    pub fn variable(index: usize) -> Self {
        Self {
            value: Value::Fraction {
                numerator: Polynomial::from_terms(vec![Term {
                    monomial: Monomial::variable(index), coefficient: Coefficient::One,
                }]),
                denominator: Polynomial::one(),
            },
        }
    }

    fn constant(coefficient: Coefficient<'a>) -> Self {
        Self { value: Value::Constant(coefficient) }
    }

    fn parts(&self) -> (Polynomial<'a>, Polynomial<'a>) {
        match &self.value {
            Value::Constant(coefficient) => (Polynomial::Constant(coefficient.clone()), Polynomial::one()),
            Value::Fraction { numerator, denominator } => (numerator.clone(), denominator.clone()),
        }
    }

    fn fraction(mut numerator: Polynomial<'a>, mut denominator: Polynomial<'a>) -> Self {
        assert!(!denominator.is_zero(), "division by zero in symbolic field");
        if numerator.is_zero() { return Self::constant(Coefficient::Zero); }
        if numerator.same(&denominator) { return Self::constant(Coefficient::One); }
        let denominator_factor = denominator.common_factor();
        if !denominator_factor.is_one() {
            let common = denominator_factor.common_factor(&numerator.common_factor());
            if !common.is_one() {
                numerator = numerator.divide_factor(&common);
                denominator = denominator.divide_factor(&common);
            }
        }
        if let Polynomial::Constant(coefficient) = &denominator {
            numerator = numerator.scale(coefficient, true);
            denominator = Polynomial::one();
        } else if denominator.sign() == Ordering::Less {
            numerator = numerator.negative();
            denominator = denominator.negative();
        }
        if let (Polynomial::Constant(coefficient), Polynomial::Constant(_)) = (&numerator, &denominator) {
            return Self::constant(coefficient.clone());
        }
        Self { value: Value::Fraction { numerator, denominator } }
    }

    /// The finite residue in the hierarchical infinitesimal ordering.
    ///
    /// In particular, this is not independent substitution of zero into the two
    /// polynomials: common powers and non-monomial factors may make both vanish.
    /// Equal leading monomials give the rational coefficient ratio; a smaller
    /// numerator gives zero, and a larger numerator gives a signed infinity.
    pub fn finite_limit(&self) -> Result<Rational, LimitError> {
        match &self.value {
            Value::Constant(coefficient) => Ok(coefficient.value().clone()),
            Value::Fraction { numerator, denominator } => {
                let (numerator_monomial, numerator_coefficient) = numerator.leading();
                let (denominator_monomial, denominator_coefficient) = denominator.leading();
                match numerator_monomial.cmp(&denominator_monomial) {
                    Ordering::Equal => Ok(numerator_coefficient.value() / denominator_coefficient.value()),
                    Ordering::Greater => Ok(Rational::zero()),
                    Ordering::Less => Err(if numerator.sign() == Ordering::Less {
                        LimitError::NegativeInfinity
                    } else {
                        LimitError::PositiveInfinity
                    }),
                }
            }
        }
    }
}

impl<'a> From<&'a Rational> for Symbolic<'a> {
    fn from(value: &'a Rational) -> Self { Self::borrowed(value) }
}

impl<'a> From<Rational> for Symbolic<'a> {
    fn from(value: Rational) -> Self { Self::owned(value) }
}

impl ExactScalar for Symbolic<'_> {
    const REBASE_SOURCE_CONTACTS: bool = true;
    fn zero_value() -> Self { Self::constant(Coefficient::Zero) }
    fn one_value() -> Self { Self::constant(Coefficient::One) }
    fn from_usize_value(value: usize) -> Self { Self::owned(Rational::from_integer(value.into())) }

    fn plus(&self, other: &Self) -> Self {
        if let (Value::Constant(a), Value::Constant(b)) = (&self.value, &other.value) {
            return Self::constant(a.plus(b));
        }
        if self.is_zero_value() { return other.clone(); }
        if other.is_zero_value() { return self.clone(); }
        let (a, b) = self.parts();
        let (c, d) = other.parts();
        if b.same(&d) { return Self::fraction(a.plus(&c), b); }
        Self::fraction(a.times(&d).plus(&c.times(&b)), b.times(&d))
    }

    fn minus(&self, other: &Self) -> Self {
        if let (Value::Constant(a), Value::Constant(b)) = (&self.value, &other.value) {
            return Self::constant(a.minus(b));
        }
        if other.is_zero_value() { return self.clone(); }
        let (a, b) = self.parts();
        let (c, d) = other.parts();
        if b.same(&d) { return Self::fraction(a.minus(&c), b); }
        Self::fraction(a.times(&d).minus(&c.times(&b)), b.times(&d))
    }

    fn times(&self, other: &Self) -> Self {
        if let (Value::Constant(a), Value::Constant(b)) = (&self.value, &other.value) {
            return Self::constant(a.times(b));
        }
        if self.is_zero_value() || other.is_zero_value() { return Self::zero_value(); }
        if matches!(&self.value, Value::Constant(a) if a.is_one()) { return other.clone(); }
        if matches!(&other.value, Value::Constant(a) if a.is_one()) { return self.clone(); }
        let (a, b) = self.parts();
        let (c, d) = other.parts();
        // Cancel known whole factors before multiplication, not after expansion.
        if a.same(&d) { return Self::fraction(c, b); }
        if b.same(&c) { return Self::fraction(a, d); }
        Self::fraction(a.times(&c), b.times(&d))
    }

    fn over(&self, other: &Self) -> Self {
        assert!(!other.is_zero_value(), "division by zero in symbolic field");
        if let (Value::Constant(a), Value::Constant(b)) = (&self.value, &other.value) {
            return Self::constant(a.over(b));
        }
        if self.is_zero_value() { return Self::zero_value(); }
        if matches!(&other.value, Value::Constant(a) if a.is_one()) { return self.clone(); }
        let (a, b) = self.parts();
        let (c, d) = other.parts();
        if b.same(&d) { return Self::fraction(a, c); }
        if a.same(&c) { return Self::fraction(d, b); }
        Self::fraction(a.times(&d), b.times(&c))
    }

    fn negative(&self) -> Self {
        match &self.value {
            Value::Constant(coefficient) => Self::constant(coefficient.negative()),
            Value::Fraction { numerator, denominator } => Self {
                value: Value::Fraction { numerator: numerator.negative(), denominator: denominator.clone() },
            },
        }
    }

    fn sign(&self) -> Ordering {
        match &self.value {
            Value::Constant(coefficient) => coefficient.sign(),
            Value::Fraction { numerator, .. } => numerator.sign(),
        }
    }

    fn compare_one(&self) -> Ordering {
        match &self.value {
            Value::Constant(coefficient) => coefficient.value().numer().cmp(coefficient.value().denom()),
            Value::Fraction { numerator, denominator } => numerator.minus(denominator).sign(),
        }
    }
}

impl PartialEq for Symbolic<'_> {
    fn eq(&self, other: &Self) -> bool { self.cmp(other) == Ordering::Equal }
}

impl Eq for Symbolic<'_> {}

impl Ord for Symbolic<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        if let (Value::Constant(a), Value::Constant(b)) = (&self.value, &other.value) {
            return a.value().cmp(b.value());
        }
        let (a, b) = self.parts();
        let (c, d) = other.parts();
        if b.same(&d) { return a.minus(&c).sign(); }
        a.times(&d).minus(&c.times(&b)).sign()
    }
}

impl PartialOrd for Symbolic<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn integer(value: i64) -> Symbolic<'static> {
        Symbolic::owned(Rational::from_integer(value.into()))
    }

    fn rational(numerator: i64, denominator: i64) -> Rational {
        Rational::new(numerator.into(), denominator.into())
    }

    #[test]
    fn every_variable_is_positive_and_dominates_later_powers() {
        let zero = Symbolic::zero_value();
        let one = Symbolic::one_value();
        for index in 0..MAX_VARIABLES {
            let variable = Symbolic::variable(index);
            assert!(zero < variable && variable < one);
            assert_eq!(variable.finite_limit(), Ok(Rational::zero()));
            if index + 1 < MAX_VARIABLES {
                let later = Symbolic::variable(index + 1);
                let mut earlier_power = variable.clone();
                // Powers beyond a machine-word exponent still retain exact order.
                for _ in 0..70 { earlier_power = earlier_power.times(&earlier_power); }
                assert!(later < earlier_power);
                assert_eq!(earlier_power.times(&variable).over(&earlier_power), variable);
                assert!(variable > later.times(&later).times(&integer(1_000_000)));
            }
        }
        let first = Symbolic::variable(0);
        let last = Symbolic::variable(MAX_VARIABLES - 1);
        assert!(first.minus(&last).sign() == Ordering::Greater);
        assert!(last.minus(&first).sign() == Ordering::Less);
    }

    #[test]
    fn polynomial_cancellations_and_ordered_field_laws_are_exact() {
        let x = Symbolic::variable(0);
        let y = Symbolic::variable(1);
        let z = Symbolic::variable(127);
        let a = x.plus(&integer(2));
        let b = y.minus(&integer(3));
        let c = z.plus(&integer(5));
        assert_eq!(a.times(&b.plus(&c)), a.times(&b).plus(&a.times(&c)));
        assert_eq!(a.plus(&b).plus(&c), a.plus(&b.plus(&c)));
        assert_eq!(a.times(&b).times(&c), a.times(&b.times(&c)));
        assert_eq!(a.over(&a), Symbolic::one_value());
        assert_eq!(a.plus(&a.negative()), Symbolic::zero_value());
        assert_eq!(a.times(&b).over(&b), a);
        assert_eq!(x.times(&x).minus(&y.times(&y)).over(&x.minus(&y)), x.plus(&y));
        assert_eq!(x.plus(&y).minus(&y).minus(&x).sign(), Ordering::Equal);
        assert!(x.times(&c) > y.times(&c));
        assert!(x.times(&b) < y.times(&b));
    }

    #[test]
    fn equivalent_fractions_compare_by_value_not_representation() {
        let x = Symbolic::variable(0);
        let y = Symbolic::variable(1);
        let common = x.plus(&y);
        let numerator = integer(2).plus(&x);
        let denominator = integer(3).minus(&y);
        let fraction = numerator.over(&denominator);
        let expanded = numerator.times(&common).over(&denominator.times(&common));
        assert_eq!(fraction, expanded);
        assert_eq!(fraction.cmp(&expanded), Ordering::Equal);
        assert_eq!(fraction.minus(&expanded), Symbolic::zero_value());
        assert!(expanded.plus(&y) > fraction);
        assert!(expanded.minus(&y) < fraction);
        let negative_denominator = numerator.negative().over(&denominator.negative());
        assert_eq!(negative_denominator, fraction);
        assert_eq!(negative_denominator.sign(), Ordering::Greater);
        assert_eq!(fraction.compare_one(), Ordering::Less);
    }

    #[test]
    fn contact_limits_are_rational_after_vanishing_denominator_cancellation() {
        let x = Symbolic::variable(0);
        let y = Symbolic::variable(1);
        let common = x.plus(&y);
        let contact = common.times(&integer(7).plus(&x))
            .over(&common.times(&integer(3).minus(&y)));
        assert_eq!(contact.finite_limit(), Ok(rational(7, 3)));
        let fraction = x.times(&integer(3).plus(&y.times(&integer(5))))
            .over(&x.times(&integer(2).plus(&y)));
        assert_eq!(fraction.finite_limit(), Ok(rational(3, 2)));
        let bottom = integer(1).plus(&x);
        let top = integer(4).plus(&y);
        let level = integer(3).plus(&y.times(&integer(2)));
        let parameter = level.minus(&bottom).over(&top.minus(&bottom));
        let contact_x = integer(2).plus(&parameter.times(&integer(9)));
        assert_eq!(parameter.finite_limit(), Ok(rational(2, 3)));
        assert_eq!(contact_x.finite_limit(), Ok(rational(8, 1)));
    }

    #[test]
    fn common_power_zero_over_zero_has_a_finite_exact_residue() {
        let x = Symbolic::variable(0);
        let y = Symbolic::variable(1);
        let power = x.times(&x).times(&y);
        assert_eq!(x.over(&x).finite_limit(), Ok(Rational::one()));
        assert_eq!(power.times(&integer(-5)).over(&power.times(&integer(2))).finite_limit(), Ok(rational(-5, 2)));
        assert_eq!(x.plus(&y).over(&x.plus(&y.times(&integer(2)))).finite_limit(), Ok(Rational::one()));
        assert_eq!(y.over(&x).finite_limit(), Ok(Rational::zero()));
        assert_eq!(power.over(&x).finite_limit(), Ok(Rational::zero()));
        assert_eq!(Symbolic::zero_value().over(&power).finite_limit(), Ok(Rational::zero()));
    }

    #[test]
    fn both_nonfinite_signs_follow_the_hierarchical_order() {
        let x = Symbolic::variable(0);
        let y = Symbolic::variable(1);
        assert_eq!(integer(1).over(&x).finite_limit(), Err(LimitError::PositiveInfinity));
        assert_eq!(integer(-1).over(&x).finite_limit(), Err(LimitError::NegativeInfinity));
        assert_eq!(integer(1).over(&x.negative()).finite_limit(), Err(LimitError::NegativeInfinity));
        assert_eq!(x.over(&y).finite_limit(), Err(LimitError::PositiveInfinity));
        assert_eq!(x.negative().over(&y).finite_limit(), Err(LimitError::NegativeInfinity));
    }

    #[test]
    fn large_borrowed_constants_keep_exact_behavior_and_share_storage() {
        let huge = (BigInt::one() << 4096usize) + BigInt::from(12345);
        let rational = Rational::new(huge, BigInt::from(97));
        let borrowed = Symbolic::borrowed(&rational);
        let cloned = borrowed.clone();
        assert_eq!(cloned.finite_limit(), Ok(rational.clone()));
        assert_eq!(borrowed, Symbolic::owned(rational.clone()));
        assert_eq!(borrowed.plus(&integer(7)).minus(&integer(7)), borrowed);
        assert_eq!(borrowed.over(&borrowed), Symbolic::one_value());
        match &cloned.value {
            Value::Constant(Coefficient::Borrowed(value)) => assert!(std::ptr::eq(*value, &rational)),
            _ => panic!("cloning a borrowed constant must preserve the borrow"),
        }
        let computed = borrowed.plus(&integer(7));
        match (&computed.value, &computed.clone().value) {
            (Value::Constant(Coefficient::Shared(a)), Value::Constant(Coefficient::Shared(b))) => assert!(Arc::ptr_eq(a, b)),
            _ => panic!("computed large constants must share their rational storage"),
        }
        let polynomial = borrowed.plus(&Symbolic::variable(0));
        assert_eq!(polynomial.finite_limit(), Ok(rational.clone()));
        match (&polynomial.value, &polynomial.clone().value) {
            (Value::Fraction { numerator: Polynomial::Terms(a), .. }, Value::Fraction { numerator: Polynomial::Terms(b), .. }) => assert!(Arc::ptr_eq(a, b)),
            _ => panic!("cloning polynomials must share their term storage"),
        }
    }

    #[test]
    #[should_panic(expected = "division by zero in symbolic field")]
    fn exact_zero_division_is_rejected_after_cancellation() {
        let x = Symbolic::variable(0);
        let zero = x.times(&integer(2)).minus(&x.plus(&x));
        let _ = integer(1).over(&zero);
    }

    #[test]
    #[should_panic(expected = "symbolic variable index exceeds MAX_VARIABLES")]
    fn variables_are_bounded() { let _ = Symbolic::variable(MAX_VARIABLES); }
}
