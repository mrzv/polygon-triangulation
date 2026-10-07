//! Finite ribbon flags realizing the common-vertex deformation in §3.1.
//!
//! Source identities and old-cap contact identities are different operations:
//! inside sources acquire the intrinsic null partner, whereas remote contacts
//! attach to the direction-preserving outside connector. No epsilon is stored.

use crate::boundary::{Boundary, BoundaryError, Chain, Side, Site, Slot};
use crate::curve::Curve;
use crate::input::{Input, VertexId};
use crate::submap::{MapError, RegionId, Submap};
use crate::work::Work;
use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Scope { First, Second }
impl Scope {
    pub fn index(self) -> usize { match self { Self::First => 0, Self::Second => 1 } }
    pub fn opposite(self) -> Self { match self { Self::First => Self::Second, Self::Second => Self::First } }
}
#[derive(Debug)]
pub(crate) enum CapError { Boundary(BoundaryError), Map(MapError), InvalidJoin, InvalidTurn, InvalidCapRegion }
impl fmt::Display for CapError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") }
}
impl std::error::Error for CapError {}
impl From<BoundaryError> for CapError { fn from(e: BoundaryError) -> Self { Self::Boundary(e) } }
impl From<MapError> for CapError { fn from(e: MapError) -> Self { Self::Map(e) } }

pub(crate) struct Join<'a, C: Curve = Input> {
    union: Boundary<'a, C>, scopes: [Boundary<'a, C>; 2], common: VertexId,
    incoming: Ordering, outgoing: Ordering, turn: Ordering,
}
impl<C: Curve> Copy for Join<'_, C> {}
impl<C: Curve> Clone for Join<'_, C> {
    fn clone(&self) -> Self { *self }
}
impl<'a, C: Curve> Join<'a, C> {
    pub fn new(left: &Submap<'a, C>, right: &Submap<'a, C>, work: &mut Work) -> Result<Self, CapError> {
        if !std::ptr::eq(left.input(), right.input()) || left.chain().end != right.chain().start {
            return Err(CapError::InvalidJoin);
        }
        let input = left.input();
        let common = left.chain().end;
        let union = Boundary::new(input, Chain::new(input, left.chain().start, right.chain().end)?)?;
        let incoming = input.edge_y_sign(crate::input::EdgeId(common.0 - 1));
        let outgoing = input.edge_y_sign(crate::input::EdgeId(common.0));
        work.predicates += 1;
        let turn = input.turn(common);
        if incoming != outgoing && turn == Ordering::Equal { return Err(CapError::InvalidTurn); }
        Ok(Self { union, scopes: [Boundary::new(input, left.chain())?, Boundary::new(input, right.chain())?],
            common, incoming, outgoing, turn })
    }
    pub fn boundary(self) -> Boundary<'a, C> { self.union }
    pub fn scope(self, scope: Scope) -> Boundary<'a, C> { self.scopes[scope.index()] }
    pub fn common(self) -> VertexId { self.common }

    /// Actual source identity. Only the join endpoint changes its slot.
    pub fn source_site(self, scope: Scope, old: Site<C::Scalar>) -> Result<Site<C::Scalar>, CapError> {
        self.scope(scope).validate_site(&old)?;
        if matches!(&old, Site::Vertex { vertex, .. } if *vertex == self.common) {
            Ok(self.union.remap_site(&self.scope(scope), &old)?)
        } else { Ok(old) }
    }

    /// Query interpretation of an old endpoint cap, never a null-source remap.
    pub fn contact_site(self, scope: Scope, old: Site<C::Scalar>) -> Result<Site<C::Scalar>, CapError> {
        let boundary = self.scope(scope);
        boundary.validate_site(&old)?;
        if !matches!(&old, Site::Vertex { vertex, .. } if *vertex == self.common) || self.incoming == self.outgoing {
            return self.source_site(scope, old);
        }
        let side = if self.turn == Ordering::Greater { Side::Right } else { Side::Left };
        let incoming = Site::Vertex { vertex: self.common, side, slot: Slot::Incoming };
        let slot = if self.union.direction(&incoming)? == boundary.direction(&old)? { Slot::Incoming } else { Slot::Outgoing };
        Ok(Site::Vertex { vertex: self.common, side, slot })
    }

    pub fn first_source(self, scope: Scope) -> Result<Site<C::Scalar>, CapError> {
        let side = if scope == Scope::First { Side::Right } else { Side::Left };
        self.source_site(scope, Site::Vertex { vertex: self.common, side, slot: Slot::Single })
    }

    /// Old target region entered by the outgoing clockwise source-curve germ.
    /// Source First departs into -u; source Second departs into w. Both cases
    /// select cap for equal Y signs, Left for positive extreme turn, Right for
    /// negative extreme turn. The target's side labels use forward input edges.
    pub fn germ_region(self, source: Scope, target: &Submap<'a, C>) -> Result<RegionId, CapError> {
        let expected = self.scope(source.opposite());
        if !std::ptr::eq(expected.input(), target.input()) || expected.chain() != target.chain() {
            return Err(CapError::InvalidJoin);
        }
        let arcs = target.end_incident_arcs(self.common)?;
        let (left, right, cap, other_cap) = if source == Scope::First {
            (arcs[0][1], arcs[1][0], arcs[0][0], arcs[1][1])
        } else {
            (arcs[0][0], arcs[1][1], arcs[0][1], arcs[1][0])
        };
        if target.arc_region(cap)? != target.arc_region(other_cap)? { return Err(CapError::InvalidCapRegion); }
        let selected = if self.incoming == self.outgoing { cap }
            else if self.turn == Ordering::Greater { left } else { right };
        Ok(target.arc_region(selected)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::base::full_visibility;
    use crate::geometry::Point;
    use crate::input::Input;

    #[test]
    fn all_rotations_preserve_contact_direction_but_not_inside_source_role() {
        for s in [-1i64, 1] { for t in [-1i64, 1] { for turn in [-1i64, 0, 1] {
            if s != t && turn == 0 { continue; }
            let points = [Point::integer(0, -s), Point::integer(0, 0), Point::integer(-s * turn, t)];
            let input = Input::open(&points).unwrap();
            let mut work = Work::default();
            let left = full_visibility(Boundary::new(&input, Chain::new(&input, VertexId(0), VertexId(1)).unwrap()).unwrap(), &mut work).unwrap();
            let right = full_visibility(Boundary::new(&input, Chain::new(&input, VertexId(1), VertexId(2)).unwrap()).unwrap(), &mut work).unwrap();
            let join = Join::new(&left, &right, &mut work).unwrap();
            for scope in [Scope::First, Scope::Second] { for side in [Side::Left, Side::Right] {
                let old = Site::Vertex { vertex: join.common(), side, slot: Slot::Single };
                let direction = join.scope(scope).direction(&old).unwrap();
                let source = join.source_site(scope, old.clone()).unwrap();
                let contact = join.contact_site(scope, old).unwrap();
                assert_eq!(join.boundary().direction(&contact).unwrap(), direction);
                assert!(!join.boundary().inside_null_pair(&contact).unwrap());
                if s == t {
                    assert_eq!(source, contact);
                } else {
                    let inside = if turn > 0 { Side::Left } else { Side::Right };
                    assert_eq!(join.boundary().inside_null_pair(&source).unwrap(), side == inside);
                    assert_eq!(matches!(contact, Site::Vertex { side: actual, .. } if actual != inside), true);
                    if side == inside { assert_ne!(source, contact); }
                }
            }}
            for (source, target) in [(Scope::First, &right), (Scope::Second, &left)] {
                let arcs = target.end_incident_arcs(join.common()).unwrap();
                let expected = if s == t {
                    if source == Scope::First { arcs[0][0] } else { arcs[0][1] }
                } else if turn > 0 {
                    if source == Scope::First { arcs[0][1] } else { arcs[0][0] }
                } else {
                    if source == Scope::First { arcs[1][0] } else { arcs[1][1] }
                };
                assert_eq!(join.germ_region(source, target).unwrap(), target.arc_region(expected).unwrap());
            }
        }}}
    }

    #[test]
    fn removed_endpoint_chords_keep_constant_time_cap_regions() {
        let input = Input::open(&[Point::integer(0, -1), Point::integer(0, 0), Point::integer(-1, -1)]).unwrap();
        let mut work = Work::default();
        let left_boundary = Boundary::new(&input, Chain::new(&input, VertexId(0), VertexId(1)).unwrap()).unwrap();
        let right_boundary = Boundary::new(&input, Chain::new(&input, VertexId(1), VertexId(2)).unwrap()).unwrap();
        let mut left = full_visibility(left_boundary, &mut work).unwrap();
        let mut right = full_visibility(right_boundary, &mut work).unwrap();
        left.coarsen(&left_boundary, 2, &mut work).unwrap();
        right.coarsen(&right_boundary, 2, &mut work).unwrap();
        let join = Join::new(&left, &right, &mut work).unwrap();
        assert_eq!(join.germ_region(Scope::First, &right).unwrap(), right.region_ids().next().unwrap());
        assert_eq!(join.germ_region(Scope::Second, &left).unwrap(), left.region_ids().next().unwrap());
        assert!(join.boundary().null_contact(&join.first_source(Scope::Second).unwrap()).unwrap().is_some());
    }
}
