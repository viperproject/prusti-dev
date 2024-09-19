// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::{
    cmp::Ordering,
    fmt::{Debug, Formatter, Result},
    hash::{Hash, Hasher},
    mem::discriminant,
};

use derive_more::{Deref, DerefMut};

use prusti_rustc_interface::middle::mir::{
    Local, Place as MirPlace, PlaceElem, PlaceRef, ProjectionElem,
};

// #[derive(Clone, Copy, Deref, DerefMut, Hash, PartialEq, Eq)]
// pub struct RootPlace<'tcx>(Place<'tcx>);
// impl<'tcx> RootPlace<'tcx> {
//     pub(super) fn new(place: Place<'tcx>) -> Self {
//         assert!(place.projection.last().copied().map(Self::is_indirect).unwrap_or(true));
//         Self(place)
//     }

//     pub fn is_indirect<V, T>(p: ProjectionElem<V, T>) -> bool {
//         match p {
//             ProjectionElem::Deref => true,

//             ProjectionElem::Field(_, _)
//             | ProjectionElem::Index(_)
//             | ProjectionElem::OpaqueCast(_)
//             | ProjectionElem::ConstantIndex { .. }
//             | ProjectionElem::Subslice { .. }
//             | ProjectionElem::Downcast(_, _) => false,
//         }
//     }
// }
// impl Debug for RootPlace<'_> {
//     fn fmt(&self, fmt: &mut Formatter) -> Result {
//         self.0.fmt(fmt)
//     }
// }
// impl From<Local> for RootPlace<'_> {
//     fn from(local: Local) -> Self {
//         Self(local.into())
//     }
// }

#[derive(Clone, Copy, Deref, DerefMut)]
pub struct Place<'tcx>(PlaceRef<'tcx>);

impl<'tcx> Place<'tcx> {
    pub(crate) fn new(local: Local, projection: &'tcx [PlaceElem<'tcx>]) -> Self {
        Self(PlaceRef { local, projection })
    }

    pub(crate) fn compare_projections(
        self,
        other: Self,
    ) -> impl Iterator<Item = (bool, PlaceElem<'tcx>, PlaceElem<'tcx>)> {
        let left = self.projection.iter().copied();
        let right = other.projection.iter().copied();
        left.zip(right).map(|(e1, e2)| (elem_eq((e1, e2)), e1, e2))
    }

    /// Check if the place `left` is a prefix of `right` or vice versa. For example:
    ///
    /// +   `partial_cmp(x.f, y.f) == None`
    /// +   `partial_cmp(x.f, x.g) == None`
    /// +   `partial_cmp(x.f, x.f) == Some(Equal)`
    /// +   `partial_cmp(x.f.g, x.f) == Some(Suffix)`
    /// +   `partial_cmp(x.f, x.f.g) == Some(Prefix)`
    /// +   `partial_cmp(x as None, x as Some.0) == Some(Both)`
    ///
    /// The ultimate question this answers is: are the two places mutually
    /// exclusive (i.e. can we have both or not)?
    /// For example, all of the following are mutually exclusive:
    ///  - `x` and `x.f`
    ///  - `(x as Ok).0` and `(x as Err).0`
    ///  - `x[_1]` and `x[_2]`
    ///  - `x[2 of 11]` and `x[5 of 14]`
    /// But the following are not:
    ///  - `x` and `y`
    ///  - `x.f` and `x.g.h`
    ///  - `x[3 of 6]` and `x[4 of 6]`
    #[tracing::instrument(level = "trace", ret)]
    pub(crate) fn partial_cmp(self, right: Self) -> Option<PlaceOrdering> {
        if self.local != right.local {
            return None;
        }
        let diff = self.compare_projections(right).find(|(eq, _, _)| !eq);
        if let Some((_, left, right)) = diff {
            use ProjectionElem::*;
            fn is_index(elem: PlaceElem<'_>) -> bool {
                matches!(elem, Index(_) | ConstantIndex { .. } | Subslice { .. })
            }
            match (left, right) {
                (Field(..), Field(..)) => None,
                (
                    ConstantIndex {
                        min_length: l,
                        from_end: lfe,
                        ..
                    },
                    ConstantIndex {
                        min_length: r,
                        from_end: rfe,
                        ..
                    },
                ) if r == l && lfe == rfe => None,
                (Downcast(_, _), Downcast(_, _)) | (OpaqueCast(_), OpaqueCast(_)) => {
                    Some(PlaceOrdering::Both)
                }
                (left, right) if is_index(left) && is_index(right) => Some(PlaceOrdering::Both),
                diff => unreachable!("Unexpected diff: {diff:?}"),
            }
        } else {
            Some(self.projection.len().cmp(&right.projection.len()).into())
        }
    }

    /// Check if the place `self` is a prefix of `place`. For example:
    ///
    /// +   `is_prefix(x.f, x.f) == true`
    /// +   `is_prefix(x.f, x.f.g) == true`
    /// +   `is_prefix(x.f.g, x.f) == false`
    pub(crate) fn is_prefix(self, place: Self) -> bool {
        Self::partial_cmp(self, place)
            .map(|o| o == PlaceOrdering::Equal || o == PlaceOrdering::Prefix)
            .unwrap_or(false)
    }

    /// Check if the place `self` is an exact prefix of `place`. For example:
    ///
    /// +   `is_prefix(x.f, x.f) == false`
    /// +   `is_prefix(x.f, x.f.g) == true`
    /// +   `is_prefix(x.f, x.f.g.h) == false`
    pub(crate) fn is_prefix_exact(self, place: Self) -> bool {
        self.0.projection.len() + 1 == place.0.projection.len()
            && Self::partial_cmp(self, place)
                .map(|o| o == PlaceOrdering::Prefix)
                .unwrap_or(false)
    }

    /// Check if the place `self` is a prefix of `place` or vice versa. For example:
    ///
    /// +   `is_prefix(x.f, x.f) == None`
    /// +   `is_prefix(x.f, x.f.g) == Some(true)`
    /// +   `is_prefix(x.f.g, x.f) == Some(false)`
    /// +   `is_prefix(x.g, x.f) == None`
    pub(crate) fn either_prefix(self, place: Self) -> Option<bool> {
        Self::partial_cmp(self, place).and_then(|o| {
            if o == PlaceOrdering::Prefix {
                Some(true)
            } else if o == PlaceOrdering::Suffix {
                Some(false)
            } else {
                None
            }
        })
    }

    /// Returns `true` if either of the places can reach the other
    /// with a series of expand/collapse operations. Note that
    /// both operations are allowed and so e.g.
    /// related_to(`_1[_4]`, `_1[_3]`) == true
    pub fn related_to(self, right: Self) -> bool {
        self.partial_cmp(right).is_some()
    }

    pub fn projection_contains_deref(self) -> bool {
        self.projection
            .iter()
            .any(|proj| matches!(proj, ProjectionElem::Deref))
    }

    #[tracing::instrument(level = "debug", ret, fields(lp = ?self.projection, rp = ?other.projection))]
    pub fn common_prefix(self, other: Self) -> Self {
        assert_eq!(self.local, other.local);

        let max_len = std::cmp::min(self.projection.len(), other.projection.len());
        let common_prefix = self
            .compare_projections(other)
            .position(|(eq, _, _)| !eq)
            .unwrap_or(max_len);
        Self::new(self.local, &self.projection[..common_prefix])
    }

    #[tracing::instrument(level = "info", ret)]
    pub fn joinable_to(self, to: Self) -> Self {
        assert!(self.is_prefix(to));
        let diff = to.projection.len() - self.projection.len();
        let to_proj = self.projection.len()
            + to.projection[self.projection.len()..]
                .iter()
                .position(|p| !matches!(p, ProjectionElem::Deref | ProjectionElem::Field(..)))
                .unwrap_or(diff);
        Self::new(self.local, &to.projection[..to_proj])
    }

    pub fn last_projection(self) -> Option<(Self, PlaceElem<'tcx>)> {
        self.0
            .last_projection()
            .map(|(place, proj)| (place.into(), proj))
    }
}

impl Debug for Place<'_> {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        for elem in self.projection.iter().rev() {
            match elem {
                ProjectionElem::OpaqueCast(_) | ProjectionElem::Downcast(_, _) => {
                    write!(fmt, "(").unwrap();
                }
                ProjectionElem::Deref => {
                    write!(fmt, "(*").unwrap();
                }
                ProjectionElem::Field(_, _)
                |  ProjectionElem::Subtype(_)
                | ProjectionElem::Index(_)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. } => {}
            }
        }

        write!(fmt, "{:?}", self.local)?;

        for &elem in self.projection.iter() {
            match elem {
                ProjectionElem::OpaqueCast(ty) => {
                    write!(fmt, "@{ty})")?;
                }
                ProjectionElem::Downcast(Some(name), _index) => {
                    write!(fmt, "@{name})")?;
                }
                ProjectionElem::Downcast(None, index) => {
                    write!(fmt, "@variant#{index:?})")?;
                }
                ProjectionElem::Deref => {
                    write!(fmt, ")")?;
                }
                ProjectionElem::Field(field, _ty) => {
                    write!(fmt, ".{:?}", field.index())?;
                }
                ProjectionElem::Index(ref index) => {
                    write!(fmt, "[{index:?}]")?;
                }
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end: false,
                } => {
                    write!(fmt, "[{offset:?} of {min_length:?}]")?;
                }
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end: true,
                } => {
                    write!(fmt, "[-{offset:?} of {min_length:?}]")?;
                }
                ProjectionElem::Subslice {
                    from,
                    to: 0,
                    from_end: true,
                } => {
                    write!(fmt, "[{from:?}:]")?;
                }
                ProjectionElem::Subslice {
                    from: 0,
                    to,
                    from_end: true,
                } => {
                    write!(fmt, "[:-{to:?}]")?;
                }
                ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: true,
                } => {
                    write!(fmt, "[{from:?}:-{to:?}]")?;
                }
                ProjectionElem::Subslice {
                    from,
                    to,
                    from_end: false,
                } => {
                    write!(fmt, "[{from:?}..{to:?}]")?;
                }
                ProjectionElem::Subtype(ty) => {
                    write!(fmt, "@{ty}")?;
                }
            }
        }

        Ok(())
    }
}

fn elem_eq<'tcx>(to_cmp: (PlaceElem<'tcx>, PlaceElem<'tcx>)) -> bool {
    use ProjectionElem::*;
    match to_cmp {
        (Field(left, _), Field(right, _)) => left == right,
        (Downcast(_, left), Downcast(_, right)) => left == right,
        (left, right) => left == right,
    }
}

impl PartialEq for Place<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.local == other.local
            && self.projection.len() == other.projection.len()
            && self.compare_projections(*other).all(|(eq, _, _)| eq)
    }
}
impl Eq for Place<'_> {}

impl Hash for Place<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.local.hash(state);
        let projection = self.0.projection;
        for &pe in projection {
            match pe {
                ProjectionElem::Field(field, _) => {
                    discriminant(&pe).hash(state);
                    field.hash(state);
                }
                ProjectionElem::Downcast(_, variant) => {
                    discriminant(&pe).hash(state);
                    variant.hash(state);
                }
                _ => pe.hash(state),
            }
        }
    }
}

// impl<'tcx, T: Into<PlaceRef<'tcx>>> From<T> for Place<'tcx> {
//     fn from(value: T) -> Self {
//         Self(value.into())
//     }
// }
impl<'tcx> From<PlaceRef<'tcx>> for Place<'tcx> {
    fn from(value: PlaceRef<'tcx>) -> Self {
        Self(value)
    }
}
impl<'tcx> From<MirPlace<'tcx>> for Place<'tcx> {
    fn from(value: MirPlace<'tcx>) -> Self {
        Self(value.as_ref())
    }
}
impl<'tcx> From<Local> for Place<'tcx> {
    fn from(value: Local) -> Self {
        MirPlace::from(value).into()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PlaceOrdering {
    // For example `x.f` to `x.f.g`.
    Prefix,
    // For example `x.f` and `x.f`.
    Equal,
    // For example `x.f.g` to `x.f`.
    Suffix,
    // For example `x[a]` and `x[b]` or `x as None` and `x as Some`.
    Both,
}

impl PlaceOrdering {
    pub fn is_eq(self) -> bool {
        matches!(self, PlaceOrdering::Equal)
    }
    pub fn is_prefix(self) -> bool {
        matches!(self, PlaceOrdering::Prefix)
    }
    pub fn is_suffix(self) -> bool {
        matches!(self, PlaceOrdering::Suffix)
    }
    pub fn is_both(self) -> bool {
        matches!(self, PlaceOrdering::Both)
    }
}

impl From<Ordering> for PlaceOrdering {
    fn from(ordering: Ordering) -> Self {
        match ordering {
            Ordering::Less => PlaceOrdering::Prefix,
            Ordering::Equal => PlaceOrdering::Equal,
            Ordering::Greater => PlaceOrdering::Suffix,
        }
    }
}
impl From<PlaceOrdering> for Option<Ordering> {
    fn from(ordering: PlaceOrdering) -> Self {
        match ordering {
            PlaceOrdering::Prefix => Some(Ordering::Less),
            PlaceOrdering::Equal => Some(Ordering::Equal),
            PlaceOrdering::Suffix => Some(Ordering::Greater),
            PlaceOrdering::Both => None,
        }
    }
}
