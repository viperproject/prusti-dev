// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::{
    hir,
    middle::{
        mir::{Mutability, ProjectionElem},
        ty::{CapturedPlace, TyKind, UpvarCapture},
    },
    target::abi::FieldIdx,
};

use super::{root_place::RootPlace, Place, PlaceRepacker};

struct Upvar<'tcx> {
    pub(crate) place: CapturedPlace<'tcx>,
    pub(crate) by_ref: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocalMutationIsAllowed {
    Yes,
    ExceptUpvars,
    No,
}

impl<'a, 'tcx: 'a> PlaceRepacker<'a, 'tcx> {
    fn upvars(self) -> Vec<Upvar<'tcx>> {
        let def = self.body().source.def_id().expect_local();
        self.tcx
            .closure_captures(def)
            .iter()
            .map(|&captured_place| {
                let capture = captured_place.info.capture_kind;
                let by_ref = match capture {
                    UpvarCapture::ByValue => false,
                    UpvarCapture::ByRef(..) => true,
                };
                Upvar {
                    place: captured_place.clone(),
                    by_ref,
                }
            })
            .collect()
    }
}

impl<'tcx> Place<'tcx> {
    pub fn is_mutable(
        self,
        is_local_mutation_allowed: LocalMutationIsAllowed,
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<RootPlace<'tcx>, Self> {
        let upvars = repacker.upvars();
        self.is_mutable_helper(is_local_mutation_allowed, &upvars, repacker)
    }

    /// Whether this value can be written or borrowed mutably.
    /// Returns the root place if the place passed in is a projection.
    fn is_mutable_helper(
        self,
        is_local_mutation_allowed: LocalMutationIsAllowed,
        upvars: &[Upvar<'tcx>],
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Result<RootPlace<'tcx>, Self> {
        match self.last_projection() {
            None => {
                let local = &repacker.body().local_decls[self.local];
                match local.mutability {
                    Mutability::Not => match is_local_mutation_allowed {
                        LocalMutationIsAllowed::Yes => Ok(RootPlace {
                            place: self,
                            is_local_mutation_allowed: LocalMutationIsAllowed::Yes,
                        }),
                        LocalMutationIsAllowed::ExceptUpvars => Ok(RootPlace {
                            place: self,
                            is_local_mutation_allowed: LocalMutationIsAllowed::ExceptUpvars,
                        }),
                        LocalMutationIsAllowed::No => Err(self),
                    },
                    Mutability::Mut => Ok(RootPlace {
                        place: self,
                        is_local_mutation_allowed,
                    }),
                }
            }
            Some((place_base, elem)) => {
                match elem {
                    ProjectionElem::Deref => {
                        let base_ty = place_base.ty(repacker).ty;

                        // Check the kind of deref to decide
                        match base_ty.kind() {
                            TyKind::Ref(_, _, mutbl) => {
                                match mutbl {
                                    // Shared borrowed data is never mutable
                                    hir::Mutability::Not => Err(self),
                                    // Mutably borrowed data is mutable, but only if we have a
                                    // unique path to the `&mut`
                                    hir::Mutability::Mut => {
                                        let mode = match self
                                            .is_upvar_field_projection(upvars, repacker)
                                        {
                                            Some(field) if upvars[field.index()].by_ref => {
                                                is_local_mutation_allowed
                                            }
                                            _ => LocalMutationIsAllowed::Yes,
                                        };

                                        place_base.is_mutable_helper(mode, upvars, repacker)
                                    }
                                }
                            }
                            TyKind::RawPtr(tnm) => {
                                match tnm.mutbl {
                                    // `*const` raw pointers are not mutable
                                    hir::Mutability::Not => Err(self),
                                    // `*mut` raw pointers are always mutable, regardless of
                                    // context. The users have to check by themselves.
                                    hir::Mutability::Mut => Ok(RootPlace {
                                        place: self,
                                        is_local_mutation_allowed,
                                    }),
                                }
                            }
                            // `Box<T>` owns its content, so mutable if its location is mutable
                            _ if base_ty.is_box() => place_base.is_mutable_helper(
                                is_local_mutation_allowed,
                                upvars,
                                repacker,
                            ),
                            // Deref should only be for reference, pointers or boxes
                            _ => panic!("Deref of unexpected type: {:?}", base_ty),
                        }
                    }
                    // All other projections are owned by their base path, so mutable if
                    // base path is mutable
                    ProjectionElem::Field(..)
                    | ProjectionElem::Index(..)
                    | ProjectionElem::ConstantIndex { .. }
                    | ProjectionElem::Subslice { .. }
                    | ProjectionElem::OpaqueCast { .. }
                    | ProjectionElem::Downcast(..) => {
                        let upvar_field_projection =
                            self.is_upvar_field_projection(upvars, repacker);
                        if let Some(field) = upvar_field_projection {
                            let upvar = &upvars[field.index()];
                            match (upvar.place.mutability, is_local_mutation_allowed) {
                                (
                                    Mutability::Not,
                                    LocalMutationIsAllowed::No
                                    | LocalMutationIsAllowed::ExceptUpvars,
                                ) => Err(self),
                                (Mutability::Not, LocalMutationIsAllowed::Yes)
                                | (Mutability::Mut, _) => {
                                    // Subtle: this is an upvar
                                    // reference, so it looks like
                                    // `self.foo` -- we want to double
                                    // check that the location `*self`
                                    // is mutable (i.e., this is not a
                                    // `Fn` closure). But if that
                                    // check succeeds, we want to
                                    // *blame* the mutability on
                                    // `place` (that is,
                                    // `self.foo`). This is used to
                                    // propagate the info about
                                    // whether mutability declarations
                                    // are used outwards, so that we register
                                    // the outer variable as mutable. Otherwise a
                                    // test like this fails to record the `mut`
                                    // as needed:
                                    //
                                    // ```
                                    // fn foo<F: FnOnce()>(_f: F) { }
                                    // fn main() {
                                    //     let var = Vec::new();
                                    //     foo(move || {
                                    //         var.push(1);
                                    //     });
                                    // }
                                    // ```
                                    let _ = place_base.is_mutable_helper(
                                        is_local_mutation_allowed,
                                        upvars,
                                        repacker,
                                    )?;
                                    Ok(RootPlace {
                                        place: self,
                                        is_local_mutation_allowed,
                                    })
                                }
                            }
                        } else {
                            place_base.is_mutable_helper(
                                is_local_mutation_allowed,
                                upvars,
                                repacker,
                            )
                        }
                    }
                }
            }
        }
    }

    /// If `place` is a field projection, and the field is being projected from a closure type,
    /// then returns the index of the field being projected. Note that this closure will always
    /// be `self` in the current MIR, because that is the only time we directly access the fields
    /// of a closure type.
    fn is_upvar_field_projection(
        self,
        upvars: &[Upvar<'tcx>],
        repacker: PlaceRepacker<'_, 'tcx>,
    ) -> Option<FieldIdx> {
        let mut place_ref = *self;
        let mut by_ref = false;

        if let Some((place_base, ProjectionElem::Deref)) = place_ref.last_projection() {
            place_ref = place_base;
            by_ref = true;
        }

        match place_ref.last_projection() {
            Some((place_base, ProjectionElem::Field(field, _ty))) => {
                let base_ty = place_base.ty(repacker.body(), repacker.tcx).ty;
                if (base_ty.is_closure() || base_ty.is_generator())
                    && (!by_ref || upvars[field.index()].by_ref)
                {
                    Some(field)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}
