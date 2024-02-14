// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

mod ty_rec;

pub use ty_rec::*;

use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    dataflow::storage,
    index::bit_set::BitSet,
    middle::{
        mir::{
            tcx::PlaceTy, Body, HasLocalDecls, Local, Mutability, Place as MirPlace, ProjectionElem,
        },
        ty::{Ty, TyCtxt, TyKind},
    },
};

pub struct Stack<'tcx>(Vec<Ty<'tcx>>);

impl<'tcx> Stack<'tcx> {
    pub fn get(&self) -> &Vec<Ty<'tcx>> {
        &self.0
    }
}

pub trait DeepTypeVisitor<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx>;

    fn visit(&mut self, ty: Ty<'tcx>) {
        self.visit_rec(ty, &mut Stack(Vec::new()));
    }
    fn visit_rec(&mut self, ty: Ty<'tcx>, stack: &mut Stack<'tcx>);
}

pub trait DeepTypeVisitable<'tcx> {
    fn visit_with(&self, visitor: &mut impl DeepTypeVisitor<'tcx>, stack: &mut Stack<'tcx>);
}

impl<'tcx> DeepTypeVisitable<'tcx> for Ty<'tcx> {
    fn visit_with(&self, visitor: &mut impl DeepTypeVisitor<'tcx>, stack: &mut Stack<'tcx>) {
        if stack.0.contains(self) {
            return;
        }
        stack.0.push(*self);
        match self.kind() {
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Str => (),
            TyKind::Adt(def_id, substs) => {
                for field in def_id.all_fields() {
                    let ty = field.ty(visitor.tcx(), substs);
                    visitor.visit_rec(ty, stack);
                }
            }
            TyKind::Tuple(tys) => {
                for ty in tys.iter() {
                    visitor.visit_rec(ty, stack);
                }
            }
            TyKind::Ref(_, ty, _) => {
                visitor.visit_rec(*ty, stack);
            }
            TyKind::Foreign(_) => todo!(),
            TyKind::Array(_, _) => todo!(),
            TyKind::Slice(_) => todo!(),
            TyKind::RawPtr(_) => todo!(),
            TyKind::FnDef(_, _) => todo!(),
            TyKind::FnPtr(_) => todo!(),
            TyKind::Dynamic(_, _, _) => todo!(),
            TyKind::Closure(_, _) => todo!(),
            TyKind::Generator(_, _, _) => todo!(),
            TyKind::GeneratorWitness(_) => todo!(),
            TyKind::GeneratorWitnessMIR(_, _) => todo!(),
            TyKind::Never => todo!(),
            TyKind::Alias(_, _) => todo!(),
            TyKind::Param(_) => todo!(),
            TyKind::Bound(_, _) => todo!(),
            TyKind::Placeholder(_) => todo!(),
            TyKind::Infer(_) => todo!(),
            TyKind::Error(_) => todo!(),
        }
        stack.0.pop();
    }
}

// pub fn is_ty_rec(ty: Ty) -> bool {
//     let walker = ty.walk();
// }
