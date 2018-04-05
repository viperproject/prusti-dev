// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::ty::{
    Ty, TyCtxt, TypeVariants, TypeFlags, AdtDef, Region, TypeAndMut, Slice,
    VariantDef, FieldDef};
use syntax::ast::{IntTy, UintTy};
use rustc::hir::Mutability;
use rustc::ty::subst::Substs;
use rustc::ty::TypeVariants::*;

pub trait TypeVisitor<'a, 'tcx> {

    fn tcx(&self) -> TyCtxt<'a, 'tcx, 'tcx>;

    fn visit_ty(&mut self, ty: Ty<'tcx>) {
        trace!("visit_ty({:?})", ty);
        self.visit_sty(&ty.sty);
        self.visit_flags(ty.flags);
    }

    fn visit_sty(&mut self, sty: &TypeVariants<'tcx>) {
        trace!("visit_sty({:?})", sty);
        match *sty {
            TyBool => {
                self.visit_bool();
            },
            TyInt(ty) => {
                self.visit_int(ty);
            },
            TyUint(ty) => {
                self.visit_uint(ty);
            },
            TyAdt(adt_def, substs) => {
                self.visit_adt(adt_def, substs);
            },
            TyRef(region, tym) => {
                self.visit_ref(region, tym);
            },
            TyTuple(parts, diverging) => {
                assert!(!diverging);
                self.visit_tuple(parts);
            },
            _ => {
                unimplemented!();
            }
        }

    }

    fn visit_flags(&mut self, _flags: TypeFlags) {
    }

    fn visit_bool(&mut self) {
    }

    fn visit_int(&mut self, _ty: IntTy) {
    }

    fn visit_uint(&mut self, _ty: UintTy) {
    }

    fn visit_adt(&mut self, adt_def: &'tcx AdtDef, substs: &'tcx Substs<'tcx>) {
        trace!("visit_adt({:?})", adt_def);
        for variant in adt_def.variants.iter() {
            self.visit_adt_variant(variant, substs);
        }
    }

    fn visit_adt_variant(&mut self, variant: &VariantDef, substs: &'tcx Substs<'tcx>) {
        trace!("visit_adt_variant({:?})", variant);
        for field in variant.fields.iter() {
            self.visit_field(field, substs);
        }
    }

    fn visit_field(&mut self, field: &FieldDef, substs: &'tcx Substs<'tcx>) {
        trace!("visit_field({:?})", field);
        let ty = field.ty(self.tcx(), substs);
        self.visit_ty(ty);
    }

    fn visit_ref(&mut self, region: Region<'tcx>, tym: TypeAndMut<'tcx>) {
        trace!("visit_ref({:?}, {:?})", region, tym);
        self.visit_ref_type(tym.ty, tym.mutbl);
    }

    fn visit_ref_type(&mut self, ty: Ty<'tcx>, mutability: Mutability) {
        trace!("visit_ref_type({:?}, {:?})", ty, mutability);
        self.visit_ty(ty);
    }

    fn visit_tuple(&mut self, parts: &'tcx Slice<Ty<'tcx>>) {
        trace!("visit_tuple({:?})", parts);
        for part in parts.iter() {
            self.visit_ty(part);
        }
    }

}
