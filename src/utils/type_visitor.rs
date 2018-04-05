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

pub trait TypeVisitor<'a, 'tcx> : Sized {

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
        walk_adt(self, adt_def, substs);
    }

    fn visit_adt_variant(&mut self, variant: &VariantDef, substs: &'tcx Substs<'tcx>) {
        trace!("visit_adt_variant({:?})", variant);
        walk_adt_variant(self, variant, substs);
    }

    fn visit_field(&mut self, field: &FieldDef, substs: &'tcx Substs<'tcx>) {
        trace!("visit_field({:?})", field);
        walk_field(self, field, substs);
    }

    fn visit_ref(&mut self, region: Region<'tcx>, tym: TypeAndMut<'tcx>) {
        trace!("visit_ref({:?}, {:?})", region, tym);
        walk_ref(self, region, tym);
    }

    fn visit_ref_type(&mut self, ty: Ty<'tcx>, mutability: Mutability) {
        trace!("visit_ref_type({:?}, {:?})", ty, mutability);
        walk_ref_type(self, ty, mutability);
    }

    fn visit_tuple(&mut self, parts: &'tcx Slice<Ty<'tcx>>) {
        trace!("visit_tuple({:?})", parts);
        walk_tuple(self, parts);
    }

}

pub fn walk_adt<'a, 'tcx, V: TypeVisitor<'a, 'tcx>>(visitor: &mut V,
                                                    adt_def: &'tcx AdtDef,
                                                    substs: &'tcx Substs<'tcx>) {
    for variant in adt_def.variants.iter() {
        visitor.visit_adt_variant(variant, substs);
    }
}

pub fn walk_adt_variant<'a, 'tcx, V: TypeVisitor<'a, 'tcx>>(visitor: &mut V,
                                                            variant: &VariantDef,
                                                            substs: &'tcx Substs<'tcx>) {
    for field in variant.fields.iter() {
        visitor.visit_field(field, substs);
    }
}

pub fn walk_field<'a, 'tcx, V: TypeVisitor<'a, 'tcx>>(visitor: &mut V,
                                                      field: &FieldDef,
                                                      substs: &'tcx Substs<'tcx>) {
    let ty = field.ty(visitor.tcx(), substs);
    visitor.visit_ty(ty);
}

pub fn walk_ref<'a, 'tcx, V: TypeVisitor<'a, 'tcx>>(visitor: &mut V,
                                                    region: Region<'tcx>,
                                                    tym: TypeAndMut<'tcx>) {
    visitor.visit_ref_type(tym.ty, tym.mutbl);
}

pub fn walk_ref_type<'a, 'tcx, V: TypeVisitor<'a, 'tcx>>(visitor: &mut V,
                                                         ty: Ty<'tcx>,
                                                         mutability: Mutability) {
    visitor.visit_ty(ty);
}

pub fn walk_tuple<'a, 'tcx, V: TypeVisitor<'a, 'tcx>>(visitor: &mut V,
                                                      parts: &'tcx Slice<Ty<'tcx>>) {
    for part in parts.iter() {
        visitor.visit_ty(part);
    }
}
