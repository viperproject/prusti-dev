// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::hir::Mutability;
use rustc::ty::{
    AdtDef, FieldDef, Region, Slice, Ty, TyCtxt, TypeFlags,
    TypeVariants, VariantDef, ParamTy};
use rustc::ty::subst::Substs;
use rustc::ty::TypeVariants::*;
use syntax::ast::{IntTy, UintTy};

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
            TyChar => {
                self.visit_char();
            },
            TyAdt(adt_def, substs) => {
                self.visit_adt(adt_def, substs);
            },
            TyRef(region, ty, mutability) => {
                self.visit_ref(region, ty, mutability);
            },
            TyTuple(parts) => {
                self.visit_tuple(parts);
            },
            TyRawPtr(ty_and_mutbl) => {
                self.visit_raw_ptr(ty_and_mutbl.ty, ty_and_mutbl.mutbl);
            },
            TyNever => {
                self.visit_never();
            },
            TyParam(param) => {
                self.visit_param(param);
            },
            ref x => {
                unimplemented!("{:?}", x);
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

    fn visit_char(&mut self) {
    }

    fn visit_never(&mut self) {
    }

    fn visit_param(&mut self, param: ParamTy) {
    }

    fn visit_adt(&mut self, adt_def: &'tcx AdtDef, substs: &'tcx Substs<'tcx>) {
        trace!("visit_adt({:?})", adt_def);
        walk_adt(self, adt_def, substs);
    }

    fn visit_adt_variant(&mut self, variant: &VariantDef, substs: &'tcx Substs<'tcx>) {
        trace!("visit_adt_variant({:?})", variant);
        walk_adt_variant(self, variant, substs);
    }

    fn visit_field(&mut self, index: usize, field: &FieldDef, substs: &'tcx Substs<'tcx>) {
        trace!("visit_field({}, {:?})", index, field);
        walk_field(self, field, substs);
    }

    fn visit_ref(&mut self, region: Region<'tcx>, ty: Ty<'tcx>, mutability: Mutability) {
        trace!("visit_ref({:?}, {:?}, {:?})", region, ty, mutability);
        walk_ref(self, region, ty, mutability);
    }

    fn visit_ref_type(&mut self, ty: Ty<'tcx>, mutability: Mutability) {
        trace!("visit_ref_type({:?}, {:?})", ty, mutability);
        walk_ref_type(self, ty, mutability);
    }

    fn visit_tuple(&mut self, parts: &'tcx Slice<Ty<'tcx>>) {
        trace!("visit_tuple({:?})", parts);
        walk_tuple(self, parts);
    }

    fn visit_raw_ptr(&mut self, ty: Ty<'tcx>, mutability: Mutability) {
        trace!("visit_raw_ptr({:?}, {:?})", ty, mutability);
        walk_raw_ptr(self, ty, mutability);
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
    for (index, field) in variant.fields.iter().enumerate() {
        visitor.visit_field(index, field, substs);
    }
}

pub fn walk_field<'a, 'tcx, V: TypeVisitor<'a, 'tcx>>(visitor: &mut V,
                                                      field: &FieldDef,
                                                      substs: &'tcx Substs<'tcx>) {
    let ty = field.ty(visitor.tcx(), substs);
    visitor.visit_ty(ty);
}

pub fn walk_ref<'a, 'tcx, V: TypeVisitor<'a, 'tcx>>(visitor: &mut V,
                                                    _: Region<'tcx>,
                                                    ty: Ty<'tcx>,
                                                    _: Mutability) {
    visitor.visit_ty(ty);
}

pub fn walk_ref_type<'a, 'tcx, V: TypeVisitor<'a, 'tcx>>(visitor: &mut V,
                                                         ty: Ty<'tcx>,
                                                         _: Mutability) {
    visitor.visit_ty(ty);
}

pub fn walk_tuple<'a, 'tcx, V: TypeVisitor<'a, 'tcx>>(visitor: &mut V,
                                                      parts: &'tcx Slice<Ty<'tcx>>) {
    for part in parts.iter() {
        visitor.visit_ty(part);
    }
}

pub fn walk_raw_ptr<'a, 'tcx, V: TypeVisitor<'a, 'tcx>>(visitor: &mut V,
                                                         ty: Ty<'tcx>,
                                                         _: Mutability) {
    visitor.visit_ty(ty);
}
