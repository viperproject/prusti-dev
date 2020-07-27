// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc_hir::Mutability;
use rustc_middle::ty::{
    AdtDef, FieldDef, ParamTy, ProjectionTy, Region, Slice, Ty, TyCtxt, TypeFlags, TyKind,
    VariantDef, subst::SubstsRef
};
use rustc_ast::ast::{IntTy, UintTy};
use log::trace;

pub trait TypeVisitor<'tcx>: Sized {
    fn tcx(&self) -> TyCtxt<'tcx>;

    fn visit_ty(&mut self, ty: Ty<'tcx>) {
        trace!("visit_ty({:?})", ty);
        self.visit_sty(&ty.kind);
        self.visit_flags(ty.flags);
    }

    fn visit_sty(&mut self, sty: &TyKind<'tcx>) {
        trace!("visit_sty({:?})", sty);
        match *sty {
            TyKind::Bool => {
                self.visit_bool();
            }
            TyKind::Int(ty) => {
                self.visit_int(ty);
            }
            TyKind::Uint(ty) => {
                self.visit_uint(ty);
            }
            TyKind::Char => {
                self.visit_char();
            }
            TyKind::Adt(adt_def, substs) => {
                self.visit_adt(adt_def, substs);
            }
            TyKind::Ref(region, ty, mutability) => {
                self.visit_ref(region, ty, mutability);
            }
            TyKind::Tuple(parts) => {
                self.visit_tuple(parts);
            }
            TyKind::RawPtr(ty_and_mutbl) => {
                self.visit_raw_ptr(ty_and_mutbl.ty, ty_and_mutbl.mutbl);
            }
            TyKind::Never => {
                self.visit_never();
            }
            TyKind::Param(param) => {
                self.visit_param(param);
            }
            TyKind::Projection(data) => {
                self.visit_projection(data);
            }
            ref x => {
                unimplemented!("{:?}", x);
            }
        }
    }

    fn visit_flags(&mut self, _flags: TypeFlags) {}

    fn visit_bool(&mut self) {}

    fn visit_int(&mut self, _ty: IntTy) {}

    fn visit_uint(&mut self, _ty: UintTy) {}

    fn visit_char(&mut self) {}

    fn visit_never(&mut self) {}

    fn visit_param(&mut self, _param: ParamTy) {}

    fn visit_projection(&mut self, _data: ProjectionTy<'tcx>) {}

    fn visit_adt(&mut self, adt_def: &'tcx AdtDef, substs: SubstsRef<'tcx>) {
        trace!("visit_adt({:?})", adt_def);
        walk_adt(self, adt_def, substs);
    }

    fn visit_adt_variant(&mut self, variant: &VariantDef, substs: SubstsRef<'tcx>) {
        trace!("visit_adt_variant({:?})", variant);
        walk_adt_variant(self, variant, substs);
    }

    fn visit_field(&mut self, index: usize, field: &FieldDef, substs: SubstsRef<'tcx>) {
        trace!("visit_field({}, {:?})", index, field);
        walk_field(self, field, substs);
    }

    fn visit_ref(&mut self, region: Region<'tcx>, ty: Ty<'tcx>, mutability: Mutability) {
        trace!("visit_ref({:?}, {:?}, {:?})", region, ty, mutability);
        walk_ref(self, region, ty, mutability);
    }

    #[allow(dead_code)]
    fn visit_ref_type(&mut self, ty: Ty<'tcx>, mutability: Mutability) {
        trace!("visit_ref_type({:?}, {:?})", ty, mutability);
        walk_ref_type(self, ty, mutability);
    }

    fn visit_tuple(&mut self, parts: SubstsRef<'tcx>) {
        trace!("visit_tuple({:?})", parts);
        walk_tuple(self, parts);
    }

    fn visit_raw_ptr(&mut self, ty: Ty<'tcx>, mutability: Mutability) {
        trace!("visit_raw_ptr({:?}, {:?})", ty, mutability);
        walk_raw_ptr(self, ty, mutability);
    }
}

pub fn walk_adt<'tcx, V: TypeVisitor<'tcx>>(
    visitor: &mut V,
    adt_def: &'tcx AdtDef,
    substs: SubstsRef<'tcx>,
) {
    for variant in adt_def.variants.iter() {
        visitor.visit_adt_variant(variant, substs);
    }
}

pub fn walk_adt_variant<'a, 'tcx, V: TypeVisitor<'tcx>>(
    visitor: &mut V,
    variant: &VariantDef,
    substs: SubstsRef<'tcx>,
) {
    for (index, field) in variant.fields.iter().enumerate() {
        visitor.visit_field(index, field, substs);
    }
}

pub fn walk_field<'a, 'tcx, V: TypeVisitor<'tcx>>(
    visitor: &mut V,
    field: &FieldDef,
    substs: SubstsRef<'tcx>,
) {
    let ty = field.ty(visitor.tcx(), substs);
    visitor.visit_ty(ty);
}

pub fn walk_ref<'tcx, V: TypeVisitor<'tcx>>(
    visitor: &mut V,
    _: Region<'tcx>,
    ty: Ty<'tcx>,
    _: Mutability,
) {
    visitor.visit_ty(ty);
}

pub fn walk_ref_type<'tcx, V: TypeVisitor<'tcx>>(
    visitor: &mut V,
    ty: Ty<'tcx>,
    _: Mutability,
) {
    visitor.visit_ty(ty);
}

pub fn walk_tuple<'tcx, V: TypeVisitor<'tcx>>(
    visitor: &mut V,
    parts: SubstsRef<'tcx>,
) {
    for part in parts.iter() {
        visitor.visit_ty(part.expect_ty());
    }
}

pub fn walk_raw_ptr<'tcx, V: TypeVisitor<'tcx>>(
    visitor: &mut V,
    ty: Ty<'tcx>,
    _: Mutability,
) {
    visitor.visit_ty(ty);
}
