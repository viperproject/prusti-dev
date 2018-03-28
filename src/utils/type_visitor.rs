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
        self.visit_sty(&ty.sty);
        self.visit_flags(ty.flags);
    }

    fn visit_sty(&mut self, sty: &TypeVariants<'tcx>) {
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
            TyTuple(parts, _) => {
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

    fn visit_adt(&mut self, adt_def: &'tcx AdtDef, _subts: &'tcx Substs<'tcx>) {
        self.visit_adt_def(adt_def);
    }

    fn visit_adt_def(&mut self, adt_def: &'tcx AdtDef) {
        for variant in adt_def.variants.iter() {
            self.visit_adt_variant(variant);
        }
    }

    fn visit_adt_variant(&mut self, variant: &VariantDef) {
        for field in variant.fields.iter() {
            self.visit_field(field);
        }
    }

    fn visit_field(&mut self, field: &FieldDef) {
        println!("field name: {:?}", field.name);
    }

    fn visit_ref(&mut self, region: Region<'tcx>, tym: TypeAndMut<'tcx>) {
        self.visit_ref_type(tym.ty, tym.mutbl);
    }

    fn visit_ref_type(&mut self, ty: Ty<'tcx>, mutability: Mutability) {
        self.visit_ty(ty);
    }

    fn visit_tuple(&mut self, parts: &'tcx Slice<Ty<'tcx>>) {
    }

}
