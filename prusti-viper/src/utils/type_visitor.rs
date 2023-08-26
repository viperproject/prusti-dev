// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_rustc_interface::hir::Mutability;
use prusti_rustc_interface::middle::ty::{
    AdtDef, FieldDef, List, ParamTy, Region, AliasKind, AliasTy, Ty, TyCtxt,
    TypeFlags, TyKind, IntTy, UintTy, FloatTy, VariantDef, GenericArgsRef, Const
};
use prusti_rustc_interface::hir::def_id::DefId;

pub trait TypeVisitor<'tcx>: Sized {
    type Error;

    fn tcx(&self) -> TyCtxt<'tcx>;

    fn unsupported<S: ToString>(&self, _msg: S) -> Self::Error;

    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Result<(), Self::Error> {
        self.visit_sty(ty.kind())?;
        self.visit_flags(ty.flags())
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_sty(&mut self, sty: &TyKind<'tcx>) -> Result<(), Self::Error> {
        match *sty {
            TyKind::Bool => {
                self.visit_bool()
            }
            TyKind::Int(ty) => {
                self.visit_int(ty)
            }
            TyKind::Uint(ty) => {
                self.visit_uint(ty)
            }
            TyKind::Float(ty) => {
                self.visit_float(ty)
            }
            TyKind::Char => {
                self.visit_char()
            }
            TyKind::Adt(adt_def, substs) => {
                self.visit_adt(adt_def, substs)
            }
            TyKind::Ref(region, ty, mutability) => {
                self.visit_ref(region, ty, mutability)
            }
            TyKind::Tuple(types) => {
                self.visit_tuple(types)
            }
            TyKind::RawPtr(ty_and_mutbl) => {
                self.visit_raw_ptr(ty_and_mutbl.ty, ty_and_mutbl.mutbl)
            }
            TyKind::Never => {
                self.visit_never()
            }
            TyKind::Param(param) => {
                self.visit_param(param)
            }
            TyKind::Alias(AliasKind::Projection, alias_ty) => {
                self.visit_projection(alias_ty)
            }
            TyKind::Closure(def_id, substs) => {
                self.visit_closure(def_id, substs)
            }
            TyKind::FnDef(def_id, substs) => {
                self.visit_fndef(def_id, substs)
            }
            TyKind::Array(ty, len) => {
                self.visit_array(ty, len)
            }
            ref x => {
                self.visit_unsupported_sty(x)
            }
        }
    }

    fn visit_unsupported_sty(
        &mut self,
        _sty: &TyKind<'tcx>
    ) -> Result<(), Self::Error>;

    fn visit_flags(&mut self, _flags: TypeFlags) -> Result<(), Self::Error> {
        Ok(())
    }

    fn visit_bool(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn visit_int(&mut self, _ty: IntTy) -> Result<(), Self::Error> {
        Ok(())
    }

    fn visit_uint(&mut self, _ty: UintTy) -> Result<(), Self::Error> {
        Ok(())
    }

    fn visit_float(&mut self, _ty: FloatTy) -> Result<(), Self::Error> {
        Ok(())
    }

    fn visit_char(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn visit_never(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn visit_param(&mut self, _param: ParamTy) -> Result<(), Self::Error> {
        Ok(())
    }

    fn visit_projection(
        &mut self,
        _data: AliasTy<'tcx>
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_adt(
        &mut self,
        adt_def: AdtDef<'tcx>,
        substs: GenericArgsRef<'tcx>
    ) -> Result<(), Self::Error> {
        walk_adt(self, adt_def, substs)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_adt_variant(
        &mut self,
        adt: AdtDef<'tcx>,
        idx: prusti_rustc_interface::target::abi::VariantIdx,
        variant: &VariantDef,
        substs: GenericArgsRef<'tcx>,
    )  -> Result<(), Self::Error> {
        walk_adt_variant(self, variant, substs)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_field(
        &mut self,
        index: usize,
        field: &FieldDef,
        substs: GenericArgsRef<'tcx>,
    ) -> Result<(), Self::Error> {
        walk_field(self, field, substs)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_ref(
        &mut self,
        region: Region<'tcx>,
        ty: Ty<'tcx>,
        mutability: Mutability
    ) -> Result<(), Self::Error> {
        walk_ref(self, region, ty, mutability)
    }

    #[allow(dead_code)]
    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_ref_type(
        &mut self,
        ty: Ty<'tcx>,
        mutability: Mutability
    ) -> Result<(), Self::Error> {
        walk_ref_type(self, ty, mutability)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_tuple(
        &mut self,
        types: &'tcx List<Ty<'tcx>>
    ) -> Result<(), Self::Error> {
        walk_tuple(self, types)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_raw_ptr(
        &mut self,
        ty: Ty<'tcx>,
        mutability: Mutability
    ) -> Result<(), Self::Error> {
        walk_raw_ptr(self, ty, mutability)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_closure(
        &mut self,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>
    ) -> Result<(), Self::Error> {
        walk_closure(self, def_id, substs)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_fndef(
        &mut self,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>
    ) -> Result<(), Self::Error> {
        walk_fndef(self, def_id, substs)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    fn visit_array(
        &mut self,
        ty: Ty<'tcx>,
        len: Const<'tcx>,
    ) -> Result<(), Self::Error> {
        walk_array(self, ty, len)
    }
}

pub fn walk_adt<'tcx, E, V: TypeVisitor<'tcx, Error = E>>(
    visitor: &mut V,
    adt_def: AdtDef<'tcx>,
    substs: GenericArgsRef<'tcx>,
) -> Result<(), E> {
    for (idx, variant) in adt_def.variants().iter_enumerated() {
        visitor.visit_adt_variant(adt_def, idx, variant, substs)?;
    }
    Ok(())
}

pub fn walk_adt_variant<'a, 'tcx, E, V: TypeVisitor<'tcx, Error = E>>(
    visitor: &mut V,
    variant: &VariantDef,
    substs: GenericArgsRef<'tcx>,
) -> Result<(), E> {
    for (index, field) in variant.fields.iter().enumerate() {
        visitor.visit_field(index, field, substs)?;
    }
    Ok(())
}

pub fn walk_field<'a, 'tcx, E, V: TypeVisitor<'tcx, Error = E>>(
    visitor: &mut V,
    field: &FieldDef,
    substs: GenericArgsRef<'tcx>,
) -> Result<(), E> {
    let ty = field.ty(visitor.tcx(), substs);
    visitor.visit_ty(ty)
}

pub fn walk_ref<'tcx, E, V: TypeVisitor<'tcx, Error = E>>(
    visitor: &mut V,
    _: Region<'tcx>,
    ty: Ty<'tcx>,
    _: Mutability,
) -> Result<(), E> {
    visitor.visit_ty(ty)
}

pub fn walk_ref_type<'tcx, E, V: TypeVisitor<'tcx, Error = E>>(
    visitor: &mut V,
    ty: Ty<'tcx>,
    _: Mutability,
) -> Result<(), E> {
    visitor.visit_ty(ty)
}

pub fn walk_tuple<'tcx, E, V: TypeVisitor<'tcx, Error = E>>(
    visitor: &mut V,
    types: &'tcx List<Ty<'tcx>>,
) -> Result<(), E> {
    for ty in types {
        visitor.visit_ty(ty)?;
    }
    Ok(())
}

pub fn walk_raw_ptr<'tcx, E, V: TypeVisitor<'tcx, Error = E>>(
    visitor: &mut V,
    ty: Ty<'tcx>,
    _: Mutability,
) -> Result<(), E> {
    visitor.visit_ty(ty)
}

pub fn walk_closure<'tcx, E, V: TypeVisitor<'tcx, Error = E>>(
    visitor: &mut V,
    _def_id: DefId,
    substs: GenericArgsRef<'tcx>
) -> Result<(), E> {
    let cl_substs = substs.as_closure();
    // TODO: when are there bound typevars? can type visitor deal with generics?
    let fn_sig =
        cl_substs.sig()
                 .no_bound_vars()
                 .ok_or_else(|| visitor.unsupported("higher-ranked lifetimes and types are not supported"))?;
    for ty in fn_sig.inputs() {
        visitor.visit_ty(*ty)?;
    }
    visitor.visit_ty(fn_sig.output())
}

pub fn walk_fndef<'tcx, E, V: TypeVisitor<'tcx, Error = E>>(
    visitor: &mut V,
    _def_id: DefId,
    substs: GenericArgsRef<'tcx>
) -> Result<(), E> {
    for ty in substs.types() {
        visitor.visit_ty(ty)?;
    }
    Ok(())
}

pub fn walk_array<'tcx, E, V: TypeVisitor<'tcx, Error = E>>(
    visitor: &mut V,
    ty: Ty<'tcx>,
    _len: Const<'tcx>,
) -> Result<(), E> {
    visitor.visit_ty(ty)?;

    Ok(())
}
