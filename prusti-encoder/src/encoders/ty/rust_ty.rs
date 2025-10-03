use std::ops::Deref;

use itertools::Itertools;
use pcg::borrow_pcg::region_projection::{HasRegions, PcgRegion, RegionIdx};
use prusti_rustc_interface::{
    abi, hir,
    index::{self, IndexVec},
    middle::ty,
    span::symbol,
};

use super::{
    data::*,
    generics::{GArgs, GParams},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RustTyDecomposition<'tcx> {
    pub ty: RustTy<'tcx>,
    pub args: GArgs<'tcx>,
}

impl<'tcx, Ctxt> HasRegions<'tcx, Ctxt> for RustTyDecomposition<'tcx> {
    fn regions(&self, _ctxt: Ctxt) -> IndexVec<RegionIdx, PcgRegion> {
        self.args
            .args()
            .iter()
            .flat_map(|arg| arg.as_region())
            .map(|region| region.into())
            .unique()
            .collect()
    }
}

impl<'tcx> RustTyDecomposition<'tcx> {
    /// Decomposes a rustc `ty::Ty` into the core type used to generate a Viper
    /// domain/predicate and its type arguments (not used for the Viper
    /// definition). For example, for the function:
    /// ```no_run
    /// struct MyStruct<I: Iterator> {
    ///     field: I::Item
    /// }
    /// fn foo<T: Iterator<Item = i32>>(x: MyStruct<T>) { ... }
    /// ```
    /// when encoding the argument type, this should be called as
    /// ```no_run
    /// let decomp = from_ty(tcx, "MyStruct<T>", "<T: Iterator<Item = i32>>")
    /// // which yields
    /// RustTyDecomposition {
    ///     ty: TyData { params: "<I: Iterator>", specifics: "MyStruct(I::Item)" }
    ///     args: GArgs { args: "<T>", context: "<T: Iterator<Item = i32>>" }
    /// }
    /// ```
    /// The `ty` field is agnostic of the client's generic arguments while the
    /// `args` field captures everything from the client's side. Note that we
    /// guarantee that `decomp.ty.params.len() == decomp.args.len()`.
    ///
    /// To recursively encode the struct itself, one should walk the
    /// `decomp.ty.specifics` and call `RustFieldData::decompose` with
    /// `decomp.ty.params`.
    ///
    /// To figure out which casts are required from the client side (e.g. when
    /// unfolding), one should walk the `decomp.ty.specifics` and call
    /// `RustFieldData::decompose_compare_normalize` with `decomp.ty.params`
    /// and `decomp.args`.
    pub fn from_ty(
        ty: ty::Ty<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
        context: impl Into<GParams<'tcx>>,
    ) -> Self {
        let (ty, args) = TyData::<'tcx, RustTyDatas>::from_ty(ty, tcx, context.into());
        Self { ty, args }
    }

    /// Same as `from_ty` to get a `RustTyDecomposition` for use in encoding,
    /// but requires fewer arguments when the type is known to be primitive.
    pub fn from_prim_ty(ty: ty::Ty<'tcx>) -> Self {
        assert!(ty.is_primitive());
        let (ty, args) = TyData::<'tcx, RustTyDatas>::from_prim_ty(ty);
        Self { ty, args }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RustTyNormalized<'tcx> {
    pub param: RustTy<'tcx>,
    pub concrete: RustTy<'tcx>,
    pub args: GArgs<'tcx>,
}

/// A to-be decomposed Rust type. We need this since we cannot infinitely
/// decompose recursive datatypes (instead fields are left as `LazyRustTy` and
/// decomposed as needed when recursing).
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LazyRustTy<'tcx>(ty::Ty<'tcx>);

impl<'tcx> LazyRustTy<'tcx> {
    pub fn new(ty: ty::Ty<'tcx>) -> Self {
        Self(ty)
    }

    pub fn new_slice(tys: &'tcx [ty::Ty<'tcx>]) -> &'tcx [Self] {
        // SAFETY: `LazyRustTy` is `repr(transparent)` over `ty::Ty`
        let ptr = tys as *const [ty::Ty<'tcx>] as *const [Self];
        unsafe { &*ptr }
    }
}

impl<'tcx> LazyRustTy<'tcx> {
    /// Decomposes the field's type into a `RustTyDecomposition` (to be used
    /// when recursing over the fields of a containing `RustTy`).
    /// The passed `params` should be those of the containing `RustTy::params`.
    pub fn decompose(&self, params: GParams<'tcx>) -> RustTyDecomposition<'tcx> {
        vir::with_vcx(|vcx| RustTyDecomposition::from_ty(self.0, vcx.tcx(), params))
    }

    /// Decomposes the field's type into a `RustTyDecomposition` (to be used
    /// when recursing over the fields of a containing `RustTy`).
    /// The passed `args` should be those of the containing `RustTyDecomposition::args`.
    ///
    /// This differs from `Self::decompose` in that it substitutes the `args`
    /// removing definitional generics. For example a `Foo<i32>` with definition
    /// `struct Foo<T>(T);` would yield `i32` instead of `T` when called on the
    /// field of `Foo`.
    pub fn decompose_normalize(&self, args: GArgs<'tcx>) -> RustTyDecomposition<'tcx> {
        vir::with_vcx(|vcx| {
            RustTyDecomposition::from_ty(args.normalize(self.0), vcx.tcx(), args.context())
        })
    }

    /// Similarly to `Self::decompose`, this decomposes the fields type.
    /// However, it tries to normalize the type first and only returns a
    /// decomposition if the type was a `TySpecifics::Param` and is now a
    /// concrete type. For example, when called on the `field: I::Item` of the
    /// following example:
    /// ```no_run
    /// struct MyStruct<I: Iterator> {
    ///     field: I::Item
    /// }
    /// fn foo<T: Iterator<Item = i32>>(x: MyStruct<T>) { ... }
    /// ```
    /// For which the initial decomposition of the argument `MyStruct<T>` was
    /// ```no_run
    /// let decomp = RustTyDecomposition {
    ///     ty: TyData { params: "<I: Iterator>", specifics: "MyStruct(I::Item)" }
    ///     args: GArgs { args: "<T>", context: "<T: Iterator<Item = i32>>" }
    /// };
    /// // one would call
    /// let field = decomp.ty.specifics.expect_struct().fields[0];
    /// let decomp_field = field.decompose_compare_normalize(decomp.ty.params, decomp.args)
    /// // where `decomp_field` would be
    /// Some(RustTyDecomposition {
    ///     ty: TyData { params: "", specifics: "i32" }
    ///     args: GArgs { args: "", context: "<T: Iterator<Item = i32>>" }
    /// });
    /// ```
    pub fn decompose_compare_normalize(
        &self,
        params: GParams<'tcx>,
        args: GArgs<'tcx>,
    ) -> Option<RustTyNormalized<'tcx>> {
        let param = self.decompose(params).ty;
        let TySpecifics::Param(..) = &param.specifics else {
            return None;
        };
        let RustTyDecomposition { ty, args } = self.decompose_normalize(args);
        if let TySpecifics::Param(..) = &ty.specifics {
            None
        } else {
            Some(RustTyNormalized {
                param,
                concrete: ty,
                args,
            })
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct RustTyDatas;

impl<'tcx> TyDatas<'tcx> for RustTyDatas {
    type TyData = RustTyData<'tcx>;
    type PrimitiveData = ty::Ty<'tcx>;
    type ParamData = ();
    type ImmRefData = LazyRustTy<'tcx>;
    type MutRefData = LazyRustTy<'tcx>;
    type StructData = ();
    type FieldData = RustFieldData<'tcx>;
    type EnumData = RustEnumData<'tcx>;
    type VariantData = RustVariantData;
}

/// An internal representation of a `ty::Ty`. Contains all that we care about
/// for encoding types, does not include any of the type arguments (i.e. drops
/// the `<i32>` part of `MyStruct<i32>`).
pub type RustTy<'tcx> = Ty<'tcx, RustTyDatas>;
pub type RustOpaque<'tcx> = <RustTyDatas as TyDatas<'tcx>>::OpaqueData;
pub type RustParam<'tcx> = <RustTyDatas as TyDatas<'tcx>>::ParamData;
pub type RustPrimitive<'tcx> = <RustTyDatas as TyDatas<'tcx>>::PrimitiveData;
pub type RustImmRef<'tcx> = <RustTyDatas as TyDatas<'tcx>>::ImmRefData;
pub type RustMutRef<'tcx> = <RustTyDatas as TyDatas<'tcx>>::MutRefData;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RustTyData<'tcx> {
    pub name: symbol::Symbol,
    pub params: GParams<'tcx>,
}

impl<'tcx> RustTyData<'tcx> {
    pub fn name(&self) -> &str {
        self.name.as_str()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RustFieldData<'tcx> {
    pub name: symbol::Symbol,
    pub fid: abi::FieldIdx,
    ty: LazyRustTy<'tcx>,
}

impl<'tcx> RustFieldData<'tcx> {
    pub fn ty(self) -> LazyRustTy<'tcx> {
        self.ty
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RustVariantData {
    pub name: symbol::Symbol,
    pub vid: abi::VariantIdx,
    pub discr_val: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RustEnumData<'tcx> {
    pub discr: ty::Ty<'tcx>,
}

// Internal methods

impl<'tcx> Deref for RustFieldData<'tcx> {
    type Target = LazyRustTy<'tcx>;
    fn deref(&self) -> &Self::Target {
        &self.ty
    }
}

impl<'tcx> TyData<'tcx, RustTyDatas> {
    fn from_ty(
        ty: ty::Ty<'tcx>,
        tcx: ty::TyCtxt<'tcx>,
        context: GParams<'tcx>,
    ) -> (RustTy<'tcx>, GArgs<'tcx>) {
        // We normalize since we may be translating a type such as the field of
        // `struct MyStruct<T: Iterator<Item = i32>>(T::Item);` where `ty` is
        // `T::Item` and `context` is `<T: Iterator<Item = i32>>`. In this case
        // we want to encode the struct as if it had an `i32` field (without any
        // Param generics).
        let ty = context.normalize(ty);

        let name = Self::ty_name(ty);
        let (params, args) = Self::identity_for_ty(ty, context.is_trait_extern_spec());
        let args = GArgs::new(context, args);
        let data = RustTyData {
            name: symbol::Symbol::intern(&name),
            params,
        };
        let specifics = TySpecifics::from_ty(ty);
        let inhabited = !ty.is_privately_uninhabited(tcx, ty::TypingEnv::fully_monomorphized());
        (Self::new(data, inhabited, specifics).alloc(), args)
    }

    fn from_prim_ty(ty: ty::Ty<'tcx>) -> (RustTy<'tcx>, GArgs<'tcx>) {
        let name = Self::prim_ty_name(ty);
        let (params, args) = Self::identity_for_prim_ty(ty);
        let args = GArgs::new(params, args);
        let data = RustTyData {
            name: symbol::Symbol::intern(&name),
            params,
        };
        let specifics = TySpecifics::from_prim_ty(ty);
        (Self::new(data, true, specifics).alloc(), args)
    }

    fn ty_name(ty: ty::Ty<'tcx>) -> String {
        match ty.kind() {
            _ if ty.is_primitive() => Self::prim_ty_name(ty),
            ty::TyKind::Str => String::from("Str"),
            ty::TyKind::Adt(adt, _) => {
                vir::with_vcx(|vcx| vcx.tcx().item_name(adt.did()).to_ident_string())
            }
            ty::TyKind::Tuple(params) => format!("{}_Tuple", params.len()),
            ty::TyKind::Never => String::from("Never"),
            ty::TyKind::Ref(_, _, ty::Mutability::Not) => String::from("Ref_immutable"),
            ty::TyKind::Ref(_, _, ty::Mutability::Mut) => String::from("Ref_mutable"),
            ty::TyKind::RawPtr(_, ty::Mutability::Not) => String::from("RawPtr_immutable"),
            ty::TyKind::RawPtr(_, ty::Mutability::Mut) => String::from("RawPtr_mutable"),
            ty::TyKind::Param(_) | ty::TyKind::Alias(..) => String::from("Param"),
            ty::TyKind::Closure(def_id, _) => vir::with_vcx(|vcx| {
                let def_key = vcx.tcx().def_key(def_id);
                match def_key.disambiguated_data.data {
                    // Asking for the item_name of a closure triggers an ICE in
                    // the compiler, so we give it a name based on its parent.
                    hir::definitions::DefPathData::Closure => format!(
                        "{}_Closure_{}",
                        vcx.tcx().item_name(hir::def_id::DefId {
                            krate: def_id.krate,
                            index: def_key.parent.unwrap()
                        }),
                        def_key.disambiguated_data.disambiguator,
                    ),
                    _ => vcx.tcx().item_name(*def_id).to_ident_string(),
                }
            }),
            ty::TyKind::FnPtr(..) => String::from("FnPtr"),
            other => unimplemented!("ty_name for {:?}", other),
        }
    }

    fn prim_ty_name(ty: ty::Ty<'tcx>) -> String {
        assert!(ty.is_primitive());
        match ty.kind() {
            ty::TyKind::Bool => String::from("Bool"),
            ty::TyKind::Char => String::from("Char"),
            ty::TyKind::Int(kind) => format!("Int_{}", kind.name_str()),
            ty::TyKind::Uint(kind) => format!("UInt_{}", kind.name_str()),
            ty::TyKind::Float(kind) => format!("Float_{}", kind.name_str()),
            _ => unreachable!(),
        }
    }

    /// For the ty `MyStruct<i32>` (with defn
    /// `struct MyStruct<T: Iterator<Item = i32>> { ... }`), returns
    /// `([<T: Iterator<Item = i32>>], [i32])`.
    pub(super) fn identity_for_ty(
        ty: ty::Ty<'tcx>,
        is_trait_extern_spec: bool,
    ) -> (GParams<'tcx>, ty::GenericArgsRef<'tcx>) {
        let (params, args) = match *ty.kind() {
            _ if ty.is_primitive() => return Self::identity_for_prim_ty(ty),
            ty::TyKind::Adt(adt, args) => (GParams::from(adt.did()), args),
            ty::TyKind::Tuple(tys) => {
                let gtys = (0..tys.len()).map(|idx| TySpecifics::new_param_ty(idx as u32));
                (
                    GParams::empty_env(Self::args_from_tys(gtys)),
                    Self::args_from_tys(tys),
                )
            }
            ty::TyKind::Array(ty, cst) => {
                let gty = TySpecifics::new_param_ty(0).into();
                let gcst = TySpecifics::new_param_const(1).into();
                let gparams = Self::args_from_generics([gty, gcst]);
                (
                    GParams::empty_env(gparams),
                    Self::args_from_generics([ty.into(), cst.into()]),
                )
            }
            ty::TyKind::Slice(ty) | ty::TyKind::RawPtr(ty, _) => {
                let gty = Self::args_from_tys([TySpecifics::new_param_ty(0)]);
                (GParams::empty_env(gty), Self::args_from_tys([ty]))
            }
            ty::TyKind::Ref(region, ty, _) => {
                // TODO: what lifetime should we use here?
                let param_region = vir::with_vcx(|vcx| vcx.tcx().lifetimes.re_erased.into());
                let param_ty = TySpecifics::new_param_ty(1).into();
                let gty = Self::args_from_generics([param_region, param_ty]);
                (
                    GParams::empty_env(gty),
                    Self::args_from_generics([region.into(), ty.into()]),
                )
            }
            ty::TyKind::Alias(..) | ty::TyKind::Param(_) => {
                let gty = Self::args_from_tys([TySpecifics::new_param_ty(0)]);
                (GParams::empty_env(gty), Self::args_from_tys([ty]))
            }
            ty::TyKind::Closure(did, args) => vir::with_vcx(|vcx| {
                let identity = ty::List::identity_for_item(vcx.tcx(), did);
                let gargs = vcx.tcx().mk_args(identity.as_closure().parent_args());
                let args = vcx.tcx().mk_args(args.as_closure().parent_args());
                (
                    GParams::new(gargs, vcx.tcx().param_env(did), is_trait_extern_spec),
                    args,
                )
            }),
            ty::TyKind::Never | ty::TyKind::Str | ty::TyKind::FnPtr(..) => {
                (GParams::empty(), ty::GenericArgs::empty())
            }
            _ => todo!("instantiate_identity_for_type for {:?}", ty),
        };
        params.check(args);
        (params, args)
    }

    fn identity_for_prim_ty(ty: ty::Ty<'tcx>) -> (GParams<'tcx>, ty::GenericArgsRef<'tcx>) {
        assert!(ty.is_primitive());
        (GParams::empty(), ty::GenericArgs::empty())
    }

    fn args_from_tys(tys: impl IntoIterator<Item = ty::Ty<'tcx>>) -> ty::GenericArgsRef<'tcx> {
        Self::args_from_generics(tys.into_iter().map(ty::GenericArg::from))
    }

    fn args_from_generics(
        tys: impl IntoIterator<Item = ty::GenericArg<'tcx>>,
    ) -> ty::GenericArgsRef<'tcx> {
        vir::with_vcx(|vcx| vcx.tcx().mk_args_from_iter(tys.into_iter()))
    }
}

impl<'tcx> TySpecifics<'tcx, RustTyDatas> {
    fn from_ty(ty: ty::Ty<'tcx>) -> Self {
        if ty.is_primitive() {
            return Self::from_prim_ty(ty);
        }
        if crate::encoders::is_type_trusted(ty) {
            return TySpecifics::mk_opaque(());
        }

        match ty.kind() {
            ty::TyKind::Adt(adt, _) => Self::from_adt(*adt),
            ty::TyKind::Tuple(args) => {
                let fields = args
                    .iter()
                    .enumerate()
                    .map(|(i, _)| RustFieldData {
                        name: symbol::Symbol::intern(&format!("_{i}")),
                        fid: abi::FieldIdx::from_usize(i),
                        ty: LazyRustTy(Self::new_param_ty(i as u32)),
                    })
                    .collect::<Vec<_>>();
                TySpecifics::mk_structlike((), true, fields)
            }
            ty::TyKind::Array(..) | ty::TyKind::Slice(..) => {
                // TODO: add array/slice support
                TySpecifics::mk_opaque(())
            }
            ty::TyKind::Ref(_, _, mutability) => match mutability {
                ty::Mutability::Mut => {
                    TySpecifics::mk_mutref(LazyRustTy(TySpecifics::new_param_ty(1)))
                }
                ty::Mutability::Not => {
                    TySpecifics::mk_immref(LazyRustTy(TySpecifics::new_param_ty(1)))
                }
            },
            // TODO: add raw pointer support
            ty::TyKind::RawPtr(..) => TySpecifics::mk_opaque(()),
            ty::TyKind::Alias(..) | ty::TyKind::Param(_) => TySpecifics::mk_param(()),
            ty::TyKind::Closure(_, args) => {
                let captured = args.as_closure().upvar_tys();
                let fields = captured
                    .iter()
                    .enumerate()
                    .map(|(i, ty)| RustFieldData {
                        name: symbol::Symbol::intern(&format!("c{i}")),
                        fid: abi::FieldIdx::from_usize(i),
                        ty: LazyRustTy(ty),
                    })
                    .collect::<Vec<_>>();
                TySpecifics::mk_structlike((), true, fields)
            }
            ty::TyKind::Never => {
                let data = vir::with_vcx(|vcx| RustEnumData {
                    discr: vcx.tcx().types.isize,
                });
                TySpecifics::mk_enumlike(data, false, Vec::new())
            }
            // TODO: add str support
            ty::TyKind::Str => TySpecifics::mk_opaque(()),
            _ => TySpecifics::mk_opaque(()),
        }
    }

    fn from_prim_ty(ty: ty::Ty<'tcx>) -> Self {
        assert!(ty.is_primitive());
        TySpecifics::mk_primitive(ty)
    }

    fn from_adt(adt: ty::AdtDef<'tcx>) -> Self {
        if adt.is_box() {
            let fields = vec![RustFieldData {
                name: symbol::Symbol::intern("deref"),
                fid: abi::FieldIdx::from_usize(0),
                ty: LazyRustTy(Self::new_param_ty(0)),
            }];
            return TySpecifics::mk_structlike((), true, fields);
        }

        match adt.adt_kind() {
            ty::AdtKind::Struct => {
                let data = Self::from_struct(adt.non_enum_variant());
                Self::StructLike(data)
            }
            ty::AdtKind::Enum => {
                let data = Self::from_enum(adt);
                Self::EnumLike(data)
            }
            ty::AdtKind::Union => {
                // TODO: add union support
                Self::mk_opaque(())
            }
        }
    }

    fn from_struct(variant: &ty::VariantDef) -> StructData<'tcx, RustTyDatas> {
        let fields = Self::from_fields(&variant.fields);
        StructData::new((), true, fields)
    }

    fn from_enum(adt: ty::AdtDef<'tcx>) -> EnumData<'tcx, RustTyDatas> {
        vir::with_vcx(|vcx| {
            use ty::util::IntTypeExt;
            let discr = adt.repr().discr_type().to_ty(vcx.tcx());
            let data = RustEnumData { discr };
            let variants = adt
                .discriminants(vcx.tcx())
                .map(|(vid, discr)| {
                    let variant = adt.variant(vid);
                    let fields = Self::from_fields(&variant.fields);
                    VariantData::new(
                        RustVariantData {
                            name: variant.name,
                            vid,
                            discr_val: discr.val,
                        },
                        true,
                        StructData::new((), true, fields),
                    )
                })
                .collect::<Vec<_>>();
            EnumData::new(data, true, variants)
        })
    }

    fn from_fields(
        fields: &index::IndexVec<abi::FieldIdx, ty::FieldDef>,
    ) -> Vec<RustFieldData<'tcx>> {
        fields
            .iter_enumerated()
            .map(|(fid, field)| {
                let ty = vir::with_vcx(|vcx| vcx.tcx().type_of(field.did).instantiate_identity());
                RustFieldData {
                    name: field.name,
                    fid,
                    ty: LazyRustTy(ty),
                }
            })
            .collect::<Vec<_>>()
    }

    fn new_param_ty(index: u32) -> ty::Ty<'tcx> {
        let name = match index {
            0 => symbol::Symbol::intern("T"),
            1 => symbol::Symbol::intern("U"),
            2 => symbol::Symbol::intern("V"),
            other => symbol::Symbol::intern(&format!("T{other}")),
        };
        vir::with_vcx(|vcx| ty::Ty::new_param(vcx.tcx(), index, name))
    }

    fn new_param_const(index: u32) -> ty::Const<'tcx> {
        let name = match index {
            0 => symbol::Symbol::intern("M"),
            1 => symbol::Symbol::intern("N"),
            other => symbol::Symbol::intern(&format!("N{other}")),
        };
        let param = ty::ParamConst { index, name };
        vir::with_vcx(|vcx| ty::Const::new_param(vcx.tcx(), param))
    }
}
