use std::ops::Deref;

use itertools::Itertools;
use pcg::borrow_pcg::region_projection::{HasRegions, PcgRegion, RegionIdx};
use prusti_interface::environment::EnvQuery;
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
    pub maybe_inhabited: bool,
}

impl<'tcx, Ctxt: Copy> HasRegions<'tcx, Ctxt> for RustTyDecomposition<'tcx> {
    fn regions(&self, _ctxt: Ctxt) -> IndexVec<RegionIdx, PcgRegion<'tcx>> {
        self.args
            .args()
            .iter()
            .flat_map(|arg| arg.walk())
            .filter_map(|arg| arg.as_region().map(PcgRegion::from))
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
    pub fn from_ty(ty: ty::Ty<'tcx>, context: impl Into<GParams<'tcx>>) -> Self {
        TyData::<'tcx, RustTyDatas>::from_ty(ty, context.into())
    }

    pub fn from_real() -> Self {
        let data = RustTyData {
            name: symbol::Symbol::intern("Real"),
            params: GParams::empty(),
            erased_ty: None,
        };
        let specifics = TySpecifics::Builtin(RustBuiltinData::BuiltinReal);
        Self {
            ty: TyData::<'tcx, RustTyDatas>::new(data, specifics).alloc(),
            args: GArgs::new(GParams::empty(), &[]),
            maybe_inhabited: true,
        }
    }

    /// Same as `from_ty` to get a `RustTyDecomposition` for use in encoding,
    /// but requires fewer arguments when the type is known to be primitive.
    pub fn from_prim_ty(ty: ty::Ty<'tcx>) -> Self {
        assert!(ty.is_primitive());
        TyData::<'tcx, RustTyDatas>::from_prim_ty(ty)
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
    /// when recursing over the fields of a containing `RustTy` to construct
    /// e.g. a predicate - i.e. when the definition of the predicate is
    /// independent of the context/generic args).
    /// The passed `params` should be those of the containing `RustTy::params`.
    ///
    /// For example a `Foo<i32>` with definition `struct Foo<T>(T);`, then
    /// decomposing the field of the struct would yield `TySpecifics::Param`
    /// with arguments `<T>` (i.e. the `i32` from the context is lost).
    pub fn decompose(&self, params: GParams<'tcx>) -> RustTyDecomposition<'tcx> {
        RustTyDecomposition::from_ty(self.0, params)
    }

    /// Decomposes the field's type into a `RustTyDecomposition` (to be used
    /// when recursing over the fields of a containing `RustTy`
    /// non-transparently, e.g. when predicates of fields should be added
    /// directly to a method itself).
    /// The passed `args` should be those of the containing `RustTyDecomposition::args`.
    pub fn decompose_context(
        &self,
        params: GParams<'tcx>,
        args: GArgs<'tcx>,
    ) -> RustTyDecomposition<'tcx> {
        let mut decomp = self.decompose(params);
        decomp.args = decomp.args.substitute(args);
        decomp
    }

    /// Decomposes the field's type into a `RustTyDecomposition` (to be used
    /// when recursing over the fields of a containing `RustTy`).
    /// The passed `args` should be those of the containing `RustTyDecomposition::args`.
    ///
    /// This differs from `Self::decompose` in that it substitutes the `args`
    /// removing definitional generics. For example a `Foo<i32>` with definition
    /// `struct Foo<T>(T);` would yield `i32` instead of `T` when called on the
    /// field of `Foo`.
    pub(super) fn decompose_normalize(&self, args: GArgs<'tcx>) -> RustTyDecomposition<'tcx> {
        RustTyDecomposition::from_ty(args.normalize(self.0), args.context())
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
        let RustTyDecomposition { ty, args, .. } = self.decompose_normalize(args);
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
    type ArrayData = LazyRustTy<'tcx>;
    type ImmRefData = LazyRustTy<'tcx>;
    type MutRefData = LazyRustTy<'tcx>;
    type StructData = ();
    type FieldData = RustFieldData<'tcx>;
    type EnumData = RustEnumData<'tcx>;
    type VariantData = RustVariantData;
    type BuiltinData = RustBuiltinData;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RustBuiltinData {
    BuiltinReal,
    BuiltinGhost,
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
pub type RustBuiltin<'tcx> = <RustTyDatas as TyDatas<'tcx>>::BuiltinData;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RustTyData<'tcx> {
    pub name: symbol::Symbol,
    pub erased_ty: Option<ty::Ty<'tcx>>,
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
    fn from_ty(ty: ty::Ty<'tcx>, context: GParams<'tcx>) -> RustTyDecomposition<'tcx> {
        // We normalize since we may be translating a type such as the field of
        // `struct MyStruct<T: Iterator<Item = i32>>(T::Item);` where `ty` is
        // `T::Item` and `context` is `<T: Iterator<Item = i32>>`. In this case
        // we want to encode the struct as if it had an `i32` field (without any
        // Param generics).
        let ty = context.normalize(ty);

        let name = Self::ty_name(ty);
        let (erased_ty, params, args) = Self::identity_for_ty(ty, context.is_trait_extern_spec());
        let args = GArgs::new(context, args);
        let data = RustTyData {
            name: symbol::Symbol::intern(&name),
            erased_ty: erased_ty.into(),
            params,
        };
        let specifics = TySpecifics::from_ty(erased_ty);
        let maybe_inhabited =
            vir::with_vcx(|vcx| !ty.is_privately_uninhabited(vcx.tcx(), context.typing_env()));
        RustTyDecomposition {
            ty: Self::new(data, specifics).alloc(),
            args,
            maybe_inhabited,
        }
    }

    fn from_prim_ty(ty: ty::Ty<'tcx>) -> RustTyDecomposition<'tcx> {
        let name = Self::prim_ty_name(ty);
        let (erased_ty, params, args) = Self::identity_for_prim_ty(ty);
        let args = GArgs::new(params, args);
        let data = RustTyData {
            name: symbol::Symbol::intern(&name),
            erased_ty: erased_ty.into(),
            params,
        };
        let specifics = TySpecifics::from_prim_ty(ty);
        RustTyDecomposition {
            ty: Self::new(data, specifics).alloc(),
            args,
            maybe_inhabited: true,
        }
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
            ty::TyKind::Array(..) => String::from("Array"),
            ty::TyKind::Slice(..) => String::from("Slice"),
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
    /// `(MyStruct<T>, [<T: Iterator<Item = i32>>], [i32])`.
    pub(super) fn identity_for_ty(
        ty: ty::Ty<'tcx>,
        is_trait_extern_spec: bool,
    ) -> (ty::Ty<'tcx>, GParams<'tcx>, ty::GenericArgsRef<'tcx>) {
        let tcx = vir::with_vcx(|vcx| vcx.tcx());
        let (new_ty, params, args) = match *ty.kind() {
            _ if ty.is_primitive() => return Self::identity_for_prim_ty(ty),
            ty::TyKind::Adt(adt, args) => {
                let params = GParams::from(adt.did());
                let new_ty = ty::Ty::new_adt(tcx, adt, params.rust_params());
                (new_ty, params, args)
            }
            ty::TyKind::Tuple(tys) => {
                let gtys = (0..tys.len()).map(|idx| TySpecifics::new_param_ty(idx as u32));
                (
                    ty::Ty::new_tup_from_iter(tcx, gtys.clone()),
                    GParams::empty_env(Self::args_from_tys(gtys)),
                    Self::args_from_tys(tys),
                )
            }
            ty::TyKind::Array(ty, cst) => {
                let gcst = TySpecifics::new_param_const(0);
                let gty = TySpecifics::new_param_ty(1);
                let gargs = Self::args_from_generics([gcst.into(), gty.into()]);
                let predicate = tcx.mk_predicate(ty::Binder::dummy(ty::PredicateKind::Clause(
                    ty::ClauseKind::ConstArgHasType(gcst, tcx.types.usize),
                )));
                let param_env = ty::ParamEnv::new(tcx.mk_clauses(&[predicate.expect_clause()]));
                (
                    ty::Ty::new_array_with_const_len(tcx, gty, gcst),
                    GParams::new(gargs, param_env, false),
                    Self::args_from_generics([cst.into(), ty.into()]),
                )
            }
            ty::TyKind::Slice(ty) => {
                let gty = TySpecifics::new_param_ty(0);
                let params = GParams::empty_env(Self::args_from_tys([gty]));
                let new_ty = ty::Ty::new_slice(tcx, gty);
                (new_ty, params, Self::args_from_tys([ty]))
            }
            ty::TyKind::RawPtr(ty, mutbl) => {
                let gty = TySpecifics::new_param_ty(0);
                let params = GParams::empty_env(Self::args_from_tys([gty]));
                let new_ty = ty::Ty::new_ptr(tcx, gty, mutbl);
                (new_ty, params, Self::args_from_tys([ty]))
            }
            ty::TyKind::Ref(region, ty, mutbl) => {
                // TODO: what lifetime should we use here?
                let param_region = tcx.lifetimes.re_erased;
                let gty = TySpecifics::new_param_ty(1);
                (
                    ty::Ty::new_ref(tcx, param_region, gty, mutbl),
                    GParams::empty_env(Self::args_from_generics([param_region.into(), gty.into()])),
                    Self::args_from_generics([region.into(), ty.into()]),
                )
            }
            ty::TyKind::Alias(_, _) | ty::TyKind::Param(_) => {
                let gty = TySpecifics::new_param_ty(0);
                let gargs = Self::args_from_tys([gty]);
                // Note: an `Alias` is turned into a `Param` here with the alias
                // itself as the type argument.
                (gty, GParams::empty_env(gargs), Self::args_from_tys([ty]))
            }
            ty::TyKind::Closure(did, args) => {
                let identity = ty::List::identity_for_item(tcx, did);
                let gargs = tcx.mk_args(identity.as_closure().parent_args());
                let args = tcx.mk_args(args.as_closure().parent_args());
                (
                    ty::Ty::new_closure(tcx, did, identity),
                    GParams::new(gargs, tcx.param_env(did), is_trait_extern_spec),
                    args,
                )
            }
            ty::TyKind::Never | ty::TyKind::Str | ty::TyKind::FnPtr(..) => {
                (ty, GParams::empty(), ty::GenericArgs::empty())
            }
            _ => todo!("instantiate_identity_for_type for {:?}", ty),
        };
        params.check(args);
        (new_ty, params, args)
    }

    fn identity_for_prim_ty(
        ty: ty::Ty<'tcx>,
    ) -> (ty::Ty<'tcx>, GParams<'tcx>, ty::GenericArgsRef<'tcx>) {
        assert!(ty.is_primitive());
        (ty, GParams::empty(), ty::GenericArgs::empty())
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
                    .map(|(i, inner)| RustFieldData {
                        name: symbol::Symbol::intern(&format!("_{i}")),
                        fid: abi::FieldIdx::from_usize(i),
                        ty: LazyRustTy(inner),
                    })
                    .collect::<Vec<_>>();
                TySpecifics::mk_structlike((), fields)
            }
            ty::TyKind::Array(inner, _) => TySpecifics::ArrayLike(ArrayData {
                slice: false,
                data: LazyRustTy(*inner),
            }),
            ty::TyKind::Slice(inner) => TySpecifics::ArrayLike(ArrayData {
                slice: true,
                data: LazyRustTy(*inner),
            }),
            ty::TyKind::Ref(_, inner, mutability) => match mutability {
                ty::Mutability::Mut => TySpecifics::mk_mutref(LazyRustTy(*inner)),
                ty::Mutability::Not => TySpecifics::mk_immref(LazyRustTy(*inner)),
            },
            // TODO: add raw pointer support
            ty::TyKind::RawPtr(..) => TySpecifics::mk_opaque(()),
            ty::TyKind::Alias(..) | ty::TyKind::Param(_) => TySpecifics::mk_param(()),
            ty::TyKind::Closure(_, args) => {
                let captured = args.as_closure().upvar_tys();
                let fields = vir::with_vcx(|vcx| {
                    captured
                        .iter()
                        .enumerate()
                        .map(|(i, ty)| RustFieldData {
                            name: symbol::Symbol::intern(&format!("c{i}")),
                            fid: abi::FieldIdx::from_usize(i),
                            ty: LazyRustTy(vcx.tcx().erase_regions(ty)),
                        })
                        .collect::<Vec<_>>()
                });
                TySpecifics::mk_structlike((), fields)
            }
            ty::TyKind::Never => {
                let data = vir::with_vcx(|vcx| RustEnumData {
                    discr: vcx.tcx().types.isize,
                });
                TySpecifics::mk_enumlike(data, Vec::new())
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
            TySpecifics::mk_structlike((), fields)
        } else if vir::with_vcx(|vcx| {
            EnvQuery::new(vcx.tcx()).is_adt_in_crate(adt, "prusti_contracts")
        }) {
            match adt.non_enum_variant().name.to_string().as_str() {
                "Real" => Self::Builtin(RustBuiltinData::BuiltinReal),
                "Ghost" => Self::Builtin(RustBuiltinData::BuiltinGhost),
                s => panic!("Found unrecognized builtin {s}"),
            }
        } else {
            match adt.adt_kind() {
                ty::AdtKind::Struct => Self::StructLike(Self::from_struct(adt.non_enum_variant())),
                ty::AdtKind::Enum => Self::EnumLike(Self::from_enum(adt)),
                ty::AdtKind::Union => {
                    // TODO: add union support
                    Self::mk_opaque(())
                }
            }
        }
    }

    fn from_struct(variant: &ty::VariantDef) -> StructData<'tcx, RustTyDatas> {
        let fields = Self::from_fields(&variant.fields);
        StructData::new((), fields)
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
                        StructData::new((), fields),
                    )
                })
                .collect::<Vec<_>>();
            EnumData::new(data, variants)
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
