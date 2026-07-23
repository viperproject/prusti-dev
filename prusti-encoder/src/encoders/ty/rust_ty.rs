use std::ops::Deref;

use prusti_interface::environment::EnvQuery;
use prusti_rustc_interface::{abi, hir, index, middle::ty, span::symbol};

use super::{
    data::*,
    generics::{GArgs, GParams},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RustTyDecomposition<'tcx> {
    pub ty: RustTy<'tcx>,
    pub args: GArgs<'tcx>,
    /// Whether this (concrete) type might be inhabited. `None` when this was
    /// created in `RustTyDecomposition::identity` from a `RustTy` where we
    /// cannot know the value.
    pub maybe_inhabited: Option<bool>,
}

impl<'tcx> RustTyDecomposition<'tcx> {
    fn new(ty: RustTy<'tcx>, args: GArgs<'tcx>, maybe_inhabited: Option<bool>) -> Self {
        ty.params.check(args.args());
        RustTyDecomposition {
            ty,
            args,
            maybe_inhabited,
        }
    }

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

    /// Same as `from_ty` to get a `RustTyDecomposition` for use in encoding,
    /// but requires fewer arguments when the type is known to be primitive.
    pub fn from_prim_ty(ty: ty::Ty<'tcx>) -> Self {
        assert!(ty.is_primitive());
        TyData::<'tcx, RustTyDatas>::from_prim_ty(ty)
    }

    /// When you only have a `RustTy<'tcx>` but you want to use the
    /// `TyUsePureEnc`. We cannot determine `maybe_inhabited` so it
    /// is left `None`; the pure encoder never reads it, and passing
    /// this decomposition to `TyUseImpureEnc` will panic.
    pub fn identity(ty: RustTy<'tcx>) -> Self {
        let args = GArgs::new(ty.params, ty.params.rust_params());
        Self::new(ty, args, None)
    }

    pub fn param() -> RustTy<'tcx> {
        let gty = TyData::<RustTyDatas>::args_from_tys([TySpecifics::new_param_ty(0)]);
        let data = RustTyData {
            name: symbol::Symbol::intern("Param"),
            params: GParams::empty_env(gty),
        };
        let specifics = TySpecifics::Param(RustParamData::Generic);
        TyData::<RustTyDatas>::new(data, specifics).alloc()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RustTyNormalized<'tcx> {
    pub param: RustTy<'tcx>,
    pub concrete: RustTyDecomposition<'tcx>,
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

    /// The (sized) type parameter at the given index. `decompose`d against a
    /// `GParams` that declares it, this yields a `Param` decomposition whose
    /// argument is that type variable. Used to make a builtin method generic
    /// over one of the reference's type parameters.
    pub fn new_param_ty(index: u32) -> Self {
        Self(TySpecifics::new_param_ty(index))
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
    pub fn decompose_normalize(&self, args: GArgs<'tcx>) -> RustTyDecomposition<'tcx> {
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
        let concrete = self.decompose_normalize(args);
        if let TySpecifics::Param(..) = &concrete.ty.specifics {
            None
        } else {
            Some(RustTyNormalized { param, concrete })
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct RustTyDatas;

impl<'tcx> TyDatas<'tcx> for RustTyDatas {
    type TyData = RustTyData<'tcx>;
    type PrimitiveData = ty::Ty<'tcx>;
    type ParamData = RustParamData;
    type ArrayData = LazyRustTy<'tcx>;
    type ImmRefData = RefData<'tcx>;
    type MutRefData = RefData<'tcx>;
    /// Raw pointers reuse the reference `RefData` (metadata + pointee), but are
    /// encoded conservatively as their own `Raw` kind: the snapshot exposes the
    /// address and pointer metadata without reasoning about the pointee.
    type RawData = RefData<'tcx>;
    type StructData = ();
    type FieldData = RustFieldData<'tcx>;
    type EnumData = RustEnumData<'tcx>;
    type VariantData = RustVariantData;
    type BuiltinData = RustBuiltinData<'tcx>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RustBuiltinData<'tcx> {
    Int,
    Real,
    Set(LazyRustTy<'tcx>),
    Multiset(LazyRustTy<'tcx>),
    Seq(LazyRustTy<'tcx>),
    Map(LazyRustTy<'tcx>, LazyRustTy<'tcx>),
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
pub type RustRaw<'tcx> = <RustTyDatas as TyDatas<'tcx>>::RawData;
pub type RustBuiltin<'tcx> = <RustTyDatas as TyDatas<'tcx>>::BuiltinData;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RustTyData<'tcx> {
    pub name: symbol::Symbol,
    pub params: GParams<'tcx>,
}

impl<'tcx> RustTyData<'tcx> {
    pub fn name(&self) -> &str {
        self.name.as_str()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RefData<'tcx> {
    /// Will always be a `pointee_metadata_projection` (`TyKind::Alias`).
    pub metadata: LazyRustTy<'tcx>,
    /// Will always be `ParamTy { index: 1, .. }`, the concrete type can be
    /// found in the `args` of the containing `RustTyDecomposition`.
    pub referent: LazyRustTy<'tcx>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RustVariantData {
    pub name: symbol::Symbol,
    pub vid: abi::VariantIdx,
    pub discr_val: u128,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RustEnumData<'tcx> {
    pub discr: ty::Ty<'tcx>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RustParamData {
    /// Represents actual type parameters.
    Generic,
    /// Represents a trait object (`dyn Trait`).
    Dyn,
}

// Internal methods

impl<'tcx> Deref for RustFieldData<'tcx> {
    type Target = LazyRustTy<'tcx>;
    fn deref(&self) -> &Self::Target {
        &self.ty
    }
}

impl<'tcx> TyData<'tcx, RustTyDatas> {
    pub fn ref_data(&self) -> Option<RefData<'tcx>> {
        match &self.specifics {
            TySpecifics::ImmRef(data) | TySpecifics::MutRef(data) | TySpecifics::Raw(data) => {
                Some(*data)
            }
            _ => None,
        }
    }

    fn from_ty(ty: ty::Ty<'tcx>, context: GParams<'tcx>) -> RustTyDecomposition<'tcx> {
        // We normalize since we may be translating a type such as the field of
        // `struct MyStruct<T: Iterator<Item = i32>>(T::Item);` where `ty` is
        // `T::Item` and `context` is `<T: Iterator<Item = i32>>`. In this case
        // we want to encode the struct as if it had an `i32` field (without any
        // Param generics).
        let ty = context.normalize(ty);

        let name = Self::ty_name(ty);
        let (params, args) = Self::identity_for_ty(ty, context.is_trait_extern_spec());
        let args = GArgs::new(context, args);
        let specifics = TySpecifics::from_ty(ty);
        // Whether the type might be inhabited. This is independent of
        // lifetimes, but `is_privately_uninhabited` ICEs on types that still
        // carry region artifacts (inference vars like `'?21` from the
        // panic/format machinery, or escaping bound/placeholder regions like
        // `'^2`). So first make the type lifetime-free: erase free & inference
        // regions, then replace any escaping bound regions with `'erased`. Only
        // genuinely non-ground, *non-lifetime* features (type/const params or
        // inference vars) can then still block the query, in which case we
        // answer conservatively (possibly-inhabited).
        let maybe_inhabited = vir::with_vcx(|vcx| {
            use prusti_rustc_interface::middle::ty::{FnMutDelegate, TypeVisitableExt};
            let tcx = vcx.tcx();
            let layout_ty = tcx.replace_escaping_bound_vars_uncached(
                tcx.erase_regions(ty),
                FnMutDelegate {
                    regions: &mut |_| tcx.lifetimes.re_erased,
                    types: &mut |_| ty::Ty::new_misc_error(tcx),
                    consts: &mut |_| ty::Const::new_misc_error(tcx),
                },
            );
            let groundish = !layout_ty.has_infer() && !layout_ty.has_param();
            !groundish || !layout_ty.is_privately_uninhabited(tcx, context.typing_env())
        });
        let data = RustTyData {
            name: symbol::Symbol::intern(&name),
            params,
        };
        RustTyDecomposition::new(
            Self::new(data, specifics).alloc(),
            args,
            Some(maybe_inhabited),
        )
    }

    fn from_prim_ty(ty: ty::Ty<'tcx>) -> RustTyDecomposition<'tcx> {
        let name = Self::prim_ty_name(ty);
        let (params, args) = Self::identity_for_prim_ty(ty);
        let args = GArgs::new(params, args);
        let data = RustTyData {
            name: symbol::Symbol::intern(&name),
            params,
        };
        let specifics = TySpecifics::from_prim_ty(ty);
        RustTyDecomposition::new(Self::new(data, specifics).alloc(), args, Some(true))
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
                // Asking for the item_name of a closure triggers an ICE in
                // the compiler, so name it after its nearest non-closure
                // ancestor (closures can nest, e.g. a quantifier's closure
                // inside an assertion's closure).
                let mut def_id = *def_id;
                let mut key = vcx.tcx().def_key(def_id);
                let mut name = String::new();
                while let hir::definitions::DefPathData::Closure = key.disambiguated_data.data {
                    name = format!("_Closure_{}{name}", key.disambiguated_data.disambiguator);
                    def_id.index = key.parent.unwrap();
                    key = vcx.tcx().def_key(def_id);
                }
                format!("{}{name}", vcx.tcx().item_name(def_id).to_ident_string())
            }),
            ty::TyKind::FnPtr(..) => String::from("FnPtr"),
            ty::TyKind::Array(..) => String::from("Array"),
            ty::TyKind::Slice(..) => String::from("Slice"),
            ty::TyKind::Dynamic(..) => String::from("Dyn"),
            ty::TyKind::Foreign(def_id) => {
                vir::with_vcx(|vcx| vcx.tcx().item_name(*def_id).to_ident_string())
            }
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
            ty::TyKind::Array(ty, cst) => vir::with_vcx(|vcx| {
                let gcst = TySpecifics::new_param_const(0).into();
                let gty = TySpecifics::new_param_ty(1).into();
                let gparams = Self::args_from_generics([gcst, gty]);
                let predicate =
                    vcx.tcx()
                        .mk_predicate(ty::Binder::dummy(ty::PredicateKind::Clause(
                            ty::ClauseKind::ConstArgHasType(
                                gcst.expect_const(),
                                vcx.tcx().types.usize,
                            ),
                        )));
                let param_env =
                    ty::ParamEnv::new(vcx.tcx().mk_clauses(&[predicate.expect_clause()]));
                (
                    GParams::new(gparams, param_env, false),
                    Self::args_from_generics([cst.into(), ty.into()]),
                )
            }),
            ty::TyKind::Slice(ty) => {
                let gty = Self::args_from_tys([TySpecifics::new_param_ty(0)]);
                (GParams::empty_env(gty), Self::args_from_tys([ty]))
            }
            ty::TyKind::RawPtr(pointee, _) => {
                // Like a reference, a raw pointer's pointer-metadata type is
                // derived from the pointee via `<pointee as Pointee>::Metadata`
                // (see `RefData` below), so it has a single generic: the pointee.
                let pointee_ty = TySpecifics::new_param_ty(0).into();
                let gty = Self::args_from_generics([pointee_ty]);
                (
                    GParams::empty_env(gty),
                    Self::args_from_generics([pointee.into()]),
                )
            }
            ty::TyKind::Ref(region, inner, _) => {
                // The pointer-metadata type is derived from the referent (see
                // `RefData` below and `pointee_metadata_projection`), so a
                // reference has just two generics: the lifetime and the referent.
                // TODO: what lifetime should we use here?
                let param_region = vir::with_vcx(|vcx| vcx.tcx().lifetimes.re_erased.into());
                let param_ty = TySpecifics::new_param_ty(1).into();
                let gty = Self::args_from_generics([param_region, param_ty]);
                (
                    GParams::empty_env(gty),
                    Self::args_from_generics([region.into(), inner.into()]),
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
            ty::TyKind::Never
            | ty::TyKind::Str
            | ty::TyKind::FnPtr(..)
            | ty::TyKind::Dynamic(..)
            | ty::TyKind::Foreign(_) => (GParams::empty(), ty::GenericArgs::empty()),
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

        /// The `<Referent as core::ptr::Pointee>::Metadata` projection type.
        /// Taken from `pointee_metadata_ty_or_projection` in `rustc`
        fn pointee_metadata_projection<'tcx>(
            tcx: ty::TyCtxt<'tcx>,
            referent: ty::Ty<'tcx>,
        ) -> ty::Ty<'tcx> {
            let metadata_did = tcx.require_lang_item(
                hir::LangItem::Metadata,
                prusti_rustc_interface::span::DUMMY_SP,
            );
            ty::Ty::new_projection(tcx, metadata_did, [referent])
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
                TySpecifics::mk_structlike((), fields)
            }
            ty::TyKind::Array(_, _) => TySpecifics::ArrayLike(ArrayData {
                slice: false,
                data: LazyRustTy(Self::new_param_ty(1)),
            }),
            ty::TyKind::Slice(_) => TySpecifics::ArrayLike(ArrayData {
                slice: true,
                data: LazyRustTy(Self::new_param_ty(0)),
            }),
            ty::TyKind::Ref(_, _, mutability) => {
                // The referent is generic parameter 1; its pointer metadata is
                // derived as `<referent as Pointee>::Metadata` rather than being
                // a separate generic parameter.
                let referent = Self::new_param_ty(1);
                let data = RefData {
                    metadata: LazyRustTy(vir::with_vcx(|vcx| {
                        pointee_metadata_projection(vcx.tcx(), referent)
                    })),
                    referent: LazyRustTy(referent),
                };
                match mutability {
                    ty::Mutability::Mut => TySpecifics::mk_mutref(data),
                    ty::Mutability::Not => TySpecifics::mk_immref(data),
                }
            }
            // Raw pointers get their own conservative `Raw` kind: we don't
            // reason about the pointee through them, but (like a reference) the
            // snapshot carries the address and pointer metadata so `PtrMetadata`
            // (e.g. a slice's length) can be read out. The pointee is generic
            // parameter 0; the metadata is derived from it as
            // `<pointee as Pointee>::Metadata`.
            ty::TyKind::RawPtr(..) => {
                let referent = Self::new_param_ty(0);
                TySpecifics::mk_raw(RefData {
                    metadata: LazyRustTy(vir::with_vcx(|vcx| {
                        pointee_metadata_projection(vcx.tcx(), referent)
                    })),
                    referent: LazyRustTy(referent),
                })
            }
            ty::TyKind::Alias(..) | ty::TyKind::Param(_) => {
                TySpecifics::mk_param(RustParamData::Generic)
            }
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
            // TODO: give dyn Trait a type witness parameter (the concrete type behind the
            // pointer), enabling virtual dispatch and distinguishing dyn TraitA from dyn TraitB.
            ty::TyKind::Dynamic(..) => TySpecifics::mk_param(RustParamData::Dyn),
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
            vcx.tcx().lang_items().get(hir::LangItem::DynMetadata) == Some(adt.did())
        }) {
            // `DynMetadata<dyn Trait>` is the metadata of a `&dyn`/`*dyn`
            // wide pointer. We never reason about vtable contents, so encode it
            // as an opaque snapshot rather than recursing into its `Foreign`
            // `VTable` field (which has no `ty_name`).
            TySpecifics::mk_opaque(())
        } else if vir::with_vcx(|vcx| {
            EnvQuery::new(vcx.tcx()).is_adt_in_crate(adt, "prusti_contracts")
        }) {
            match adt.non_enum_variant().name.to_string().as_str() {
                "Int" => Self::Builtin(RustBuiltinData::Int),
                "Real" => Self::Builtin(RustBuiltinData::Real),
                "Set" => Self::Builtin(RustBuiltinData::Set(LazyRustTy(Self::new_param_ty(0)))),
                "Multiset" => {
                    Self::Builtin(RustBuiltinData::Multiset(LazyRustTy(Self::new_param_ty(0))))
                }
                "Seq" => Self::Builtin(RustBuiltinData::Seq(LazyRustTy(Self::new_param_ty(0)))),
                "Map" => Self::Builtin(RustBuiltinData::Map(
                    LazyRustTy(Self::new_param_ty(0)),
                    LazyRustTy(Self::new_param_ty(1)),
                )),
                // `Ghost<T>` is encoded as if it were `struct Ghost<T>(T)`
                // (like `Box` above): the snapshot wraps the value of `T`.
                "Ghost" => {
                    let fields = vec![RustFieldData {
                        name: symbol::Symbol::intern("val"),
                        fid: abi::FieldIdx::from_usize(0),
                        ty: LazyRustTy(Self::new_param_ty(0)),
                    }];
                    TySpecifics::mk_structlike((), fields)
                }
                // TODO: support other builtins (e.g. `Seq`, `Map`, `Set`, etc.)
                s => todo!("Unimplemented builtin {s}"),
            }
        } else {
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
