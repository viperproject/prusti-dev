use prusti_interface::specs::typed::ExternSpecKind;
use prusti_rustc_interface::{
    middle::ty,
    span::{def_id::DefId, symbol},
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, HasType};

use crate::encoders::{
    TyUsePureEnc,
    ty::{
        RustParamData, RustTyDecomposition,
        data::TySpecifics,
        generics::{GArgs, GArgsTyEnc, GParamVariant, r#trait::TraitEnc},
        lifted::TyConstructorEnc,
    },
};

/// The list of defined parameters in a given context. E.g. the type parameters
/// `T` and `U` in the body of the function `fn foo<T, U>(t: T) -> U { ... }`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GParams<'tcx> {
    params: ty::GenericArgsRef<'tcx>,
    env: ty::ParamEnv<'tcx>,
    /// Trait extern_specs will have a synthetic `Prusti_T_Self` parameter
    /// instead of the actual `Self` parameter to which the spec is attached to.
    /// This flag indicates whether this is the case, so that we can replace it
    /// with the actual `Self` parameter when needed.
    is_trait_extern_spec: bool,
}

impl<'tcx> GParams<'tcx> {
    pub fn new(
        params: ty::GenericArgsRef<'tcx>,
        env: ty::ParamEnv<'tcx>,
        is_trait_extern_spec: bool,
    ) -> Self {
        GParams {
            params,
            env,
            is_trait_extern_spec,
        }
    }

    /// Gets the generic params for a given def_id. Additionally if this is a
    /// special extern_spec function for a trait, replaces the synthetic
    /// `Prusti_T_Self` parameter with the `Self` that the actual trait has.
    pub fn new_maybe_extern(def_id: DefId, kind: Option<ExternSpecKind>) -> Self {
        vir::with_vcx(|vcx| {
            let params = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
            let env = vcx.tcx().param_env(def_id);
            let is_trait_extern_spec = matches!(kind, Some(ExternSpecKind::Trait));
            Self::new(params, env, is_trait_extern_spec)
        })
    }

    pub fn empty() -> Self {
        Self::empty_env(ty::GenericArgs::empty())
    }

    pub fn empty_env(params: ty::GenericArgsRef<'tcx>) -> Self {
        Self::new(params, ty::ParamEnv::empty(), false)
    }

    pub fn count(self) -> usize {
        self.ty_params().count() + self.const_params().count()
    }

    pub fn is_trait_extern_spec(self) -> bool {
        self.is_trait_extern_spec
    }

    pub(super) fn expect_const(self, idx: usize) -> (ty::ParamConst, ty::Ty<'tcx>) {
        self.const_ty(self.params[idx].expect_const())
    }

    fn const_ty(self, const_: ty::Const<'tcx>) -> (ty::ParamConst, ty::Ty<'tcx>) {
        let ty::ConstKind::Param(p) = const_.kind() else {
            unreachable!()
        };
        (p, p.find_const_ty_from_env(self.env))
    }

    pub fn check(self, args: &'tcx [ty::GenericArg<'tcx>]) {
        assert_eq!(
            self.params.len(),
            args.len(),
            "generic args length mismatch, context {self:?}, args {args:?}"
        );
    }

    /// Tries to normalize associated types of the corresponding type. Returns
    /// `Some` if managed to normalize (or there were no associated types), else
    /// returns None.
    pub fn try_normalize(self, ty: ty::Ty<'tcx>) -> Option<ty::Ty<'tcx>> {
        use prusti_rustc_interface::{
            middle::ty,
            trait_selection::{
                infer::{InferCtxt, TyCtxtInferExt},
                traits::{
                    NormalizeExt, ObligationCause, ScrubbedTraitError, TraitEngine, TraitEngineExt,
                },
            },
        };
        vir::with_vcx(|vcx| {
            // Normalize associated types
            let ifctxt: InferCtxt = vcx.tcx().infer_ctxt().build(ty::TypingMode::PostAnalysis);
            let mut fulfill_cx = <dyn TraitEngine<ScrubbedTraitError> as TraitEngineExt<
                ScrubbedTraitError,
            >>::new(&ifctxt);
            // TODO: is this correct?
            let kinds = self
                .params
                .iter()
                .map(|param| match param.kind() {
                    ty::GenericArgKind::Lifetime(_) => {
                        ty::BoundVariableKind::Region(ty::BoundRegionKind::Anon)
                    }
                    ty::GenericArgKind::Type(_) => ty::BoundVariableKind::Ty(ty::BoundTyKind::Anon),
                    ty::GenericArgKind::Const(_) => ty::BoundVariableKind::Const,
                })
                .collect::<Vec<_>>();
            let kinds = vcx.tcx().mk_bound_variable_kinds(&kinds);
            let ty = ty::Binder::bind_with_vars(ty, kinds);
            let nty = ifctxt
                .at(&ObligationCause::dummy(), self.env)
                .deeply_normalize(ty, &mut *fulfill_cx);
            nty.ok().map(|nty| nty.skip_binder())
        })
    }

    /// Same as `try_normalize`, but returns the argument type if it failed to
    /// normalize it.
    pub fn normalize(self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        self.try_normalize(ty).unwrap_or(ty)
    }

    pub fn rust_params(self) -> ty::GenericArgsRef<'tcx> {
        self.params
    }

    pub fn typing_env(self) -> ty::TypingEnv<'tcx> {
        let mut env = ty::TypingEnv::fully_monomorphized();
        env.param_env = self.env;
        env
    }

    fn params<T>(
        self,
        f: impl Fn(ty::GenericArg<'tcx>) -> Option<T>,
    ) -> impl Iterator<Item = (usize, T)> {
        self.params
            .iter()
            .enumerate()
            .filter_map(move |(i, arg)| f(arg).map(|arg| (i, arg)))
    }

    fn ty_params(self) -> impl Iterator<Item = (usize, ty::ParamTy)> {
        self.params(ty::GenericArg::as_type).map(move |(i, ty)| {
            let ty::TyKind::Param(mut param) = *ty.kind() else {
                unreachable!("expected type parameter, got {ty:?}")
            };
            if self.is_trait_extern_spec && param.name.as_str() == "Prusti_T_Self" {
                param.name = symbol::Symbol::intern("Self");
            }
            (i, param)
        })
    }

    fn const_params(self) -> impl Iterator<Item = (usize, ty::ParamConst, ty::Ty<'tcx>)> {
        self.params(ty::GenericArg::as_const)
            .map(move |(i, const_)| {
                let (param, ty) = self.const_ty(const_);
                (i, param, ty)
            })
    }
}

impl<'vir> From<DefId> for GParams<'vir> {
    fn from(did: DefId) -> Self {
        Self::new_maybe_extern(did, None)
    }
}

/// Handles everything relating to the encoding of generic parameters (both for
/// Rust functions and type definitions). Used to turn e.g. the Rust function
/// `fn foo<T, U>(x: U)` into the Viper `method foo(x: Ref, T: Type, U: Type)`
/// (handles the type parameters).
pub struct GenericParamsEnc;
#[derive(Debug, Clone)]
pub struct GenericParams<'vir> {
    ty_args: &'vir [vir::TypeTyVal<'vir>],
    ty_decls: Vec<vir::LocalDeclTyVal<'vir>>,
    ty_exprs: Vec<vir::ExprTyVal<'vir>>,

    const_args: &'vir [vir::TypeCSnap<'vir>],
    const_decls: Vec<vir::LocalDeclCSnap<'vir>>,
    const_exprs: Vec<vir::ExprCSnap<'vir>>,

    // maps generic param index to either ty or const index
    indices: Vec<Result<usize, usize>>,
}

impl<'vir> GenericParams<'vir> {
    pub fn ty_args(&self) -> &'vir [vir::TypeTyVal<'vir>] {
        self.ty_args
    }

    pub fn ty_decls(&self) -> &[vir::LocalDeclTyVal<'vir>] {
        &self.ty_decls
    }

    pub fn ty_exprs(&self) -> &[vir::ExprTyVal<'vir>] {
        &self.ty_exprs
    }

    pub fn const_args(&self) -> &'vir [vir::TypeCSnap<'vir>] {
        self.const_args
    }

    pub fn const_decls(&self) -> &[vir::LocalDeclCSnap<'vir>] {
        &self.const_decls
    }

    pub fn const_exprs(&self) -> &[vir::ExprCSnap<'vir>] {
        &self.const_exprs
    }

    pub fn const_expr(&self, param: ty::ParamConst) -> vir::ExprCSnap<'vir> {
        self.const_exprs()[self.map_idx(param.index).unwrap_err()]
    }

    fn map_idx(&self, index: u32) -> Result<usize, usize> {
        let result = self.indices[index as usize];
        assert!(
            result.ok().is_none_or(|i| i != usize::MAX),
            "trying to map invalid generic param index {index} (possibly a region?)"
        );
        result
    }

    // TODO: type preconditions do not currently work
    /*
    /// Creates a pure assertion representing e.g. `arg: List<T>` -> `typeof(arg) == List_ty(T)`
    pub fn ty_assertion<E: TaskEncoder + 'vir + ?Sized>(&self, deps: &mut TaskEncoderDependencies<'vir, E>, snap: vir::ExprSnap<'vir>, ty: RustTyDecomposition<'vir>) -> vir::ExprBool<'vir> {
        let vcx = vir::with_vcx(|vcx| vcx);
        let ty_expr = self.ty_expr(deps, vcx, ty);
        let typeof_ref = deps
            .require_ref::<TypeOfEnc>(ty.ty)
            .unwrap();
        let typeof_call = typeof_ref.typeof_function.call()(snap);
        vcx.mk_eq_expr(typeof_call, ty_expr)
    }
    */

    pub(super) fn ty_expr<E: TaskEncoder + 'vir + ?Sized>(
        &self,
        deps: &mut TaskEncoderDependencies<'vir, E>,
        ty: RustTyDecomposition<'vir>,
    ) -> Result<vir::ExprTyVal<'vir>, EncodeFullError<'vir, E>> {
        if let TySpecifics::Param(RustParamData::Generic) = &ty.ty.specifics {
            let param = ty.args.expect_param();
            return Ok(match param {
                GParamVariant::Param(p) => self.ty_exprs[self.map_idx(p.index).unwrap()],
                GParamVariant::Alias(alias) => vir::with_vcx(|vcx| {
                    let tcx = vcx.tcx();
                    let trait_did = tcx.associated_item(alias.def_id).container_id(tcx);
                    let trait_data = deps.require_ref::<TraitEnc>(trait_did).unwrap();
                    let args = GArgs::new(ty.args.context, alias.args);
                    let args = deps.require_dep::<GArgsTyEnc>(args).unwrap();
                    (trait_data.assoc_types[&alias.def_id])(args.get_ty(), args.get_const())
                }),
            });
        }
        let ty_constructor = deps.require_ref::<TyConstructorEnc>(ty.ty)?.ty_constructor;
        let args = deps.require_dep::<GArgsTyEnc>(ty.args)?;
        Ok(ty_constructor(args.get_ty(), args.get_const()))
    }
}

impl TaskEncoder for GenericParamsEnc {
    task_encoder::encoder_cache!(GenericParamsEnc);
    const ENCODER_NAME: &'static str = "generic params encoder";
    type TaskDescription<'tcx> = GParams<'tcx>;
    type OutputFullDependency<'vir> = GenericParams<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let sanitize = |name: symbol::Symbol, index: u32| {
                vir::ViperIdent::sanitize(vcx, &format!("{name}${index}")).to_str()
            };

            let mut indices = vec![Ok(usize::MAX); task_key.params.len()];
            let ty_decls = task_key
                .ty_params()
                .enumerate()
                .map(|(i, (gi, param))| {
                    indices[gi] = Ok(i);
                    vcx.mk_local_decl(sanitize(param.name, param.index), vir::TYPE_TYVAL)
                })
                .collect::<Vec<_>>();
            let ty_args = vcx.alloc_slice(&vec![vir::TYPE_TYVAL; ty_decls.len()]);
            let ty_exprs = ty_decls
                .iter()
                .map(|decl| vcx.mk_local_ex(*decl))
                .collect::<Vec<_>>();

            let const_decls = task_key
                .const_params()
                .enumerate()
                .map(|(i, (gi, p, ty))| {
                    indices[gi] = Err(i);
                    let ty = RustTyDecomposition::from_prim_ty(ty);
                    let lifted_const = deps.require_ref::<TyUsePureEnc>(ty)?;
                    Ok(vcx.mk_local_decl(
                        sanitize(p.name, p.index),
                        lifted_const.snapshot.downcast_ty(),
                    ))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let const_args = const_decls.iter().map(|decl| decl.ty()).collect::<Vec<_>>();
            let const_args = vcx.alloc_slice(&const_args);
            let const_exprs = const_decls
                .iter()
                .map(|decl| vcx.mk_local_ex(*decl))
                .collect::<Vec<_>>();

            let output = GenericParams {
                ty_args,
                ty_decls,
                ty_exprs,
                const_args,
                const_decls,
                const_exprs,
                indices,
            };
            Ok(((), output))
        })
    }
}
