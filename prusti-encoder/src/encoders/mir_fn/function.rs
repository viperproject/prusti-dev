use prusti_interface::PrustiError;
use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, FunctionIdn, Reify};

use crate::encoders::{
    MirLocalDefEnc, MirLocalDefEncTask, MirPureEnc, MirPureEncTask, MirSpecEnc, Pure, PureKind,
    TyUsePureEnc,
    mir_fn::{CallTaskDescription, RustSignature},
    pure::spec::MirSpecEncMode,
    ty::{
        RustTyDecomposition,
        generics::{GArgCaster, GArgsCastEnc, GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc},
        use_pure::TyUsePure,
    },
};

/// The body of a `#[field_projection(a.b)]` spec function: the projection of
/// the field path `a.b` (which may name private fields: nothing here is
/// type-checked by rustc) from the referent of the function's first argument,
/// which must be a shared reference. The result is the field itself when the
/// return type is the field's type, or a reference pointing at the field in
/// place when it is a shared reference to the field's type. The outer error
/// is an encoding failure, the inner one a malformed projection.
fn field_projection_body<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, FunctionEnc>,
    def_id: DefId,
    params: GParams<'vir>,
    path: &[String],
    arg: vir::ExprSnap<'vir>,
) -> Result<Result<vir::ExprSnap<'vir>, String>, task_encoder::EncodeFullError<'vir, FunctionEnc>> {
    let sig = vcx
        .tcx()
        .fn_sig(def_id)
        .instantiate_identity()
        .skip_binder();
    let Some(ref_ty) = sig.inputs().first().copied() else {
        return Ok(Err("the function takes no argument".to_string()));
    };
    let ty::TyKind::Ref(_, self_ty, ty::Mutability::Not) = *ref_ty.kind() else {
        return Ok(Err(
            "the first argument must be a shared reference".to_string()
        ));
    };
    let ref_use = deps.require_dep::<TyUsePureEnc>(RustTyDecomposition::from_ty(ref_ty, params))?;
    let ref_data = ref_use.expect_immref();
    let (cur_ty, snap, addr) = match crate::encoders::ty::use_pure::project_field_path(
        vcx,
        deps,
        params,
        path,
        self_ty,
        ref_data.value_access(arg.downcast_ty()),
        ref_data.addr_access(arg.downcast_ty()),
    )? {
        Ok(projected) => projected,
        Err(message) => return Ok(Err(message)),
    };
    let ret_ty = sig.output();
    let same =
        |a: ty::Ty<'vir>, b: ty::Ty<'vir>| vcx.tcx().erase_regions(a) == vcx.tcx().erase_regions(b);
    if same(ret_ty, cur_ty) {
        return Ok(Ok(snap));
    }
    if let ty::TyKind::Ref(_, inner, ty::Mutability::Not) = *ret_ty.kind()
        && same(inner, cur_ty)
    {
        let ret_use =
            deps.require_dep::<TyUsePureEnc>(RustTyDecomposition::from_ty(ret_ty, params))?;
        let unit = RustTyDecomposition::from_ty(vcx.tcx().types.unit, params);
        let metadata = deps
            .require_dep::<TyUsePureEnc>(unit)?
            .zst_to_snap()
            .unwrap()
            .upcast_ty();
        return Ok(Ok(ret_use
            .expect_immref()
            .prim_to_snap(addr, metadata, snap)
            .upcast_ty()));
    }
    Ok(Err(format!(
        "the return type `{ret_ty}` is neither the field's type `{cur_ty}` nor a shared \
        reference to it"
    )))
}

// Function wrapper

pub struct FunctionCallEnc;

#[derive(Debug, Clone)]
pub struct FunctionCallEncOutput<'vir> {
    function: FunctionEncOutputRef<'vir>,
    ty_args: GArgsTy<'vir>,
    arg_tys: Vec<TyUsePure<'vir>>,
    inputs: Vec<GArgCaster<'vir, Pure>>,
    output: GArgCaster<'vir, Pure>,
}

impl<'vir> FunctionCallEncOutput<'vir> {
    /// `true` if the callee is `#[pure_unstable]` and therefore expects the
    /// interior-mutability value `Map` argument (callers must use
    /// [`Self::call_pure_unstable`]).
    pub fn is_pure_unstable(&self) -> bool {
        self.function.pure_unstable.is_some()
    }

    /// The `inner_only` flag of a `#[pure_unstable]` callee: `true` means it
    /// takes the level-0 map only, `false` the combined level-0/level-1 map.
    pub fn pure_unstable_inner_only(&self) -> bool {
        self.function
            .pure_unstable
            .expect("not a pure_unstable function")
    }

    /// Calls the definitional function `f_`. In impure code a pure function
    /// is called as a method (its `MethodEnc`), whose postcondition ties the
    /// result to this application.
    pub fn call_pure<Curr, Next>(
        &self,
        args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.call_casted(self.function.function_ref, args, &[])
    }

    /// Call a `#[pure_unstable]` callee, passing the interior-mutability value
    /// `Map` as the extra Viper argument.
    pub fn call_pure_unstable<Curr, Next>(
        &self,
        args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
        inner_map: vir::ExprGenMap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.call_casted(self.function.function_ref, args, &[inner_map])
    }

    fn call_casted<Curr, Next>(
        &self,
        function: FnSig<'vir>,
        mut args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
        maps: &[vir::ExprGenMap<'vir, Curr, Next>],
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        assert_eq!(self.inputs.len(), args.len());
        for ((arg, caster), ty) in args
            .iter_mut()
            .zip(self.inputs.iter())
            .zip(self.arg_tys.iter())
        {
            *arg = caster.cast_to_callee_ctx(ty.dummy_ref_address(*arg));
        }
        let call = function.call()(&args, maps, self.ty_args.get_ty(), self.ty_args.get_const());
        self.output.cast_to_caller_ctx(call)
    }
}

impl TaskEncoder for FunctionCallEnc {
    task_encoder::encoder_cache!(FunctionCallEnc);
    const ENCODER_NAME: &'static str = "function call encoder";
    type TaskDescription<'tcx> = CallTaskDescription<'tcx>;
    type OutputFullDependency<'vir> = FunctionCallEncOutput<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let (callee_def_id, assoc_enc) = task_key.trait_call(deps)?;
        let function_ref = if let Some(assoc_enc) = assoc_enc {
            FunctionEncOutputRef {
                function_ref: assoc_enc.call_stub_pure_function.unwrap(),
                // Trait-call stubs do not (yet) carry the value `Map`.
                pure_unstable: None,
            }
        } else {
            deps.require_ref::<FunctionEnc>(task_key.callee)?
        };
        let signature = RustSignature::new(callee_def_id);
        let ty_args = deps.require_dep::<GArgsTyEnc>(task_key.gargs)?;
        let inputs = signature
            .inputs
            .iter()
            .map(|ty| {
                let normalized = ty.decompose_compare_normalize(signature.gparams, task_key.gargs);
                deps.require_dep::<GArgsCastEnc<Pure>>(normalized)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let normalized = signature
            .output
            .decompose_compare_normalize(signature.gparams, task_key.gargs);
        let output = deps.require_dep::<GArgsCastEnc<Pure>>(normalized)?;
        let arg_tys = signature
            .inputs
            .iter()
            .map(|ty| {
                let ty_task = ty.decompose_normalize(task_key.gargs);
                deps.require_dep::<TyUsePureEnc>(ty_task)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok((
            (),
            FunctionCallEncOutput {
                function: function_ref,
                ty_args,
                inputs,
                output,
                arg_tys,
            },
        ))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        FunctionEnc::emit_outputs(program);
    }
}

// Function encoder

struct FunctionEnc;

/// The function signature carries a `ManyMap` slot (between the snapshot args
/// and the type/const generics) for the interior-mutability value `Map` of
/// `#[pure_unstable]` functions. It is empty (length 0) for all other
/// functions, so their emitted Viper signature is unchanged.
type FnSig<'vir> =
    FunctionIdn<'vir, (vir::ManySnap, vir::ManyMap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>;

#[derive(Debug, Clone)]
struct FunctionEncOutputRef<'vir> {
    function_ref: FnSig<'vir>,
    /// `Some` if this is a `#[pure_unstable]` function (so its signature has a
    /// non-empty `ManyMap` slot that callers must fill); the `bool` is the
    /// `inner_only` flag.
    pure_unstable: Option<bool>,
}

impl<'vir> OutputRefAny for FunctionEncOutputRef<'vir> {}

#[derive(Debug, Clone, Copy)]
struct FunctionEncOutput<'vir> {
    function: vir::Function<'vir>,
}

#[derive(Clone, Debug)]
pub enum FunctionEncError {}

impl TaskEncoder for FunctionEnc {
    task_encoder::encoder_cache!(FunctionEnc);
    const ENCODER_NAME: &'static str = "function encoder";
    type TaskDescription<'tcx> = DefId;

    type OutputRef<'vir> = FunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = FunctionEncOutput<'vir>;

    type EncodingError = FunctionEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let def_id = *task_key;
            let local_defs = deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                def_id,
                all_locals: true,
            })?;

            tracing::debug!("encoding {def_id:?}");

            let name = vir::ViperIdent::from_def_id(vcx, def_id);
            let function_ident = vir::vir_format_identifier!(vcx, "f_{name}");
            let arg_types = vcx.alloc_slice(&local_defs.snap_ty_args().collect::<Vec<_>>());
            let return_type = local_defs.snap_ty_return();
            let params = GParams::from(def_id);
            let generics = deps.require_dep::<GenericParamsEnc>(params)?;
            // `#[pure_unstable]` functions take the interior-mutability value
            // `Map` as an extra argument (so e.g. a borrow-count function can
            // read the current state). Non-pure-unstable functions and
            // `#[interior_mut]` accessors (whose marking only declares a level)
            // have an empty `ManyMap` slot, leaving their signature unchanged.
            let pure_unstable = crate::encoders::get_pure_unstable_encoding(def_id);
            let map_decls: &[vir::LocalDeclMap<'vir>] = if pure_unstable.is_some() {
                vcx.alloc_slice(&[crate::encoders::ty::interior_mut::pure_unstable_map_decl(
                    deps,
                )?])
            } else {
                &[]
            };
            let map_types = vcx.alloc_slice(&map_decls.iter().map(|d| d.ty).collect::<Vec<_>>());
            let function_ref = FunctionIdn::new(
                function_ident,
                (
                    arg_types,
                    map_types,
                    generics.ty_args(),
                    generics.const_args(),
                ),
                return_type,
            );
            deps.emit_output_ref(
                def_id,
                FunctionEncOutputRef {
                    function_ref,
                    pure_unstable,
                },
            )?;

            let spec =
                deps.require_dep::<MirSpecEnc>((def_id, def_id, MirSpecEncMode::PureWithResult))?;

            let expr = if let Some(path) = crate::encoders::get_field_projection(def_id) {
                let arg = vcx.mk_local_ex(local_defs.local_decl_args().next().unwrap());
                match field_projection_body(vcx, deps, def_id, params, &path, arg)? {
                    Ok(expr) => Some(expr),
                    Err(message) => {
                        vcx.emit_early_error(PrustiError::incorrect(
                            format!("invalid `#[field_projection]`: {message}"),
                            vcx.tcx().def_span(def_id).into(),
                        ));
                        None
                    }
                }
            } else if !crate::encoders::encodes_body(def_id) {
                None
            } else {
                // Encode the body of the function. If it cannot be encoded (e.g. it
                // uses an unsupported feature), report it and emit the function
                // abstractly (keeping its contract) rather than failing entirely
                // (which would leave a dangling reference for callers).
                match deps.require_dep::<MirPureEnc>(MirPureEncTask {
                    encoding_depth: 0,
                    kind: PureKind::Pure,
                    parent_def_id: def_id,
                    gargs: params.identity_args(),
                }) {
                    Ok(out) => {
                        let expr = out
                            .expr
                            .reify(vcx, (def_id, spec.pre_args, vir::OldLabel::None));
                        assert!(
                            expr.ty() == return_type,
                            "expected {:?}, got {:?}",
                            return_type,
                            expr.ty()
                        );
                        Some(expr)
                    }
                    Err(err) => {
                        let (message, span) = super::dep_error(&err);
                        vcx.emit_early_error(PrustiError::unsupported(
                            format!(
                                "cannot encode function body `{}`: {message}",
                                vcx.tcx().def_path_str(def_id),
                            ),
                            span.unwrap_or_else(|| vcx.tcx().def_span(def_id)).into(),
                        ));
                        None
                    }
                }
            };

            tracing::debug!("finished {def_id:?}");

            let mut posts = spec
                .posts
                .iter()
                .map(|(post, _)| {
                    // use inhale-exhale expression to prevent viper checking that
                    // the function body expression satisfies the postcondition:
                    // that's checked in the method encoding of this function.
                    vcx.mk_inhale_exhale_expr(*post, vcx.mk_bool::<true>())
                })
                .collect::<Vec<_>>();
            let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
            // An inline `#[interior_mut]` accessor returns a pointer to its
            // object: the pointer's address IS the identity that keys the
            // object (`im_id_*`). Stating this lets pointer equalities in
            // specs (`a.as_ptr() == b.as_ptr()`) imply key equalities, i.e.
            // aliasing of the interior-mutable objects.
            if crate::encoders::spec::is_interior_mut_accessor(def_id)
                && crate::encoders::get_field_projection(def_id).is_none()
            {
                let sig = vcx
                    .tcx()
                    .fn_sig(def_id)
                    .instantiate_identity()
                    .skip_binder();
                let ref_ty = sig.inputs()[0];
                if let ty::TyKind::Ref(_, self_ty, _) = *ref_ty.kind()
                    && sig.output().is_raw_ptr()
                {
                    let self_decomp = RustTyDecomposition::from_ty(self_ty, params);
                    // Encodes the type's IM functions, which emit `im_id_*`.
                    deps.require_dep::<crate::encoders::ty::interior_mut::TyInteriorMutUseEnc>(
                        self_decomp,
                    )?;
                    let holder_snap = deps.require_dep::<TyUsePureEnc>(self_decomp)?.snapshot;
                    let ref_use = deps.require_dep::<TyUsePureEnc>(
                        RustTyDecomposition::from_ty(ref_ty, params),
                    )?;
                    let self_value = ref_use
                        .expect_immref()
                        .value_access(vcx.mk_local_ex(func_args[0]).downcast_ty());
                    let ret_use = deps.require_dep::<TyUsePureEnc>(
                        RustTyDecomposition::from_ty(sig.output(), params),
                    )?;
                    let result: vir::ExprSnap<'vir> = vcx.mk_result(return_type);
                    let ptr_addr = ret_use.expect_raw().address_access(result.downcast_ty());
                    let im_id = crate::encoders::ty::interior_mut::im_id_function(
                        vcx,
                        def_id,
                        holder_snap,
                        &generics,
                    );
                    posts.push(vcx.mk_eq_expr(
                        ptr_addr,
                        im_id.call()(self_value, generics.ty_exprs(), generics.const_exprs()),
                    ));
                }
            }
            // `im_deref(ptr)`: the primitive read of interior-mutable state,
            // defined as the lookup of the object `(address(ptr), T)` in the
            // function's interior-mutability snapshot.
            if prusti_interface::environment::EnvQuery::new(vcx.tcx())
                .has_prusti_attribute(def_id, "im_deref")
            {
                let sig = vcx
                    .tcx()
                    .fn_sig(def_id)
                    .instantiate_identity()
                    .skip_binder();
                let ptr_use = deps.require_dep::<TyUsePureEnc>(RustTyDecomposition::from_ty(
                    sig.inputs()[0],
                    params,
                ))?;
                let ret_use = deps.require_dep::<TyUsePureEnc>(RustTyDecomposition::from_ty(
                    sig.output(),
                    params,
                ))?;
                let ptr_addr = ptr_use
                    .expect_raw()
                    .address_access(vcx.mk_local_ex(func_args[0]).downcast_ty());
                let result: vir::ExprSnap<'vir> = vcx.mk_result(return_type);
                let ret_data = ret_use.expect_immref();
                let tys = crate::encoders::ty::interior_mut::ImTys::new(deps);
                let key =
                    (tys.key.constructor)(&[ptr_addr.as_dyn(), generics.ty_exprs()[0].as_dyn()]);
                let map = vcx.mk_local_ex(map_decls[0]);
                posts.push(vcx.mk_eq_expr(ret_data.addr_access(result.downcast_ty()), ptr_addr));
                posts.push(
                    vcx.mk_bin_op_expr(
                        vir::BinOpKind::Implies,
                        vcx.mk_set_in_expr(key, vcx.mk_map_domain_expr(map)),
                        vcx.mk_eq_expr(
                            ret_data.value_access_generic(result.downcast_ty()),
                            vcx.mk_map_lookup_expr(map, key).downcast_ty::<vir::PSnap>(),
                        ),
                    )
                    .downcast_ty(),
                );
            }
            let posts = vcx.alloc_slice(&posts);

            let function = vcx.mk_function(
                function_ref,
                (
                    &func_args,
                    map_decls,
                    generics.ty_decls(),
                    generics.const_decls(),
                ),
                &[],
                posts,
                expr.is_none().then_some(&vir::DecreasesGenData::Star),
                expr,
            );
            Ok((FunctionEncOutput { function }, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            program.add_function(output.function);
        }
    }
}
