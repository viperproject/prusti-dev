use pcg::borrow_pcg::FunctionData;
use prusti_interface::PrustiError;
use prusti_rustc_interface::{
    middle::{mir, ty},
    span::{def_id::DefId, symbol},
};
use task_encoder::{
    EncodeFullError, EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies,
};
use vir::MethodIdn;

use crate::encoders::{
    FunctionCallEnc, Impure, ImpureEncVisitor, MirLocalDefEnc, MirLocalDefEncTask, MirSpecEnc,
    WandEnc, WandEncTask,
    mir_fn::{CallTaskDescription, RustSignature, SpecBlocks, SpecBlocksEnc},
    pure::spec::MirSpecEncMode,
    ty::{
        generics::{
            GArgCaster, GArgs, GArgsCastEnc, GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc,
        },
        interior_mut::{
            BOUNDARY_IM0_MAP, ImTys, MapUnionEnc, TyInteriorMutUseEnc, im_boundary_maps, im_frame,
            im0_snap_sources, merge_pairs,
        },
    },
};

// Method wrapper

pub struct MethodCallEnc;

#[derive(Debug, Clone)]
pub struct MethodCallEncOutput<'vir> {
    method: MethodEncOutputRef<'vir>,
    ty_args: GArgsTy<'vir>,
    inputs: Vec<GArgCaster<'vir, Impure>>,
    output: GArgCaster<'vir, Impure>,
}

impl<'vir> MethodCallEncOutput<'vir> {
    pub fn call(
        &self,
        mut args: Vec<vir::ExprRef<'vir>>,
        ret: vir::ExprRef<'vir>,
    ) -> Vec<vir::Stmt<'vir>> {
        assert_eq!(self.inputs.len(), args.len());
        let generics = args.iter().zip(self.inputs.iter());
        let mut stmts: Vec<_> = generics
            .filter_map(|(arg, caster)| caster.cast_to_callee_ctx(arg))
            .collect();

        args.insert(0, ret);
        let call = (self.method.method_ref)(&args, self.ty_args.get_ty(), self.ty_args.get_const())
            .alloc();
        stmts.push(call);

        let result = self.output.cast_to_caller_ctx(ret);
        if let Some(result) = result {
            stmts.push(result);
        }
        stmts
    }
}

impl TaskEncoder for MethodCallEnc {
    task_encoder::encoder_cache!(MethodCallEnc);
    type TaskDescription<'tcx> = CallTaskDescription<'tcx>;
    type OutputFullDependency<'vir> = MethodCallEncOutput<'vir>;

    const ENCODER_NAME: &'static str = "method call encoder";

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let (callee_def_id, assoc_enc) = task_key.trait_call(deps)?;
        let method_ref = if let Some(assoc_enc) = assoc_enc {
            MethodEncOutputRef {
                method_ref: assoc_enc.call_stub_impure,
            }
        } else {
            deps.require_ref::<MethodEnc>(task_key.callee)?
        };
        let signature = RustSignature::new(callee_def_id);
        let ty_args = deps.require_dep::<GArgsTyEnc>(task_key.gargs)?;
        let inputs = signature
            .inputs
            .iter()
            .map(|ty| {
                let normalized = ty.decompose_compare_normalize(signature.gparams, task_key.gargs);
                deps.require_dep::<GArgsCastEnc<Impure>>(normalized)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let normalized = signature
            .output
            .decompose_compare_normalize(signature.gparams, task_key.gargs);
        let output = deps.require_dep::<GArgsCastEnc<Impure>>(normalized)?;
        Ok((
            (),
            MethodCallEncOutput {
                method: method_ref,
                ty_args,
                inputs,
                output,
            },
        ))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        MethodEnc::emit_outputs(program);
    }
}

// Method encoder

pub(super) struct MethodEnc;

#[derive(Debug, Clone)]
pub(super) struct MethodEncOutputRef<'vir> {
    method_ref: MethodIdn<'vir, (vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap)>,
}

impl<'vir> OutputRefAny for MethodEncOutputRef<'vir> {}

#[derive(Debug, Clone, Copy)]
pub(super) struct MethodEncOutput<'vir> {
    method: vir::Method<'vir>,
}

#[derive(Clone, Debug)]
pub enum MethodEncError {
    /// The method cannot be encoded; this was reported as an early error.
    Reported,
}

impl TaskEncoder for MethodEnc {
    task_encoder::encoder_cache!(MethodEnc);
    const ENCODER_NAME: &'static str = "method encoder";
    type TaskDescription<'tcx> = DefId;

    type OutputRef<'vir> = MethodEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = MethodEncOutput<'vir>;

    type EncodingError = MethodEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn error_reported(error: &Self::EncodingError) -> bool {
        matches!(error, MethodEncError::Reported)
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let def_id = *task_key;
        vir::with_vcx(|vcx| {
            let span = vcx.tcx().def_span(def_id);

            let arg_defs = deps.require_ref_spanned::<MirLocalDefEnc>(
                MirLocalDefEncTask::Local {
                    def_id,
                    all_locals: false,
                },
                span,
            )?;

            // Argument count for the Viper method:
            // - one (`Ref`) for the return place;
            // - one (`Ref`) for each MIR argument.
            //
            // Note that the return place is modelled as an argument of the
            // Viper method. This corresponds to an execution model where the
            // method can return data to the caller without a copy--it directly
            // modifies a place provided by the caller.
            //
            // TODO: type parameters: for generic methods we will want to pass
            //   values of type `Type` as well`
            let arg_count = arg_defs.arg_count + 1;

            // Create the identifier and use it as an output ref. This is what
            // is used when other methods call this one.
            let method_name =
                vir::vir_format_identifier!(vcx, "m_{}", vir::ViperIdent::from_def_id(vcx, def_id));
            let ref_args = vcx.alloc_slice(&vec![vir::TYPE_REF; arg_count]);
            let params = GParams::from(def_id);
            let generics = deps.require_dep_spanned::<GenericParamsEnc>(params, span)?;
            let method_ref = MethodIdn::new(
                method_name,
                (ref_args, generics.ty_args(), generics.const_args()),
            );
            deps.emit_output_ref(def_id, MethodEncOutputRef { method_ref })?;

            let arg_defs = deps.require_dep_spanned::<MirLocalDefEnc>(
                MirLocalDefEncTask::Local {
                    def_id,
                    all_locals: false,
                },
                span,
            )?;

            // Method contract. We will need to emit pre- and postconditions for
            // the permissions, the functional spec, and (in the postcondition)
            // wands in case of a reborrowing function.
            let mut pres = Vec::new();
            let mut posts = Vec::new();
            let spec = deps.require_dep_spanned::<MirSpecEnc>(
                (def_id, def_id, MirSpecEncMode::Impure),
                span,
            )?;
            let function_data = FunctionData::new(def_id);
            let wands = deps
                .require_dep_spanned::<WandEnc>(
                    WandEncTask {
                        data: function_data,
                    },
                    span,
                )
                .map_err(|err| {
                    // Without its wands, the method has no contract.
                    let (message, _) = super::dep_error(&err);
                    vcx.emit_early_error(PrustiError::unsupported(
                        format!(
                            "cannot encode method `{}`: {message}",
                            vcx.tcx().def_path_str(def_id),
                        ),
                        vcx.tcx().def_span(def_id).into(),
                    ));
                    EncodeFullError::EncodingError(MethodEncError::Reported, None)
                })?;

            // Add direct resources for inputs and outputs to the pre- and
            // postconditions, respectively. "Direct" here refers to owned
            // Viper resources that must be passed in/out given the signature,
            // without going through any dereferences.
            let mut args = Vec::with_capacity(arg_count + params.count());
            for arg_idx in (0..arg_count).map(mir::Local::from) {
                let name_p = arg_defs[arg_idx].local.name;
                args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                if arg_idx != mir::RETURN_PLACE {
                    pres.push(arg_defs[arg_idx].impure_pred);
                }
            }
            posts.push(arg_defs[mir::RETURN_PLACE].impure_pred);

            // ..
            pres.extend(wands.indirect_pres(vcx, &arg_defs, deps));
            posts.extend(wands.indirect_posts(vcx, &arg_defs, deps));
            posts.extend(wands.wand_posts(vcx, &arg_defs, deps));

            // The method of a pure function ties its result to the
            // definitional function `f_` (see `FunctionEnc`), so a caller in
            // impure code learns the result's value from the method call. The
            // callee proves nothing for it: the function's body is this
            // method's body by construction. Closures have no `f_`.
            let is_pure =
                crate::encoders::is_function_pure(def_id, GArgs::new(params, params.rust_params()));
            if is_pure && !vcx.tcx().is_closure_like(def_id) {
                let pure_func = deps.require_dep_spanned::<FunctionCallEnc>(
                    CallTaskDescription::new(def_id, params.rust_params(), def_id)
                        .resolve_trait_calls(false),
                    span,
                )?;
                let arg_snaps = (1..arg_count)
                    .map(mir::Local::from)
                    .map(|arg_idx| vcx.mk_old_expr(arg_defs[arg_idx].impure_snap))
                    .collect::<Vec<_>>();
                let app = if pure_func.is_pure_unstable() {
                    // The callee reads the interior-mutability value `Map`:
                    // materialize it from the arguments in the pre-state.
                    let arg_data = (1..arg_count)
                        .map(mir::Local::from)
                        .map(|arg_idx| {
                            let arg_def = &arg_defs[arg_idx];
                            (arg_def.ty, vcx.mk_null(), arg_def.impure_snap)
                        })
                        .collect::<Vec<_>>();
                    let map = crate::encoders::ty::interior_mut::pure_unstable_call_map(
                        deps,
                        &arg_data,
                        pure_func.pure_unstable_inner_only(),
                    )?;
                    pure_func.call_pure_unstable(arg_snaps, vcx.mk_old_expr(map))
                } else {
                    pure_func.call_pure(arg_snaps)
                };
                posts.push(vcx.mk_inhale_exhale_expr(
                    vcx.mk_eq_expr(arg_defs[mir::RETURN_PLACE].impure_snap, app),
                    vcx.mk_bool::<true>(),
                ));
            }

            // Write permission to all interior-mutable objects reachable from
            // the arguments (collected by the `_IM` functions of their types).
            // We emit a single quantified permission over the union of all
            // these sets, since arguments may alias (e.g. two shared
            // references to the same `Cell`), in which case the shared
            // interior-mutable objects must be counted only once.
            //
            // The precondition requires the full set of each argument (owned
            // interior-mutable objects as well as those behind references).
            // The postcondition returns only the objects reachable through
            // references in the arguments (in the `old` state; the owned ones
            // are consumed by the function) plus the full set of the result.
            // The union again ensures that objects returned to the caller
            // through both a reference argument and the result (e.g. when a
            // function returns one of its arguments) are not counted twice.
            //
            // Arguments that provably reach no interior-mutable objects are
            // skipped entirely: their maps are empty, and leaving them out
            // keeps the pre- and postcondition map terms of the remaining
            // sources aligned (an extra empty union changes the term, and
            // opaque map consumers such as `s_Param_IM_1` need term-equal
            // arguments to compare equal).
            let fn_sig = vcx
                .tcx()
                .fn_sig(def_id)
                .instantiate_identity()
                .skip_binder();
            let mut arg_ims = Vec::with_capacity(arg_count - 1);
            for arg_idx in (1..arg_count).map(mir::Local::from) {
                let arg = &arg_defs[arg_idx];
                if crate::encoders::ty::interior_mut::provably_no_interior_mut(
                    vcx.tcx(),
                    fn_sig.inputs()[arg_idx.index() - 1],
                    &mut Default::default(),
                ) {
                    continue;
                }
                // Encode the argument type's IM functions (dispatch axioms).
                deps.require_dep::<TyInteriorMutUseEnc>(arg.ty)?;
                arg_ims.push((
                    arg_idx,
                    fn_sig.inputs()[arg_idx.index() - 1],
                    arg.ty,
                    arg.local_ex,
                    arg.impure_snap,
                ));
            }

            let tys = ImTys::new(deps);
            let unions = deps.require_dep::<MapUnionEnc>(())?;

            // Emits the level-0 and level-1 QPs over the arguments, evaluating
            // each argument's snapshot via `snap_of`. The maps of all
            // arguments are merged into one per level (arguments may alias, in
            // which case the shared maps' overlaps are assumed to agree), and
            // the level-1 functions take the level-0 IM-QP `Map` snapshot,
            // materialized once from the merged level-0 map (this matches the
            // level-0 QP exactly, so `qp_to_map`'s precondition is
            // discharged).
            let mk_qps =
                |deps: &mut TaskEncoderDependencies<'vir, _>,
                 snap_of: &dyn Fn(vir::ExprSnap<'vir>) -> vir::ExprSnap<'vir>,
                 prefix: &str|
                 -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, MethodEnc>> {
                    // Bind each argument's snapshot once with a `let` and use the
                    // bound variable in every map expression. The snapshot
                    // functions are heap-dependent (framed by a `wildcard`
                    // permission), and Silicon fails to match `qp_to_map`'s
                    // precondition against the just-inhaled level-0 QP when the
                    // two map expressions evaluate the snapshots separately.
                    let mut lets = Vec::with_capacity(arg_ims.len());
                    let mut im0_sources = Vec::with_capacity(arg_ims.len());
                    for (idx, (_, _, ty, addr, snap)) in arg_ims.iter().enumerate() {
                        let val = snap_of(*snap);
                        let decl = vcx.mk_local_decl(
                            vir::vir_format!(vcx, "{prefix}_im_snap_{idx}"),
                            val.ty(),
                        );
                        lets.push((decl, val));
                        im0_sources.push((*ty, *addr, vcx.mk_local_ex(decl)));
                    }
                    // Each level-1 source reads through its own canonical
                    // `im0_snap` map (see `im_boundary_maps`).
                    let maps = im_boundary_maps(deps, &im0_sources, &[], false)?;
                    let mut qps = vec![maps.qp0(vcx, deps, None)?];
                    if let Some(qp1) = maps.qp1(vcx, deps, None)? {
                        qps.push(qp1);
                    }
                    // Self-framing order: the level-0 QP grants what the level-1
                    // map reads need (on exhale those reads are evaluated in the
                    // pre-exhale heap, so the same order works in both
                    // directions).
                    let mut expr = vcx.mk_conj(&qps);
                    for (decl, val) in lets.into_iter().rev() {
                        expr = vcx.mk_let_expr(decl, val, expr);
                    }
                    Ok(expr)
                };

            // The boundary QPs are created under the function's span (they
            // have no user-written source), with handlers for the permission
            // failures that can arise from them, so that such failures are
            // reported at the function instead of being position-less. A
            // permission failure on safe code is always a Prusti encoding
            // bug, never an error in the user's program (the amounts flow
            // deterministically; every user-provable state is guarded by the
            // value-level preconditions, which fail first) — so these are
            // INTERNAL errors, kept only to carry a usable position. The one
            // user-facing case is a negative amount: `#[interior_mut(EXPR)]`
            // permission expressions are user-written.
            let mut im_qp_pre: Option<vir::ExprBool<'vir>> = None;
            let mut im_qp_post: Option<vir::ExprBool<'vir>> = None;
            let mut im_frame_post: Option<vir::ExprBool<'vir>> = None;
            vcx.with_span(
                span,
                |vcx| -> Result<(), EncodeFullError<'vir, MethodEnc>> {
                    vcx.handle_error("call.precondition:insufficient.permission", move |_| {
                        Some(vec![PrustiError::internal(
                            "a call to this function failed to provide the interior-mutability \
                            permissions its precondition requires; this indicates a bug in \
                            Prusti's interior-mutability encoding",
                            span.into(),
                        )])
                    });
                    vcx.handle_error(
                    "postcondition.violated:insufficient.permission",
                    move |_| {
                        Some(vec![PrustiError::internal(
                            "this function failed to return the interior-mutability permissions \
                            its postcondition promises; this indicates a bug in Prusti's \
                            interior-mutability encoding",
                            span.into(),
                        )])
                    },
                );
                    vcx.handle_error(
                    "application.precondition:insufficient.permission",
                    move |_| {
                        Some(vec![PrustiError::internal(
                            "the interior-mutability contract of this function reads state whose \
                            permission is not available; this indicates a bug in Prusti's \
                            interior-mutability encoding",
                            span.into(),
                        )])
                    },
                );
                    vcx.handle_error("not.wellformed:negative.permission", move |_| {
                        Some(vec![PrustiError::verification(
                            "a permission amount in this function's interior-mutability contract \
                        might be negative",
                            span.into(),
                        )])
                    });
                    if !arg_ims.is_empty() {
                        im_qp_pre = Some(mk_qps(deps, &|s| s, "pre")?);
                    }

                    // In the postcondition we return only the interior-mutable objects
                    // reachable *behind a reference* (computed by the indirect encoder,
                    // i.e. the data behind the `&` as a `Param`), in the `old` state —
                    // NOT the arguments' own `s_Ref_immutable_IM_N` maps. The owned IM
                    // objects of the arguments are consumed by the function. The
                    // result's own IM objects are created by the function and returned
                    // to the caller: its pairs (in the post state) are added, with the
                    // result's snapshot bound once with a `let` shared by all its map
                    // expressions.
                    let (post_pairs, mut post_im0_sources) =
                        wands.interior_mut_post_pairs(vcx, &arg_defs, deps);
                    // By-value arguments without function-shape nodes contribute
                    // their SHARED component in the `old` state: their owned
                    // interior-mutable objects are consumed by the function, but the
                    // objects behind references inside them (e.g. a guard's borrow
                    // flag) belong to others and must return to the caller — else a
                    // call like `drop(guard)` takes them to the grave and the expiry
                    // wand has nothing to apply against. Arguments WITH shape nodes
                    // are covered by `interior_mut_post_pairs` (type-level sources,
                    // expanded pairs, or the wand for blocked projections).
                    let shape_locals: Vec<mir::Local> =
                        wands.inputs().map(|g| g.mir_local()).collect();
                    let mut post_shared_sources = Vec::new();
                    for (local, rust_ty, ty, local_ex, impure_snap) in &arg_ims {
                        // A type parameter's shape nodes cannot be expanded into
                        // pairs, so `mem::drop`'s argument is a shared source like
                        // shape-less arguments.
                        // TODO: this holds for every by-value type parameter, but
                        // the extra postcondition map read makes the contracts of
                        // e.g. `Cell::set` fail to check reliably.
                        if matches!(rust_ty.kind(), ty::TyKind::Ref(..))
                            || (shape_locals.contains(local)
                                && !vcx.tcx().is_diagnostic_item(symbol::sym::mem_drop, def_id))
                        {
                            continue;
                        }
                        post_shared_sources.push((*ty, *local_ex, vcx.mk_old_expr(*impure_snap)));
                    }
                    // `mem::drop` is modeled as a pure discard: its argument's guard
                    // effects (a `RefCell` count decrement) are attributed to the
                    // expiry pledges, which fire at the borrow's expiry right after
                    // the call. The shared interior-mutable state it returns is
                    // therefore framed; without this, the fresh chunks from its
                    // postcondition leave e.g. the borrow count unconstrained, and
                    // the expiry's level-1 amounts become underivable.
                    if vcx.tcx().is_diagnostic_item(symbol::sym::mem_drop, def_id)
                        && !post_shared_sources.is_empty()
                    {
                        im_frame_post = Some(im_frame(deps, &post_shared_sources, false)?);
                    }
                    // A pure function leaves every interior-mutable object as it
                    // found it: the objects reachable from all its arguments (both
                    // components) are framed, so a call in impure code (a method
                    // call, see above) does not lose their values.
                    if is_pure && !arg_ims.is_empty() {
                        let all_sources = arg_ims
                            .iter()
                            .map(|(_, _, ty, local_ex, impure_snap)| {
                                (*ty, *local_ex, vcx.mk_old_expr(*impure_snap))
                            })
                            .collect::<Vec<_>>();
                        im_frame_post = Some(im_frame(deps, &all_sources, true)?);
                    }
                    let result = &arg_defs[mir::RETURN_PLACE];
                    let result_snap_decl =
                        vcx.mk_local_decl("post_im_snap_result", result.impure_snap.ty());
                    let result_snap_var = vcx.mk_local_ex(result_snap_decl);
                    // The expanded function-shape pair expressions reference the
                    // fixed `BOUNDARY_IM0_MAP` name; the canonical sources read
                    // through their own `im0_snap` maps instead.
                    let l0_map_post_decl = vcx.mk_local_decl(BOUNDARY_IM0_MAP, tys.snap_map);
                    // A provably interior-mut-free result is skipped like the
                    // arguments above, keeping the post map terms aligned with the
                    // precondition's.
                    if !crate::encoders::ty::interior_mut::provably_no_interior_mut(
                        vcx.tcx(),
                        fn_sig.output(),
                        &mut Default::default(),
                    ) {
                        post_im0_sources.push((result.ty, result.local_ex, result_snap_var));
                    }
                    if !post_im0_sources.is_empty()
                        || !post_shared_sources.is_empty()
                        || post_pairs.iter().any(|ps| !ps.is_empty())
                    {
                        // The sources' maps in the canonical triple form (see
                        // `im_boundary_maps`); the expanded function-shape pairs of
                        // partially-blocked arguments keep their own shape and are
                        // merged on top.
                        let post_maps =
                            im_boundary_maps(deps, &post_im0_sources, &post_shared_sources, false)?;
                        let [post_pairs_0, post_pairs_1] = post_pairs;
                        let extra_0 = (!post_pairs_0.is_empty())
                            .then(|| merge_pairs(&tys, &unions, post_pairs_0));
                        let has_pairs_1 = !post_pairs_1.is_empty();
                        let extra_1 = has_pairs_1.then(|| merge_pairs(&tys, &unions, post_pairs_1));
                        let mut post_qps = vec![post_maps.qp0(vcx, deps, extra_0)?];
                        if let Some(mut post_qp1) = post_maps.qp1(vcx, deps, extra_1)? {
                            // The joined map for the expanded pair expressions, which
                            // reference the fixed `BOUNDARY_IM0_MAP` name.
                            if has_pairs_1 {
                                let l0_map_post = im0_snap_sources(
                                    deps,
                                    &post_im0_sources,
                                    &post_shared_sources,
                                )?;
                                post_qp1 = vcx.mk_let_expr(l0_map_post_decl, l0_map_post, post_qp1);
                            }
                            post_qps.push(post_qp1);
                        }
                        // Self-framing order (see `mk_qps`).
                        im_qp_post = Some(vcx.mk_let_expr(
                            result_snap_decl,
                            result.impure_snap,
                            vcx.mk_conj(&post_qps),
                        ));
                    }
                    Ok(())
                },
            )?;

            // Trusted functions, call stubs, external functions and trait
            // functions without a default implementation have no body to
            // encode; only their contract is emitted.
            let blocks = if let Some(body_with_facts) =
                crate::encoders::impure_body_with_facts(def_id)
            {
                let body = &body_with_facts.body;
                let local_defs = deps.require_dep_spanned::<MirLocalDefEnc>(
                    MirLocalDefEncTask::Local {
                        def_id,
                        all_locals: true,
                    },
                    span,
                )?;

                let pcg_creator = pcg::PcgCtxtCreator::new(vcx.tcx());
                let pcg_ctxt = pcg_creator.new_nll_ctxt(&body_with_facts);
                let fpcs_analysis = pcg::run_pcg(pcg_ctxt);
                pcg_ctxt.update_debug_visualization_metadata();

                let block_count = body.basic_blocks.len();

                let mut encoded_blocks = Vec::with_capacity(
                    // extra blocks: Start, End
                    2 + block_count,
                );
                let mut start_stmts = Vec::new();
                for local in (arg_count..body.local_decls.len()).map(mir::Local::from) {
                    // Spec-only locals have no definition.
                    let Some(local_def) = local_defs.get(local) else {
                        continue;
                    };
                    let name_p = local_def.local.name;
                    start_stmts.push(
                        vcx.mk_local_decl_stmt(vir::vir_local_decl! { vcx; [name_p] : Ref }, None),
                    )
                }
                // This will be overwritten later.
                encoded_blocks.push(vcx.mk_cfg_block(
                    &vir::CfgBlockLabelData::Start,
                    &[],
                    &[],
                    vcx.mk_goto_stmt(&vir::CfgBlockLabelData::BasicBlock(0)),
                ));

                let spec_blocks = SpecBlocks::new(
                    deps.require_dep::<SpecBlocksEnc>(def_id)?,
                    body,
                    fpcs_analysis.analysis().loop_analysis(),
                );

                deps.check_cycle()?;
                let mut visitor = ImpureEncVisitor {
                    vcx,
                    deps,
                    def_id,
                    local_decls: &body.local_decls,
                    fpcs_analysis,
                    local_defs,
                    spec_blocks,
                    body,

                    wands,

                    tmp_ctr: 0,
                    label_ctr: 0,
                    call_labels: Default::default(),
                    wandless_calls: Default::default(),
                    from_to_vars: Default::default(),

                    current_block: None,
                    current_block_pres: None,
                    current_block_succs: None,
                    current_block_label: None,
                    current_fpcs: None,

                    current_stmts: None,
                    current_terminator: None,
                    encoded_blocks,
                };
                // if we encountered an error/cycle during encoding, we don't
                // emit a method body; encoding errors additionally surface as
                // early errors rather than silently degrading to a stub
                match visitor.visit_body(body) {
                    Ok(()) => {
                        start_stmts.extend(
                            visitor
                                .from_to_vars
                                .decls()
                                .map(|v| vcx.mk_local_decl_stmt(v, Some(vcx.mk_bool::<false>()))),
                        );
                        visitor.encoded_blocks[0] = vcx.mk_cfg_block(
                            &vir::CfgBlockLabelData::Start,
                            &[],
                            vcx.alloc_slice(&start_stmts),
                            vcx.mk_goto_stmt(&vir::CfgBlockLabelData::BasicBlock(0)),
                        );

                        visitor.encoded_blocks.push(vcx.mk_cfg_block(
                            vcx.alloc(vir::CfgBlockLabelData::End),
                            &[],
                            &[],
                            vcx.alloc(vir::TerminatorStmtData::Exit),
                        ));

                        visitor.deps.check_cycle()?;

                        Some(visitor.encoded_blocks)
                    }
                    Err(EncodeFullError::AlreadyEncoded) => None,
                    Err(err) => {
                        let (message, span) = super::dep_error(&err);
                        vcx.emit_early_error(PrustiError::unsupported(
                            format!(
                                "cannot encode method body `{}`: {message}",
                                vcx.tcx().def_path_str(def_id),
                            ),
                            span.unwrap_or_else(|| vcx.tcx().def_span(def_id)).into(),
                        ));
                        None
                    }
                }
            } else {
                None
            };

            // Add the functional specification as the last pre- and
            // postconditions, after the IM QPs that grant the permissions
            // its interior-mutable reads need.
            pres.extend(im_qp_pre);
            pres.extend(spec.pre_exprs());
            posts.extend(im_qp_post);
            posts.extend(spec.post_exprs());
            posts.extend(im_frame_post);

            Ok((
                MethodEncOutput {
                    method: vcx.mk_method(
                        method_ref,
                        (&args, generics.ty_decls(), generics.const_decls()),
                        &[],
                        vcx.alloc_slice(&pres),
                        vcx.alloc_slice(&posts),
                        blocks.map(|blocks| vcx.alloc_slice(&blocks)),
                    ),
                },
                (),
            ))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            program.add_method(output.method);
        }
    }
}
