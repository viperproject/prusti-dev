use pcg::borrow_pcg::FunctionData;
use prusti_interface::PrustiError;
use prusti_rustc_interface::{middle::mir, span::def_id::DefId};
use task_encoder::{
    EncodeFullError, EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies,
};
use vir::{CastType, MethodIdn};

use crate::{
    encoders::{
        Impure, ImpureEncVisitor, MirLocalDefEnc, MirLocalDefEncTask, MirSpecEnc, WandEnc,
        WandEncTask,
        interior_mut::{TyInteriorMutUseEnc, interior_mut_inner_map},
        mir_fn::{CallTaskDescription, RustSignature, SpecBlocks},
        pure::spec::MirSpecEncMode,
        ty::{
            generics::{GArgCaster, GArgsCastEnc, GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc},
            indirect::{full_perm, interior_mut_quant_perm, object_perm},
        },
    },
    trait_support::is_function_with_body,
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
                method_ref: assoc_enc.call_stub_impure.unwrap(),
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
pub enum MethodEncError {}

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

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let def_id = *task_key;
        vir::with_vcx(|vcx| {
            let span = vcx.tcx().def_span(def_id);
            let trusted = crate::encoders::is_function_trusted(def_id);

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
                vir::vir_format_identifier!(vcx, "m_{}", vcx.tcx().def_path_str(def_id));
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
            let wands = deps.require_dep_spanned::<WandEnc>(
                WandEncTask {
                    data: function_data,
                },
                span,
            )?;

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
            // TODO(interior-mut, STEP B): currently only the inner-IM (full
            // permission) objects are granted, via a single QP in the pre- and
            // postcondition. The object-IM (permission-expression) objects need
            // a separate treatment that does NOT emit a second QP over the same
            // `p_Param` predicate (Silicon's QP framing cannot disentangle two
            // QPs over one predicate); the planned approach materializes the
            // inner-IM QP into a Viper `Map` (`qp_to_map`) and expresses the
            // object-IM permission against that Map.
            // Collect each argument's IM encoding + address/snapshot.
            let mut arg_ims = Vec::with_capacity(arg_count - 1);
            for arg_idx in (1..arg_count).map(mir::Local::from) {
                let arg = &arg_defs[arg_idx];
                let im = deps.require_dep::<TyInteriorMutUseEnc>(arg.ty)?;
                arg_ims.push((im, arg.local_ex, arg.impure_snap));
            }

            // Emits an inner-IM QP and an object-IM QP over the arguments,
            // evaluating each argument's snapshot via `snap_of`. The object-IM
            // set function takes the inner-IM QP `Map` snapshot, materialized
            // once from the union of the arguments' inner-IM sets (this matches
            // the single inner-IM QP exactly, so `qp_to_map`'s precondition is
            // discharged). The two QPs are returned as `(inner, object)` so the
            // caller can order them appropriately (the object-IM QP must be
            // processed while the inner-IM permission is held).
            //
            // TODO(interior-mut): the object-IM QP still grants full permission
            // (placeholder); and the result's own IM objects are not yet
            // returned in the postcondition.
            let mut mk_qps = |deps: &mut TaskEncoderDependencies<'vir, _>,
                              snap_of: &dyn Fn(vir::ExprSnap<'vir>) -> vir::ExprSnap<'vir>,
                              prefix: &str|
             -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, MethodEnc>> {
                // Bind each argument's snapshot once with a `let` and use the
                // bound variable in every set expression. The snapshot
                // functions are heap-dependent (framed by a `wildcard`
                // permission), and Silicon fails to match `qp_to_map`'s
                // precondition against the just-inhaled inner QP when the two
                // set expressions evaluate the snapshots separately.
                let mut lets = Vec::with_capacity(arg_ims.len());
                let mut snap_vars = Vec::with_capacity(arg_ims.len());
                let mut inner = Vec::with_capacity(arg_ims.len());
                for (idx, (im, addr, snap)) in arg_ims.iter().enumerate() {
                    let val = snap_of(*snap);
                    let decl = vcx.mk_local_decl(
                        vir::vir_format!(vcx, "{prefix}_im_snap_{idx}"),
                        val.ty(),
                    );
                    lets.push((decl, val));
                    let var = vcx.mk_local_ex(decl);
                    snap_vars.push(var);
                    inner.push(im.get_all_inner(*addr, var));
                }
                let union_inner = inner.iter().copied().reduce(|a, b| {
                    vcx.mk_anyset_op_expr(vir::CollectionBinOpKind::Union, a, b)
                        .downcast_ty()
                });
                let mut object = Vec::with_capacity(arg_ims.len());
                if let Some(union_inner) = union_inner {
                    let map = interior_mut_inner_map(deps, union_inner)?;
                    for ((im, addr, _), var) in arg_ims.iter().zip(&snap_vars) {
                        object.push(im.get_all_object(*addr, *var, map));
                    }
                }
                let inner_qp = interior_mut_quant_perm(
                    vcx,
                    deps,
                    vec![vir::TYPE_REF.as_dyn(), vir::TYPE_TYVAL.as_dyn()],
                    inner,
                    full_perm,
                )?;
                let object_qp = interior_mut_quant_perm(
                    vcx,
                    deps,
                    vec![
                        vir::TYPE_REF.as_dyn(),
                        vir::TYPE_TYVAL.as_dyn(),
                        vir::TYPE_PERM.as_dyn(),
                    ],
                    object,
                    object_perm,
                )?;
                // The inner QP comes first: the object QP's `qp_to_map` needs
                // the inner permission to be inhaled already.
                let mut expr = vcx.mk_conj(&[inner_qp, object_qp]);
                for (decl, val) in lets.into_iter().rev() {
                    expr = vcx.mk_let_expr(decl, val, expr);
                }
                Ok(expr)
            };

            pres.push(mk_qps(deps, &|s| s, "pre")?);

            // In the postcondition we return only the interior-mutable objects
            // reachable *behind a reference* (computed by the indirect encoder,
            // i.e. the data behind the `&` as a `Param`), in the `old` state —
            // NOT the arguments' own `s_Ref_immutable_IM_*` sets. The owned IM
            // objects of the arguments are consumed by the function.
            //
            // The inner-IM QP is pushed BEFORE the object-IM QP (this ordering
            // is what makes the `Cell`/multi-arg cases verify). NOTE: once the
            // object-IM perm genuinely depends on `qp_to_map(inner_set)` (i.e.
            // a `RefCell` whose `#[pure_unstable]` perm closure reads the map),
            // the object QP's `qp_to_map` precondition / permission amounts can
            // no longer be matched at exhale here — that is the open QP-matching
            // problem (the perm verified before only because the map was dead).
            let (mut post_inner, mut post_object) =
                wands.interior_mut_post_sets(vcx, &arg_defs, deps);
            // The result's own IM objects are created by the function and
            // returned to the caller: add its full sets (in the post state).
            // As in `mk_qps`, the result's snapshot is bound once with a `let`
            // shared by the inner set, the map and the object set.
            let result = &arg_defs[mir::RETURN_PLACE];
            let result_im = deps.require_dep::<TyInteriorMutUseEnc>(result.ty)?;
            let result_snap_decl =
                vcx.mk_local_decl("post_im_snap_result", result.impure_snap.ty());
            let result_snap_var = vcx.mk_local_ex(result_snap_decl);
            post_inner.push(result_im.get_all_inner(result.local_ex, result_snap_var));
            let post_map = interior_mut_inner_map(
                deps,
                post_inner
                    .iter()
                    .copied()
                    .reduce(|a, b| {
                        vcx.mk_anyset_op_expr(vir::CollectionBinOpKind::Union, a, b)
                            .downcast_ty()
                    })
                    .unwrap(),
            )?;
            post_object.push(result_im.get_all_object(
                result.local_ex,
                result_snap_var,
                post_map,
            ));
            let post_inner_qp = interior_mut_quant_perm(
                vcx,
                deps,
                vec![vir::TYPE_REF.as_dyn(), vir::TYPE_TYVAL.as_dyn()],
                post_inner,
                full_perm,
            )?;
            let post_object_qp = interior_mut_quant_perm(
                vcx,
                deps,
                vec![
                    vir::TYPE_REF.as_dyn(),
                    vir::TYPE_TYVAL.as_dyn(),
                    vir::TYPE_PERM.as_dyn(),
                ],
                post_object,
                object_perm,
            )?;
            posts.push(vcx.mk_let_expr(
                result_snap_decl,
                result.impure_snap,
                vcx.mk_conj(&[post_inner_qp, post_object_qp]),
            ));

            // Do not encode the method body if it is external, trusted, just
            // a call stub, or a trait function without a default implementation
            let local_def_id = def_id
                .as_local()
                .filter(|_| !trusted && is_function_with_body(vcx.tcx(), def_id));
            let blocks = if let Some(local_def_id) = local_def_id {
                let body_with_facts = vcx.body_mut().get_impure_fn_body_with_facts(local_def_id);
                let body = &body_with_facts.body;
                let local_defs = deps.require_dep_spanned::<MirLocalDefEnc>(
                    MirLocalDefEncTask::Local {
                        def_id: local_def_id.to_def_id(),
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
                    let name_p = local_defs[local].local.name;
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

                let spec_blocks =
                    SpecBlocks::new(def_id, body, fpcs_analysis.analysis().loop_analysis());

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
                        vcx.emit_early_error(PrustiError::unsupported(
                            format!(
                                "cannot encode method body `{}`: {}",
                                vcx.tcx().def_path_str(def_id),
                                super::dep_error_message(&err),
                            ),
                            vcx.tcx().def_span(def_id).into(),
                        ));
                        None
                    }
                }
            } else {
                None
            };

            // Add functional specification as the last pre- and postconditions.
            pres.extend(spec.pre_exprs());
            posts.extend(spec.post_exprs());

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
