use prusti_interface::PrustiError;
use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, Reify};

use crate::{
    encoders::{
        MirLocalDefEnc, MirLocalDefEncTask, MirPureEnc, MirPureEncTask, MirSpecEnc, Pure, PureKind,
        mir_fn::{CallTaskDescription, RustSignature},
        pure::spec::MirSpecEncMode,
        ty::generics::{GArgCaster, GArgsCastEnc, GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc},
    },
    trait_support::is_function_with_body,
};

// Function wrapper

pub struct FunctionCallEnc;

#[derive(Debug, Clone)]
pub struct FunctionCallEncOutput<'vir> {
    function: FunctionEncOutputRef<'vir>,
    ty_args: GArgsTy<'vir>,
    inputs: Vec<GArgCaster<'vir, Pure>>,
    output: GArgCaster<'vir, Pure>,
}

impl<'vir> FunctionCallEncOutput<'vir> {
    /// Calls the definitional function `f_`, used in pure/spec contexts.
    pub fn call_pure<Curr, Next>(
        &self,
        args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.call_casted(self.function.function_ref, args)
    }

    /// Calls the caller wrapper `cf_`, used when encoding impure assignments.
    pub fn call_impure<Curr, Next>(
        &self,
        args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.call_casted(self.function.caller_ref, args)
    }

    fn call_casted<Curr, Next>(
        &self,
        function: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
        mut args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        assert_eq!(self.inputs.len(), args.len());
        for (arg, caster) in args.iter_mut().zip(self.inputs.iter()) {
            *arg = caster.cast_to_callee_ctx(*arg);
        }
        let call = function.call()(&args, self.ty_args.get_ty(), self.ty_args.get_const());
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
                caller_ref: assoc_enc.call_stub_pure_caller.unwrap(),
                function_ref: assoc_enc.call_stub_pure_function.unwrap(),
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
        Ok((
            (),
            FunctionCallEncOutput {
                function: function_ref,
                ty_args,
                inputs,
                output,
            },
        ))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        FunctionEnc::emit_outputs(program);
    }
}

// Function encoder

struct FunctionEnc;

#[derive(Debug, Clone)]
struct FunctionEncOutputRef<'vir> {
    caller_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
    function_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
}

impl<'vir> OutputRefAny for FunctionEncOutputRef<'vir> {}

#[derive(Debug, Clone, Copy)]
struct FunctionEncOutput<'vir> {
    caller: vir::Function<'vir>,
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
            let trusted = crate::encoders::is_function_trusted(def_id);
            let local_defs = deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                def_id,
                all_locals: true,
            })?;

            tracing::debug!("encoding {def_id:?}");

            let caller_ident =
                vir::vir_format_identifier!(vcx, "cf_{}", vcx.tcx().def_path_str(def_id));
            let function_ident =
                vir::vir_format_identifier!(vcx, "f_{}", vcx.tcx().def_path_str(def_id));
            let arg_types = vcx.alloc_slice(&local_defs.snap_ty_args().collect::<Vec<_>>());
            let return_type = local_defs.snap_ty_return();
            let params = GParams::from(def_id);
            let generics = deps.require_dep::<GenericParamsEnc>(params)?;
            let caller_ref = FunctionIdn::new(
                caller_ident,
                (arg_types, generics.ty_args(), generics.const_args()),
                return_type,
            );
            let function_ref = FunctionIdn::new(
                function_ident,
                (arg_types, generics.ty_args(), generics.const_args()),
                return_type,
            );
            deps.emit_output_ref(
                def_id,
                FunctionEncOutputRef {
                    caller_ref,
                    function_ref,
                },
            )?;

            let substs = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
            let spec =
                deps.require_dep::<MirSpecEnc>((def_id, def_id, MirSpecEncMode::PureWithResult))?;

            let expr = if trusted || !is_function_with_body(vcx.tcx(), def_id) {
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
                    param_env: vcx.tcx().param_env(def_id),
                    substs,
                    caller_def_id: None,
                }) {
                    Ok(out) => {
                        let expr = out.expr.reify(vcx, (def_id, spec.pre_args));
                        assert!(
                            expr.ty() == return_type,
                            "expected {:?}, got {:?}",
                            return_type,
                            expr.ty()
                        );
                        Some(expr)
                    }
                    Err(err) => {
                        vcx.emit_early_error(PrustiError::unsupported(
                            format!(
                                "cannot encode function body `{}`: {}",
                                vcx.tcx().def_path_str(def_id),
                                super::dep_error_message(&err),
                            ),
                            vcx.tcx().def_span(def_id).into(),
                        ));
                        None
                    }
                }
            };

            tracing::debug!("finished {def_id:?}");

            let posts = spec
                .posts
                .iter()
                .map(|(post, _)| {
                    // use inhale-exhale expression to prevent viper checking that
                    // the function body expression satisfies the postcondition:
                    // that's checked in the method encoding of this function.
                    vcx.mk_inhale_exhale_expr(*post, vcx.mk_bool::<true>())
                })
                .collect::<Vec<_>>();
            let posts = vcx.alloc_slice(&posts);

            let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
            let wrapped_call_args = func_args
                .iter()
                .map(|arg| vcx.mk_local_ex(arg))
                .collect::<Vec<_>>();
            let wrapped_call = function_ref.call()(
                &wrapped_call_args,
                generics.ty_exprs(),
                generics.const_exprs(),
            );
            let caller = vcx.mk_function(
                caller_ref,
                (&func_args, generics.ty_decls(), generics.const_decls()),
                vcx.alloc_slice(&spec.pre_exprs().collect::<Vec<_>>()),
                posts,
                None,
                Some(wrapped_call),
            );
            let function = vcx.mk_function(
                function_ref,
                (&func_args, generics.ty_decls(), generics.const_decls()),
                &[],
                posts,
                expr.is_none().then_some(&vir::DecreasesGenData::Star),
                expr,
            );
            Ok((FunctionEncOutput { caller, function }, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            program.add_function(output.caller);
            program.add_function(output.function);
        }
    }
}
