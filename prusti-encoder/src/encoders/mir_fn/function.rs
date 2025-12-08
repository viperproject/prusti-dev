use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, Reify};

use crate::encoders::{
    MirLocalDefEnc, MirLocalDefEncTask, MirPureEnc, MirPureEncTask, MirSpecEnc, Pure, PureKind,
    mir_fn::{CallTaskDescription, RustSignature},
    ty::generics::{GArgCaster, GArgsCastEnc, GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc},
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
    pub fn call<Curr, Next>(
        &self,
        mut args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        assert_eq!(self.inputs.len(), args.len());
        let a = args.iter_mut().zip(self.inputs.iter());
        for (arg, caster) in a {
            *arg = caster.cast_to_callee_ctx(*arg);
        }
        let call = self.function.function_ref.call()(
            &args,
            self.ty_args.get_ty(),
            self.ty_args.get_const(),
        );
        self.output.cast_to_caller_ctx(call)
    }
}

impl TaskEncoder for FunctionCallEnc {
    task_encoder::encoder_cache!(FunctionCallEnc);
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
        let function_ref = deps.require_ref::<FunctionEnc>(task_key.callee)?;
        let signature = RustSignature::new(task_key.callee);
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
    function_ref: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>,
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

            let function_ident =
                vir::vir_format_identifier!(vcx, "f_{}", vcx.tcx().def_path_str(def_id));
            let arg_types = vcx.alloc_slice(&local_defs.snap_ty_args().collect::<Vec<_>>());
            let return_type = local_defs.snap_ty_return();
            let params = GParams::from(def_id);
            let generics = deps.require_dep::<GenericParamsEnc>(params)?;
            let function_ref = FunctionIdn::new(
                function_ident,
                (arg_types, generics.ty_args(), generics.const_args()),
                return_type,
            );
            deps.emit_output_ref(def_id, FunctionEncOutputRef { function_ref })?;

            let substs = ty::GenericArgs::identity_for_item(vcx.tcx(), def_id);
            let spec = deps.require_dep::<MirSpecEnc>((def_id, true))?;

            let expr = if trusted {
                None
            } else {
                // Encode the body of the function
                let expr = deps
                    .require_dep::<MirPureEnc>(MirPureEncTask {
                        encoding_depth: 0,
                        kind: PureKind::Pure,
                        parent_def_id: def_id,
                        param_env: vcx.tcx().param_env(def_id),
                        substs,
                        caller_def_id: None,
                    })?
                    .expr;
                let expr = expr.reify(vcx, (def_id, spec.pre_args));
                assert!(
                    expr.ty() == return_type,
                    "expected {:?}, got {:?}",
                    return_type,
                    expr.ty()
                );
                Some(expr)
            };

            // TODO: type preconditions do not currently work
            /*
            let arg_type_assertions = local_defs.args().map(|arg| {
                let snap = vcx.mk_local_ex(arg.local_snap);
                generics.ty_assertion(deps, snap, arg.rust_ty)
            }).collect::<Vec<_>>();
            */

            tracing::debug!("finished {def_id:?}");

            let mut pres = Vec::new(); // arg_type_assertions;
            pres.extend(spec.pres);

            // TODO: type preconditions do not currently work
            /*
            let ret = local_defs.ret();
            let snap = vcx.mk_result(ret.local_snap.ty());
            let ret_type_assertions = generics.ty_assertion(deps, snap, ret.rust_ty);
            */
            let mut posts = Vec::new(); // vec![ret_type_assertions];
            posts.extend(spec.posts);

            let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
            let function = vcx.mk_function(
                function_ref,
                (&func_args, generics.ty_decls(), generics.const_decls()),
                vcx.alloc_slice(&pres),
                vcx.alloc_slice(&posts),
                expr.is_none().then_some(&vir::DecreasesGenData::Star),
                expr,
            );
            Ok((FunctionEncOutput { function }, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors() {
            program.add_function(output.function);
        }
    }
}
