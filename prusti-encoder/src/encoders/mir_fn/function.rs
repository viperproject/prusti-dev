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
    /// `true` if the callee is `#[pure_unstable]` and therefore expects the
    /// inner-IM-QP `Map` argument (callers must use [`Self::call_pure_unstable`]).
    pub fn is_pure_unstable(&self) -> bool {
        self.function.pure_unstable.is_some()
    }

    /// Calls the definitional function `f_`, used in pure/spec contexts.
    pub fn call_pure<Curr, Next>(
        &self,
        args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.call_casted(self.function.function_ref, args, &[])
    }

    /// Call a `#[pure_unstable]` callee, passing the inner-IM-QP `Map` snapshot
    /// as the extra Viper argument.
    pub fn call_pure_unstable<Curr, Next>(
        &self,
        args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
        inner_map: vir::ExprGenMap<'vir, Curr, Next>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.call_casted(self.function.function_ref, args, &[inner_map])
    }

    /// Calls the caller wrapper `cf_`, used when encoding impure assignments.
    pub fn call_impure<Curr, Next>(
        &self,
        args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        self.call_casted(self.function.caller_ref, args, &[])
    }

    fn call_casted<Curr, Next>(
        &self,
        function: FnSig<'vir>,
        mut args: Vec<vir::ExprGenSnap<'vir, Curr, Next>>,
        maps: &[vir::ExprGenMap<'vir, Curr, Next>],
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        assert_eq!(self.inputs.len(), args.len());
        for (arg, caster) in args.iter_mut().zip(self.inputs.iter()) {
            *arg = caster.cast_to_callee_ctx(*arg);
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
                caller_ref: assoc_enc.call_stub_pure_caller.unwrap(),
                function_ref: assoc_enc.call_stub_pure_function.unwrap(),
                // Trait-call stubs do not (yet) carry the inner-IM `Map`.
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

/// The function signature carries a `ManyMap` slot (between the snapshot args
/// and the type/const generics) for the inner-IM-QP `Map` of `#[pure_unstable]`
/// functions. It is empty (length 0) for all other functions, so their emitted
/// Viper signature is unchanged.
type FnSig<'vir> =
    FunctionIdn<'vir, (vir::ManySnap, vir::ManyMap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>;

#[derive(Debug, Clone)]
struct FunctionEncOutputRef<'vir> {
    caller_ref: FnSig<'vir>,
    function_ref: FnSig<'vir>,
    /// `Some` if this is a `#[pure_unstable]` function (so its signature has a
    /// non-empty `ManyMap` slot that callers must fill); the `bool` is the
    /// `inner_only` flag.
    pure_unstable: Option<bool>,
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
            // `#[pure_unstable]` functions take the inner-IM-QP `Map` snapshot as
            // an extra argument (so e.g. a borrow-count function can read the
            // current interior-mutable state). Non-pure-unstable functions have
            // an empty `ManyMap` slot, leaving their Viper signature unchanged.
            let pure_unstable = crate::encoders::get_pure_unstable(def_id);
            let map_decls: &[vir::LocalDeclMap<'vir>] = if pure_unstable.is_some() {
                vcx.alloc_slice(&[crate::encoders::ty::interior_mut::pure_unstable_inner_map_decl(
                    deps,
                )?])
            } else {
                &[]
            };
            let map_types =
                vcx.alloc_slice(&map_decls.iter().map(|d| d.ty).collect::<Vec<_>>());
            let caller_ref = FunctionIdn::new(
                caller_ident,
                (arg_types, map_types, generics.ty_args(), generics.const_args()),
                return_type,
            );
            let function_ref = FunctionIdn::new(
                function_ident,
                (arg_types, map_types, generics.ty_args(), generics.const_args()),
                return_type,
            );
            deps.emit_output_ref(
                def_id,
                FunctionEncOutputRef {
                    caller_ref,
                    function_ref,
                    pure_unstable,
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
            let map_exprs = map_decls
                .iter()
                .map(|arg| vcx.mk_local_ex(arg))
                .collect::<Vec<_>>();
            let wrapped_call = function_ref.call()(
                &wrapped_call_args,
                &map_exprs,
                generics.ty_exprs(),
                generics.const_exprs(),
            );
            let caller = vcx.mk_function(
                caller_ref,
                (&func_args, map_decls, generics.ty_decls(), generics.const_decls()),
                vcx.alloc_slice(&spec.pre_exprs().collect::<Vec<_>>()),
                posts,
                None,
                Some(wrapped_call),
            );
            let function = vcx.mk_function(
                function_ref,
                (&func_args, map_decls, generics.ty_decls(), generics.const_decls()),
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
