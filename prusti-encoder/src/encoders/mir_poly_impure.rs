use prusti_interface::PrustiError;
use prusti_rustc_interface::span::def_id::DefId;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies, TaskEncoderError};

/// Encodes a Rust function as a Viper method using the polymorphic encoding of generics.
pub struct MirPolyImpureEnc;

use crate::encoder_traits::impure_function_enc::{
    ImpureFunctionEnc, ImpureFunctionEncError, ImpureFunctionEncOutput, ImpureFunctionEncOutputRef,
};

impl ImpureFunctionEnc for MirPolyImpureEnc {
    fn mk_method_ident<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        def_id: &Self::TaskKey<'tcx>,
    ) -> vir::ViperIdent<'vir> {
        vir::vir_format_identifier!(vcx, "m_{}", vcx.tcx().def_path_str(*def_id))
    }
}

impl TaskEncoder for MirPolyImpureEnc {
    task_encoder::encoder_cache!(MirPolyImpureEnc);

    type TaskDescription<'tcx> = DefId;

    type TaskKey<'tcx> = DefId;

    type OutputRef<'vir> = ImpureFunctionEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = ImpureFunctionEncOutput<'vir>;

    type EncodingError = ImpureFunctionEncError;

    const ENCODER_NAME: &'static str = "impure method encoder";

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        def_id: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        <Self as ImpureFunctionEnc>::encode(*def_id, deps).map(|r| (r, ()))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let (outputs, errored) = Self::all_outputs_local();
        for output in outputs {
            program.add_method(output.method);
        }
        for (error_key, output_ref, error) in errored {
            vir::with_vcx(|vcx| {
                use vir::CallableIdn;
                let span = vcx.tcx().def_span(error_key);
                let method_stub = vcx.mk_method(
                    output_ref.method_ref,
                    (
                        vcx.alloc_slice(&output_ref.method_ref.arity().0.iter()
                            .enumerate()
                            .map(|(idx, ty)| vcx.mk_local_decl(vir::vir_format!(vcx, "_0_{idx}"), ty))
                            .collect::<Vec<_>>()),
                        vcx.alloc_slice(&output_ref.method_ref.arity().1.iter()
                            .enumerate()
                            .map(|(idx, ty)| vcx.mk_local_decl(vir::vir_format!(vcx, "_1_{idx}"), ty))
                            .collect::<Vec<_>>()),
                    ),
                    &[],
                    vcx.alloc_slice(&[
                        // TODO: the strange false == true expression is constructed
                        //   here because a const bool false doesn't get a span attached
                        //   to it. (Maybe we don't need the const bool optimisation.)
                        // TODO: this should instead be a span + error handler at the
                        //   call site. We should change this once there is an encoder
                        //   for method calls, which will encode a call to a stub method
                        //   differently (if it can know that it failed?).
                        vcx.with_span(span, |vcx| vcx.mk_eq_expr(vcx.mk_bool::<false>(), vcx.mk_bool::<true>())),
                    ]),
                    &[],
                    None,
                );
                if output_ref.should_be_verified {
                    let mut prusti_error = PrustiError::verification("method was not verified", span.into());
                    explain(error, &mut prusti_error);
                    vcx.emit_early_error(prusti_error);
                }
                program.add_method(method_stub);
            });
        }
    }
}

/// Format the error nicely to be displayed to the user.
/// TODO: should be elsewhere
pub fn explain<E: TaskEncoder + ?Sized>(error: TaskEncoderError<E>, prusti_error: &mut PrustiError) {
    // TODO: the other cases will not happen in this encoder (it does not
    //   directly return `Err`) but should probably be handled for other encoders
    match error {
        TaskEncoderError::EnqueueingError(..) => (),
        TaskEncoderError::EncodingError(..) => (),
        TaskEncoderError::DependencyError(stack) => {
            // skip the first one since that is already the main error and span
            for (encoder, desc, spans) in &stack[1..] {
                prusti_error.add_note_mut(format!("{desc} ({encoder})"), spans.first().cloned().map(|s| s.into()));
            }
        }
        TaskEncoderError::CyclicError => (),
    }
}
