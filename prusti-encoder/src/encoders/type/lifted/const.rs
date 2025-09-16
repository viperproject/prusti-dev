use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, FunctionIdn, ViperIdent};

use crate::encoders::{most_generic_ty::get_vir_base_name_kind, TyPureEnc};

/// Creates domain functions which embed values of the given type into instances
/// of `Type`, suitable for passing as the representation of a type parameter,
/// e.g., when calling a method.
pub struct LiftedConstEnc;

#[derive(Clone, Debug)]
pub struct LiftedConstEncOutputRef<'vir> {
    pub const_type_function: vir::FunctionIdn<'vir, vir::Dyn, vir::TyVal>,
    pub const_value_function: vir::FunctionIdn<'vir, vir::TyVal, vir::Dyn>,
}

impl<'vir> task_encoder::OutputRefAny for LiftedConstEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct LiftedConstEncOutput<'vir> {
    pub domain: vir::Domain<'vir>,
}

impl TaskEncoder for LiftedConstEnc {
    task_encoder::encoder_cache!(LiftedConstEnc);

    type TaskDescription<'vir> = ty::Ty<'vir>;

    type OutputRef<'vir> = LiftedConstEncOutputRef<'vir>;

    type OutputFullLocal<'vir> = LiftedConstEncOutput<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    #[allow(non_snake_case)]
    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let base_name = get_vir_base_name_kind(task_key.kind(), vcx);
            let ty_enc = deps.require_ref::<TyPureEnc>(*task_key)?;
            let const_type_function = FunctionIdn::new(
                ViperIdent::new(vir::vir_format!(vcx, "const_typ_{base_name}")),
                ty_enc.snapshot.upcast_ty(),
                vir::TYPE_TYVAL,
            );
            let const_value_function = FunctionIdn::new(
                ViperIdent::new(vir::vir_format!(vcx, "const_val_{base_name}")),
                vir::TYPE_TYVAL,
                ty_enc.snapshot.upcast_ty(),
            );

            let output_ref = LiftedConstEncOutputRef {
                const_type_function,
                const_value_function,
            };

            #[allow(clippy::unit_arg)]
            deps.emit_output_ref(*task_key, output_ref)?;

            let domain = vcx.mk_domain(
                ViperIdent::new(vir::vir_format!(vcx, "LiftedConst_{base_name}")),
                &[],
                vcx.alloc_slice(&[
                    vcx.mk_domain_axiom_inverse(const_value_function, const_type_function),
                ]),
                vcx.alloc_slice(&[
                    vcx.mk_domain_function(const_type_function, false),
                    vcx.mk_domain_function(const_value_function, false),
                ]),
            );

            Ok((LiftedConstEncOutput { domain }, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors() {
            program.add_domain(output.domain);
        }
    }
}
