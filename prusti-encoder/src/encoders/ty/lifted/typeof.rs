use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder};
use vir::FunctionIdn;

use crate::encoders::ty::{RustTy, pure::TyPureEnc};

#[derive(Debug, Clone)]
pub struct TypeOfEncOutputRef<'vir> {
    /// Returns the Viper representation of the type of a snapshot-encoded value
    pub typeof_function: vir::FunctionIdn<'vir, vir::Snap, vir::TyVal>,
}

impl<'vir> OutputRefAny for TypeOfEncOutputRef<'vir> {}

type TypeOfEncOutput<'vir> = vir::DomainFunction<'vir>;

pub struct TypeOfEnc;

impl TaskEncoder for TypeOfEnc {
    task_encoder::encoder_cache!(TypeOfEnc);
    const ENCODER_NAME: &'static str = "typeof encoder";
    type TaskDescription<'tcx> = RustTy<'tcx>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

    type OutputRef<'vir> = TypeOfEncOutputRef<'vir>;

    type OutputFullLocal<'vir> = TypeOfEncOutput<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let base_name = task_key.name();
            let domain = deps.require_ref::<TyPureEnc>(*task_key)?;
            let snap = (domain.domain)();
            let typeof_function = FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "s_{base_name}_typeof"),
                snap,
                vir::TYPE_TYVAL,
            );
            deps.emit_output_ref(*task_key, TypeOfEncOutputRef { typeof_function })?;

            let typeof_function = vcx.mk_domain_function(typeof_function, false, None);
            Ok((typeof_function, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let typeof_fns = Self::all_outputs_local_no_errors();
        vir::with_vcx(|vcx| {
            let domain = vcx.mk_domain(
                vir::ViperIdent::new("TypeOf"),
                &[],
                &[],
                vcx.alloc_slice(&typeof_fns),
                None,
            );
            program.add_domain(domain);
        })
    }
}
