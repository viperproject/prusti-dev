use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::FunctionIdn;

/// Encodes `s_Param_typ`, the function mapping a generic snapshot to the type
/// of the value it holds. Stating a param's type is what lets the variant
/// bridge emitted by the pure casters fire, and with it the reconstruction of
/// the param from its concrete value.
pub(crate) struct ParamTypEnc;

#[derive(Debug, Clone, Copy)]
pub(crate) struct ParamTyp<'vir> {
    pub(crate) typ: FunctionIdn<'vir, vir::PSnap, vir::TyVal>,
}

impl TaskEncoder for ParamTypEnc {
    task_encoder::encoder_cache!(ParamTypEnc);
    const ENCODER_NAME: &'static str = "param typ encoder";

    type TaskDescription<'vir> = ();
    type OutputFullLocal<'vir> = vir::Domain<'vir>;
    type OutputFullDependency<'vir> = ParamTyp<'vir>;

    fn task_to_key<'vir>(_task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {}

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let typ = FunctionIdn::new(
            vir::ViperIdent::new("s_Param_typ"),
            vir::TYPE_PSNAP,
            vir::TYPE_TYVAL,
        );
        deps.emit_output_ref(*task_key, ())?;
        let domain = vir::with_vcx(|vcx| {
            vcx.mk_domain(
                vir::ViperIdent::new("ParamTyp"),
                &[],
                &[],
                vcx.alloc_slice(&[vcx.mk_domain_function(typ, false, None)]),
                None,
            )
        });
        Ok((domain, ParamTyp { typ }))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for domain in Self::all_outputs_local_no_errors(program) {
            program.add_domain(domain);
        }
    }
}
