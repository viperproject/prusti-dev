use task_encoder::TaskEncoder;
use vir::{DomainGenData, FunctionIdn, ViperIdent};

#[derive(Debug, Clone, Copy)]
pub struct IntRealCastDomain<'vir> {
    pub from_int: FunctionIdn<'vir, vir::Int, vir::Perm>,
}

pub struct IntRealCastEnc;

impl TaskEncoder for IntRealCastEnc {
    task_encoder::encoder_cache!(IntRealCastEnc);
    const ENCODER_NAME: &'static str = "int_real_cast encoder";

    type TaskDescription<'vir> = ();

    type OutputFullLocal<'vir> = &'vir DomainGenData<'vir, (), !>;

    type OutputFullDependency<'vir> = IntRealCastDomain<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            deps.emit_output_ref(*task_key, ())?;

            let domain_name = "s_IntRealCast";

            let domain_ident = vir::ViperIdent::new(domain_name);
            let from_int_name = vir::vir_format!(vcx, "{domain_name}_from_int");

            let from_int = FunctionIdn::new(
                ViperIdent::new(from_int_name),
                vir::TYPE_INT,
                vir::TYPE_PERM,
            );

            let from_int_data = vcx.mk_domain_function(from_int, false, Some("to_real"));

            let domain_data = vcx.mk_domain::<(), !>(
                domain_ident,
                &[],
                &[],
                vcx.alloc_slice(&[from_int_data]),
                None,
            );

            Ok((domain_data, IntRealCastDomain { from_int }))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            program.add_domain(output);
        }
    }
}
