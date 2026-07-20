use task_encoder::TaskEncoder;
use vir::{CastType, DomainGenData, DomainIdnCSnap, FunctionIdn, ViperIdent};

#[derive(Debug, Clone, Copy)]
pub struct RealDomain<'vir> {
    pub from_int: FunctionIdn<'vir, vir::Prim, vir::Prim>,
    pub to_int: FunctionIdn<'vir, vir::Prim, vir::Prim>,
}

pub struct RealEnc;

impl TaskEncoder for RealEnc {
    task_encoder::encoder_cache!(RealEnc);
    const ENCODER_NAME: &'static str = "real encoder";

    type TaskDescription<'vir> = ();

    type OutputFullLocal<'vir> = &'vir DomainGenData<'vir, (), !>;

    type OutputFullDependency<'vir> = RealDomain<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            program.add_domain(output);
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let domain_name = "s_Real";

            let domain_ident = DomainIdnCSnap::new(vir::ViperIdent::new(domain_name), 0);
            let from_int_name = vir::vir_format!(vcx, "{domain_name}_from_int");

            let from_int = FunctionIdn::new(
                ViperIdent::new(from_int_name),
                vir::TYPE_INT.upcast_ty(),
                vir::TYPE_PERM.upcast_ty(),
            );

            let from_int_data = vcx.mk_domain_function(from_int, false, Some("to_real"));

            let to_int_name = vir::vir_format!(vcx, "{domain_name}_to_int");

            let to_int = FunctionIdn::new(
                ViperIdent::new(to_int_name),
                vir::TYPE_PERM.upcast_ty(),
                vir::TYPE_INT.upcast_ty(),
            );

            let to_int_data = vcx.mk_domain_function(to_int, false, Some("to_int"));

            let domain_data = vcx.mk_domain::<(), !>(
                domain_ident.name(),
                &[],
                &[],
                vcx.alloc_slice(&[from_int_data, to_int_data]),
                None,
            );

            deps.emit_output_ref(*task_key, ())?;
            Ok((domain_data, RealDomain { from_int, to_int }))
        })
    }
}
