use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, CastType, FunctionIdn};

/// Encodes `read()`, an unspecified permission amount strictly between `none`
/// and `write`, for predicates that hold part of a permission and leave the
/// splitting of it to the verifier.
///
/// It is a domain function rather than a regular one: a function whose body
/// unfolds a predicate using `read()` only sees the limited version of a
/// regular function, which carries no postcondition, so the fraction could
/// not be shown to be non-negative there.
pub struct ReadPermEnc;

#[derive(Debug, Clone, Copy)]
pub struct ReadPerm<'vir> {
    pub read: FunctionIdn<'vir, (), vir::Perm>,
}

impl TaskEncoder for ReadPermEnc {
    task_encoder::encoder_cache!(ReadPermEnc);
    const ENCODER_NAME: &'static str = "read permission encoder";

    type TaskDescription<'vir> = ();
    type OutputFullLocal<'vir> = vir::Domain<'vir>;
    type OutputFullDependency<'vir> = ReadPerm<'vir>;

    fn task_to_key<'vir>(_task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {}

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let read = FunctionIdn::new(vir::ViperIdent::new("read"), (), vir::TYPE_PERM);
        let domain = vir::with_vcx(|vcx| {
            let bounds = vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "{}_bounds", read.name()),
                vcx.mk_conj(&[
                    vcx.mk_bin_op_expr(vir::BinOpKind::CmpLt, vcx.mk_no_perm(), read())
                        .downcast_ty(),
                    vcx.mk_bin_op_expr(vir::BinOpKind::CmpLt, read(), vcx.mk_full_perm())
                        .downcast_ty(),
                ]),
            );
            vcx.mk_domain(
                vir::ViperIdent::new("ReadPerm"),
                &[],
                vcx.alloc_slice(&[bounds]),
                vcx.alloc_slice(&[vcx.mk_domain_function(read, false, None)]),
                None,
            )
        });
        Ok((domain, ReadPerm { read }))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for domain in Self::all_outputs_local_no_errors(program) {
            program.add_domain(domain);
        }
    }
}
