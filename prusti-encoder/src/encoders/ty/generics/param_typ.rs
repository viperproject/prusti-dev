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
    /// Holds for every param and its type, so that an axiom can be
    /// triggered on a param of one particular type, named by its type
    /// constructor in the second argument.
    pub(crate) has_typ: FunctionIdn<'vir, (vir::PSnap, vir::TyVal), vir::Bool>,
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
        let has_typ = FunctionIdn::new(
            vir::ViperIdent::new("s_Param_has_typ"),
            (vir::TYPE_PSNAP, vir::TYPE_TYVAL),
            vir::TYPE_BOOL,
        );
        deps.emit_output_ref(*task_key, ())?;
        let domain = vir::with_vcx(|vcx| {
            let p_decl = vcx.mk_local_decl("p", vir::TYPE_PSNAP);
            let typ_p = typ(vcx.mk_local_ex(p_decl));
            let has_own_typ = vcx.mk_forall_expr(
                vcx.alloc_slice(&[p_decl]),
                vcx.alloc_slice(&[vcx.mk_trigger(&[typ_p])]),
                has_typ(vcx.mk_local_ex(p_decl), typ_p),
            );
            vcx.mk_domain(
                vir::ViperIdent::new("ParamTyp"),
                &[],
                vcx.alloc_slice(&[
                    vcx.mk_domain_axiom(vir::ViperIdent::new("s_Param_has_typ_own"), has_own_typ)
                ]),
                vcx.alloc_slice(&[
                    vcx.mk_domain_function(typ, false, None),
                    vcx.mk_domain_function(has_typ, false, None),
                ]),
                None,
            )
        });
        Ok((domain, ParamTyp { typ, has_typ }))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for domain in Self::all_outputs_local_no_errors(program) {
            program.add_domain(domain);
        }
    }
}
