use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::FunctionIdn;

/// The (uninterpreted) function transferring the *referent value* of a `&mut`
/// across an unsize coercion: `value_cast(old_referent_snap, from_ty, to_ty)` is
/// the new referent snapshot. Like `metadata_cast`, it is only defined by
/// axioms; the array->slice axioms are added (for the concrete element types) in
/// `MirBuiltinUseCastEnc`. The identity axiom handles degenerate `T -> T`
/// reborrows; every other (e.g. `Struct -> dyn`) coercion is left unconstrained.
pub struct ValueCastEnc;

impl TaskEncoder for ValueCastEnc {
    task_encoder::encoder_cache!(ValueCastEnc);
    const ENCODER_NAME: &'static str = "unsize value cast encoder";
    type TaskDescription<'vir> = ();
    type OutputFullDependency<'vir> =
        FunctionIdn<'vir, (vir::PSnap, vir::TyVal, vir::TyVal), vir::PSnap>;
    type OutputFullLocal<'vir> = vir::Domain<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let idn = vir::ViperIdent::new("unsize_value_cast");
        let fn_idn = vir::FunctionIdn::new(
            idn,
            (vir::TYPE_PSNAP, vir::TYPE_TYVAL, vir::TYPE_TYVAL),
            vir::TYPE_PSNAP,
        );
        vir::with_vcx(|vcx| {
            let domain_fn = vcx.mk_domain_function(fn_idn, false, None);
            // See comment in `MetadataCastEnc` about the corresponding axiom there.
            // forall input: s_Param, same: Type :: { value_cast(input, same, same) }
            //     value_cast(input, same, same) == input
            let expr = vir::expr! {
                forall input: PSnap, same: Type :: { [fn_idn](input, same, same) }
                    ([fn_idn](input, same, same)) == (input)
            };
            let axiom = vcx.mk_domain_axiom(vir::ViperIdent::new("unsize_value_cast_eq"), expr);
            let domain = vcx.mk_domain(
                vir::ViperIdent::new("UnsizeValueCast"),
                &[],
                vcx.alloc_slice(&[axiom]),
                vcx.alloc_slice(&[domain_fn]),
                None,
            );
            Ok((domain, fn_idn))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        match Self::all_outputs_local_no_errors(program).as_slice() {
            [] => (),
            [domain] => program.add_domain(domain),
            _ => unreachable!(),
        }
    }
}

/// The (uninterpreted) function transferring the *referent metadata* across an
/// unsize coercion: `metadata_cast(old_referent_metadata, from_ty, to_ty)` is
/// the new referent metadata. It is only defined by axioms.
pub struct MetadataCastEnc;

impl TaskEncoder for MetadataCastEnc {
    task_encoder::encoder_cache!(MetadataCastEnc);
    const ENCODER_NAME: &'static str = "metadata cast encoder";
    type TaskDescription<'vir> = ();
    type OutputFullDependency<'vir> =
        FunctionIdn<'vir, (vir::PSnap, vir::TyVal, vir::TyVal), vir::PSnap>;
    type OutputFullLocal<'vir> = vir::Domain<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let idn = vir::ViperIdent::new("metadata_cast");
        let fn_idn = vir::FunctionIdn::new(
            idn,
            (vir::TYPE_PSNAP, vir::TYPE_TYVAL, vir::TYPE_TYVAL),
            vir::TYPE_PSNAP,
        );
        vir::with_vcx(|vcx| {
            let domain_fn = vcx.mk_domain_function(fn_idn, false, None);

            // The only universally-valid axiom: a degenerate cast (same source and
            // target type) leaves the metadata unchanged. Concrete coercions that
            // *do* rewrite the metadata (e.g. array -> slice, where the metadata
            // becomes the slice length) are attached per-coercion in
            // `MetadataCastAxiomEnc`, so this encoder does not assume any particular
            // pointee shape exists.
            // forall input: s_Param, same: Type :: { metadata_cast(input, same, same) } metadata_cast(input, same, same) == input
            let expr = vir::expr! {
                forall input: PSnap, same: Type :: { [fn_idn](input, same, same) }
                    ([fn_idn](input, same, same)) == (input)
            };
            let axiom_eq = vcx.mk_domain_axiom(vir::ViperIdent::new("metadata_cast_eq"), expr);

            let domain = vcx.mk_domain(
                vir::ViperIdent::new("MetadataCast"),
                &[],
                vcx.alloc_slice(&[axiom_eq]),
                vcx.alloc_slice(&[domain_fn]),
                None,
            );
            Ok((domain, fn_idn))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        match Self::all_outputs_local_no_errors(program).as_slice() {
            [] => (),
            [domain] => program.add_domain(domain),
            _ => unreachable!(),
        }
    }
}
