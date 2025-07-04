use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdn, DomainIdnPSnap, FunctionIdn, PredicateIdn, ViperIdent};

pub struct GenericEnc;

#[derive(Clone, Debug)]
pub enum GenericEncError {
    // UnsupportedType,
}

#[derive(Clone, Debug)]
pub struct GenericEncOutputRef<'vir> {
    pub type_snapshot: vir::TypeTyVal<'vir>,
    pub param_snapshot: vir::TypePSnap<'vir>,
    pub param_type_function: vir::FunctionIdn<'vir, vir::PSnap, vir::TyVal>,
    pub ref_to_pred: PredicateIdn<'vir, (vir::Ref, vir::TyVal)>,
    pub ref_to_snap: FunctionIdn<'vir, (vir::Ref, vir::TyVal), vir::PSnap>,
    pub unreachable_to_snap: FunctionIdn<'vir, (), vir::PSnap>,
    // pub domain_type_name: DomainIdent<'vir, KnownArityAny<'vir, DomainParamData<'vir>, 0>>,
    pub domain_param_name: DomainIdnPSnap<'vir>,
}
impl<'vir> task_encoder::OutputRefAny for GenericEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct GenericEncOutput<'vir> {
    pub type_snapshot: vir::Domain<'vir>,
    pub ref_to_pred: vir::Predicate<'vir>,
    pub param_snapshot: vir::Domain<'vir>,
    pub ref_to_snap: vir::Function<'vir>,
    pub unreachable_to_snap: vir::Function<'vir>,
}

impl TaskEncoder for GenericEnc {
    task_encoder::encoder_cache!(GenericEnc);

    type TaskDescription<'vir> = (); // ?

    type OutputRef<'vir> = GenericEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = GenericEncOutput<'vir>;

    type EncodingError = GenericEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    #[allow(non_snake_case)]
    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        let ref_to_pred =
            PredicateIdn::new(ViperIdent::new("p_Param"), (vir::TYPE_REF, vir::TYPE_TYVAL));
        // let type_domain_ident = DomainIdent::nullary(ViperIdent::new("Type"));
        let param_domain_ident = DomainIdnPSnap::new(ViperIdent::new("s_Param"));
        let ref_to_snap = FunctionIdn::new(
            ViperIdent::new("p_Param_snap"),
            (vir::TYPE_REF, vir::TYPE_TYVAL),
            vir::TYPE_PSNAP,
        );
        let unreachable_to_snap =
            FunctionIdn::new(ViperIdent::new("p_Param_unreachable"), (), vir::TYPE_PSNAP);

        let param_type_function =
            FunctionIdn::new(ViperIdent::new("typ"), vir::TYPE_PSNAP, vir::TYPE_TYVAL);

        let output_ref = GenericEncOutputRef {
            type_snapshot: vir::TYPE_TYVAL,
            param_snapshot: vir::TYPE_PSNAP,
            ref_to_pred,
            // domain_type_name: type_domain_ident,
            domain_param_name: param_domain_ident,
            ref_to_snap,
            unreachable_to_snap,
            param_type_function,
        };

        #[allow(clippy::unit_arg)]
        deps.emit_output_ref(*task_key, output_ref)?;

        let typ = param_type_function;

        vir::with_vcx(|vcx| {
            let t = vcx.mk_local_ex("t", vir::TYPE_TYVAL);
            let ref_to_snap = vcx.mk_function(
                ref_to_snap,
                vir::vir_arg_tuple! { vcx; self: Ref, t: Type },
                vcx.alloc_slice(&[vcx.mk_predicate_app_expr(ref_to_pred(
                    vcx.mk_local_ex("self", vir::TYPE_REF),
                    t,
                )(Some(
                    vcx.mk_wildcard(),
                )))]),
                vcx.alloc_slice(&[vcx.mk_eq_expr(typ(vcx.mk_result(vir::TYPE_PSNAP)), t)]),
                None,
            );

            // unreachable_to_snap
            let false_ = vcx.alloc_slice(&[vcx.mk_bool::<false>()]);
            let unreachable_to_snap =
                vcx.mk_function(unreachable_to_snap, (), false_, false_, None);
            Ok((
                GenericEncOutput {
                    param_snapshot: vir::vir_domain! { vcx; domain s_Param {
                            function typ(s_Param): Type;
                        }
                    },
                    ref_to_pred: vir::vir_predicate! { vcx; predicate p_Param(self_p: Ref, t: Type) },
                    type_snapshot: vir::vir_domain! { vcx; domain Type { } },
                    ref_to_snap,
                    unreachable_to_snap,
                },
                (),
            ))
        })
    }
}
