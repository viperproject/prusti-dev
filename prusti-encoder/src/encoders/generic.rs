use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{
    BinaryArity, CallableIdent, DomainIdent, DomainParamData, FunctionIdent,
    KnownArityAny, NullaryArity, PredicateIdent, TypeData, UnaryArity, ViperIdent,
};

pub struct GenericEnc;

#[derive(Clone, Debug)]
pub enum GenericEncError {
    UnsupportedType,
}

#[derive(Clone, Debug)]
pub struct GenericEncOutputRef<'vir> {
    pub type_snapshot: vir::Type<'vir>,
    pub param_snapshot: vir::Type<'vir>,
    pub param_type_function: vir::FunctionIdent<'vir, UnaryArity<'vir>>,
    pub ref_to_pred: PredicateIdent<'vir, BinaryArity<'vir>>,
    pub ref_to_snap: FunctionIdent<'vir, BinaryArity<'vir>>,
    pub unreachable_to_snap: FunctionIdent<'vir, NullaryArity<'vir>>,
    pub domain_type_name: DomainIdent<'vir, KnownArityAny<'vir, DomainParamData<'vir>, 0>>,
    pub domain_param_name: DomainIdent<'vir, KnownArityAny<'vir, DomainParamData<'vir>, 0>>,
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

const TYP_DOMAIN: TypeData<'static> = TypeData::Domain("Type", &[]);
const SNAPSHOT_PARAM_DOMAIN: TypeData<'static> = TypeData::Domain("s_Param", &[]);

impl TaskEncoder for GenericEnc {
    task_encoder::encoder_cache!(GenericEnc);

    type TaskDescription<'tcx> = (); // ?

    type OutputRef<'vir> = GenericEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = GenericEncOutput<'vir>;

    type EncodingError = GenericEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    #[allow(non_snake_case)]
    fn do_encode_full<'tcx: 'vir, 'vir>(
        task_key: &Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> Result<
        (
            Self::OutputFullLocal<'vir>,
            Self::OutputFullDependency<'vir>,
        ),
        (
            Self::EncodingError,
            Option<Self::OutputFullDependency<'vir>>,
        ),
    > {
        let ref_to_pred =
            PredicateIdent::new(ViperIdent::new("p_Param"), BinaryArity::new(&[&TypeData::Ref, &TYP_DOMAIN]));
        let type_domain_ident = DomainIdent::nullary(ViperIdent::new("Type"));
        let param_domain_ident = DomainIdent::nullary(ViperIdent::new("s_Param"));
        let ref_to_snap = FunctionIdent::new(
            ViperIdent::new("p_Param_snap"),
            BinaryArity::new(&[&TypeData::Ref, &TYP_DOMAIN]),
            &SNAPSHOT_PARAM_DOMAIN,
        );
        let unreachable_to_snap = FunctionIdent::new(
            ViperIdent::new("p_Param_unreachable"),
            NullaryArity::new(&[]),
            &SNAPSHOT_PARAM_DOMAIN,
        );

        let param_type_function = FunctionIdent::new(
            ViperIdent::new("typ"),
            UnaryArity::new(&[&SNAPSHOT_PARAM_DOMAIN]),
            &TYP_DOMAIN,
        );


        let output_ref = GenericEncOutputRef {
            type_snapshot: &TYP_DOMAIN,
            param_snapshot: &SNAPSHOT_PARAM_DOMAIN,
            ref_to_pred,
            domain_type_name: type_domain_ident,
            domain_param_name: param_domain_ident,
            ref_to_snap,
            unreachable_to_snap,
            param_type_function,
        };

        #[allow(clippy::unit_arg)]
        deps.emit_output_ref::<Self>(
            *task_key,
            output_ref
        );

        let typ = FunctionIdent::new(
            ViperIdent::new("typ"),
            UnaryArity::new(&[&SNAPSHOT_PARAM_DOMAIN]),
            &TYP_DOMAIN,
        );


        vir::with_vcx(|vcx| {
            let t = vcx.mk_local_ex("t", &TYP_DOMAIN);
            let ref_to_snap = vcx.mk_function(
                "p_Param_snap",
                vir::vir_arg_list! { vcx; self: Ref, t: Type },
                vir::vir_type! { vcx; s_Param },
                vcx.alloc_slice(&[vcx.mk_predicate_app_expr(ref_to_pred.apply(
                    vcx,
                    [vcx.mk_local_ex("self", &TypeData::Ref), t],
                    Some(vcx.mk_wildcard()),
                ))]),
                vcx.alloc_slice(&[vcx.mk_bin_op_expr(
                    vir::BinOpKind::CmpEq,
                    typ.apply(vcx, [vcx.mk_result(&SNAPSHOT_PARAM_DOMAIN)]),
                    t,
                )]),
                None,
            );

            // unreachable_to_snap
            let name = unreachable_to_snap.name_str();
            let false_ = vcx.alloc_slice(&[vcx.mk_bool::<false>()]);
            let unreachable_to_snap =
                vcx
                    .mk_function(name, &[], &SNAPSHOT_PARAM_DOMAIN, false_, false_, None);
            Ok((
                GenericEncOutput {
                    param_snapshot: vir::vir_domain! { vcx; domain s_Param {
                            function typ(s_Param): Type;
                        }
                    },
                    ref_to_pred: vir::vir_predicate! { vcx; predicate p_Param(self_p: Ref, t: Type) },
                    type_snapshot: vir::vir_domain! { vcx; domain Type { } },
                    ref_to_snap,
                    unreachable_to_snap
                },
                (),
            ))
        })
    }
}
