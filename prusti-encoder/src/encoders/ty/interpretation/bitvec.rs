use task_encoder::TaskEncoder;
use vir::{
    BackendInterpretationPair, CastType, DomainGenData, DomainIdnCSnap, FunctionIdn, ViperIdent,
};

#[derive(Eq, PartialEq, Hash, Debug, Clone, Copy)]
pub enum BitVecSize {
    BitVec8,
    BitVec16,
    BitVec32,
    BitVec64,
    BitVec128,
}

#[derive(Debug, Clone, Copy)]
pub struct BitVecDomain<'vir> {
    pub domain: vir::DomainIdn<'vir, vir::CSnap>,
    pub from_int: FunctionIdn<'vir, vir::Prim, vir::CSnap>,
    pub ubv_to_int: FunctionIdn<'vir, vir::CSnap, vir::Prim>,
    pub sbv_to_int: FunctionIdn<'vir, vir::CSnap, vir::Prim>,
    pub bv_xor: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub bv_and: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub bv_or: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub bv_shl: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub bv_shr: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
}

pub struct BitVecEnc;

impl TaskEncoder for BitVecEnc {
    task_encoder::encoder_cache!(BitVecEnc);
    const ENCODER_NAME: &'static str = "bitvec encoder";

    type TaskDescription<'vir> = BitVecSize;

    type OutputFullLocal<'vir> = &'vir DomainGenData<'vir, (), !>;

    type OutputFullDependency<'vir> = BitVecDomain<'vir>;

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
            let domain_name = match *task_key {
                BitVecSize::BitVec8 => "s_BitVec_8",
                BitVecSize::BitVec16 => "s_BitVec_16",
                BitVecSize::BitVec32 => "s_BitVec_32",
                BitVecSize::BitVec64 => "s_BitVec_64",
                BitVecSize::BitVec128 => "s_BitVec_128",
            };

            let domain_ident = DomainIdnCSnap::new(vir::ViperIdent::new(domain_name), 0);

            let self_type = domain_ident();

            let from_int_name = vir::vir_format!(vcx, "{}_from_int", domain_name);

            let from_int = FunctionIdn::new(
                ViperIdent::new(from_int_name),
                vir::TYPE_INT.upcast_ty(),
                self_type,
            );

            let from_int_data = vcx.mk_domain_function(
                from_int,
                false,
                Some(match *task_key {
                    BitVecSize::BitVec8 => "(_ int2bv 8)",
                    BitVecSize::BitVec16 => "(_ int2bv 16)",
                    BitVecSize::BitVec32 => "(_ int2bv 32)",
                    BitVecSize::BitVec64 => "(_ int2bv 64)",
                    BitVecSize::BitVec128 => "(_ int2bv 128)",
                }),
            );

            let ubv_to_int_name = vir::vir_format!(vcx, "{}_ubv_to_int", domain_name);
            let ubv_to_int = FunctionIdn::new(
                ViperIdent::new(ubv_to_int_name),
                self_type,
                vir::TYPE_INT.upcast_ty(),
            );
            let ubv_to_int_data = vcx.mk_domain_function(ubv_to_int, false, Some("ubv_to_int"));

            let sbv_to_int_name = vir::vir_format!(vcx, "{}_sbv_to_int", domain_name);
            let sbv_to_int = FunctionIdn::new(
                ViperIdent::new(sbv_to_int_name),
                self_type,
                vir::TYPE_INT.upcast_ty(),
            );
            let sbv_to_int_data = vcx.mk_domain_function(sbv_to_int, false, Some("sbv_to_int"));

            let bv_and_name = vir::vir_format!(vcx, "{}_bv_and", domain_name);
            let bv_and = FunctionIdn::new(
                ViperIdent::new(bv_and_name),
                (self_type, self_type),
                self_type,
            );
            let bv_and_data = vcx.mk_domain_function(bv_and, false, Some("bvand"));

            let bv_xor_name = vir::vir_format!(vcx, "{}_bv_xor", domain_name);
            let bv_xor = FunctionIdn::new(
                ViperIdent::new(bv_xor_name),
                (self_type, self_type),
                self_type,
            );
            let bv_xor_data = vcx.mk_domain_function(bv_xor, false, Some("bvxor"));

            let bv_or_name = vir::vir_format!(vcx, "{}_bv_or", domain_name);
            let bv_or = FunctionIdn::new(
                ViperIdent::new(bv_or_name),
                (self_type, self_type),
                self_type,
            );
            let bv_or_data = vcx.mk_domain_function(bv_or, false, Some("bvor"));

            let bv_shl_name = vir::vir_format!(vcx, "{}_bv_shl", domain_name);
            let bv_shl = FunctionIdn::new(
                ViperIdent::new(bv_shl_name),
                (self_type, self_type),
                self_type,
            );
            let bv_shl_data = vcx.mk_domain_function(bv_shl, false, Some("bvshl"));

            let bv_shr_name = vir::vir_format!(vcx, "{}_bv_shr", domain_name);
            let bv_shr = FunctionIdn::new(
                ViperIdent::new(bv_shr_name),
                (self_type, self_type),
                self_type,
            );
            let bv_shr_data = vcx.mk_domain_function(bv_shr, false, Some("bvlshr"));

            let functions = &[
                from_int_data,
                ubv_to_int_data,
                sbv_to_int_data,
                bv_and_data,
                bv_xor_data,
                bv_or_data,
                bv_shl_data,
                bv_shr_data,
            ];

            let domain_data = vcx.mk_domain::<(), !>(
                domain_ident.name(),
                &[],
                &[],
                vcx.alloc_slice(functions),
                match *task_key {
                    BitVecSize::BitVec8 => Some(vcx.alloc_slice(&[
                        vcx.alloc(BackendInterpretationPair {
                            key: "SMTLIB",
                            value: "(_ BitVec 8)",
                        }),
                        vcx.alloc(BackendInterpretationPair {
                            key: ("Boogie"),
                            value: ("bv8"),
                        }),
                    ])),
                    BitVecSize::BitVec16 => Some(vcx.alloc_slice(&[
                        vcx.alloc(BackendInterpretationPair {
                            key: "SMTLIB",
                            value: "(_ BitVec 16)",
                        }),
                        vcx.alloc(BackendInterpretationPair {
                            key: ("Boogie"),
                            value: ("bv16"),
                        }),
                    ])),
                    BitVecSize::BitVec32 => Some(vcx.alloc_slice(&[
                        vcx.alloc(BackendInterpretationPair {
                            key: "SMTLIB",
                            value: "(_ BitVec 32)",
                        }),
                        vcx.alloc(BackendInterpretationPair {
                            key: ("Boogie"),
                            value: ("bv32"),
                        }),
                    ])),
                    BitVecSize::BitVec64 => Some(vcx.alloc_slice(&[
                        vcx.alloc(BackendInterpretationPair {
                            key: "SMTLIB",
                            value: "(_ BitVec 64)",
                        }),
                        vcx.alloc(BackendInterpretationPair {
                            key: ("Boogie"),
                            value: ("bv64"),
                        }),
                    ])),
                    BitVecSize::BitVec128 => Some(vcx.alloc_slice(&[
                        vcx.alloc(BackendInterpretationPair {
                            key: "SMTLIB",
                            value: "(_ BitVec 128)",
                        }),
                        vcx.alloc(BackendInterpretationPair {
                            key: ("Boogie"),
                            value: ("bv128"),
                        }),
                    ])),
                },
            );

            deps.emit_output_ref(*task_key, ())?;
            Ok((
                domain_data,
                BitVecDomain {
                    domain: domain_ident,
                    from_int,
                    ubv_to_int,
                    sbv_to_int,
                    bv_xor,
                    bv_and,
                    bv_or,
                    bv_shl,
                    bv_shr,
                },
            ))
        })
    }
}
