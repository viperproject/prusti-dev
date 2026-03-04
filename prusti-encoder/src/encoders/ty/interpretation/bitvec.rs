use task_encoder::TaskEncoder;
use vir::{
    BackendInterpretationPair, CastType, DomainGenData, DomainIdnCSnap, FunctionIdn, ViperIdent,
};

#[derive(Eq, PartialEq, Hash, Debug, Clone, Copy)]
pub enum BitVecSize {
    BitVec16,
    BitVec32,
    BitVec64,
    BitVec128,
}

#[derive(Debug, Clone, Copy)]
pub struct BitVecDomain<'vir> {
    pub domain: vir::DomainIdn<'vir, vir::CSnap>,
    pub from_int: FunctionIdn<'vir, vir::Prim, vir::CSnap>,
}

pub struct BitVecEnc;

impl TaskEncoder for BitVecEnc {
    task_encoder::encoder_cache!(BitVecEnc);

    type TaskDescription<'vir> = BitVecSize;

    type OutputFullLocal<'vir> = &'vir DomainGenData<'vir, (), !>;

    type OutputFullDependency<'vir> = BitVecDomain<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors() {
            program.add_domain(output);
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let domain_name = match *task_key {
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
                    BitVecSize::BitVec16 => "(_ int2bv 16)",
                    BitVecSize::BitVec32 => "(_ int2bv 32)",
                    BitVecSize::BitVec64 => "(_ int2bv 64)",
                    BitVecSize::BitVec128 => "(_ int2bv 128)",
                }),
            );

            let functions = &[from_int_data];

            let domain_data = vcx.mk_domain::<(), !>(
                domain_ident.name(),
                &[],
                &[],
                vcx.alloc_slice(functions),
                match *task_key {
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
                },
            ))
        })
    }
}
