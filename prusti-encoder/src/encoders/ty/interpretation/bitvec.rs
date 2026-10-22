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

impl BitVecSize {
    pub fn from_bits(bits: u32) -> Self {
        match bits {
            8 => BitVecSize::BitVec8,
            16 => BitVecSize::BitVec16,
            32 => BitVecSize::BitVec32,
            64 => BitVecSize::BitVec64,
            128 => BitVecSize::BitVec128,
            _ => unreachable!("unsupported bitvector width {bits}"),
        }
    }

    pub fn to_bits(self) -> u32 {
        match self {
            BitVecSize::BitVec8 => 8,
            BitVecSize::BitVec16 => 16,
            BitVecSize::BitVec32 => 32,
            BitVecSize::BitVec64 => 64,
            BitVecSize::BitVec128 => 128,
        }
    }

    pub fn domain_name(&self) -> &'static str {
        match *self {
            BitVecSize::BitVec8 => "s_BitVec_8",
            BitVecSize::BitVec16 => "s_BitVec_16",
            BitVecSize::BitVec32 => "s_BitVec_32",
            BitVecSize::BitVec64 => "s_BitVec_64",
            BitVecSize::BitVec128 => "s_BitVec_128",
        }
    }

    pub fn int_to_bv_interpretation(&self) -> &'static str {
        match *self {
            BitVecSize::BitVec8 => "(_ int2bv 8)",
            BitVecSize::BitVec16 => "(_ int2bv 16)",
            BitVecSize::BitVec32 => "(_ int2bv 32)",
            BitVecSize::BitVec64 => "(_ int2bv 64)",
            BitVecSize::BitVec128 => "(_ int2bv 128)",
        }
    }

    pub fn interpretation(&self) -> (&'static str, &'static str) {
        match *self {
            BitVecSize::BitVec8 => ("(_ BitVec 8)", "bv8"),
            BitVecSize::BitVec16 => ("(_ BitVec 16)", "bv16"),
            BitVecSize::BitVec32 => ("(_ BitVec 32)", "bv32"),
            BitVecSize::BitVec64 => ("(_ BitVec 64)", "bv64"),
            BitVecSize::BitVec128 => ("(_ BitVec 128)", "bv128"),
        }
    }
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

impl BitVecEnc {
    /// Creates a binary domain function `<domain_name>_<suffix>` on the
    /// bitvector domain, interpreted as the given SMT-LIB function.
    fn mk_binop<'vir>(
        vcx: &'vir vir::VirCtxt<'_>,
        domain_name: &str,
        self_type: vir::Type<'vir, vir::CSnap>,
        suffix: &str,
        interpretation: &'vir str,
    ) -> (
        FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
        vir::DomainFunction<'vir>,
    ) {
        let name = vir::vir_format!(vcx, "{}_{}", domain_name, suffix);
        let ident = FunctionIdn::new(ViperIdent::new(name), (self_type, self_type), self_type);
        let data = vcx.mk_domain_function(ident, false, Some(interpretation));
        (ident, data)
    }
}

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
            let domain_name = task_key.domain_name();

            let domain_ident = DomainIdnCSnap::new(vir::ViperIdent::new(domain_name), 0);

            let self_type = domain_ident();

            let from_int_name = vir::vir_format!(vcx, "{}_from_int", domain_name);

            let from_int = FunctionIdn::new(
                ViperIdent::new(from_int_name),
                vir::TYPE_INT.upcast_ty(),
                self_type,
            );

            let from_int_data =
                vcx.mk_domain_function(from_int, false, Some(task_key.int_to_bv_interpretation()));

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

            let (bv_and, bv_and_data) =
                Self::mk_binop(vcx, domain_name, self_type, "bv_and", "bvand");
            let (bv_xor, bv_xor_data) =
                Self::mk_binop(vcx, domain_name, self_type, "bv_xor", "bvxor");
            let (bv_or, bv_or_data) = Self::mk_binop(vcx, domain_name, self_type, "bv_or", "bvor");
            let (bv_shl, bv_shl_data) =
                Self::mk_binop(vcx, domain_name, self_type, "bv_shl", "bvshl");
            let (bv_shr, bv_shr_data) =
                Self::mk_binop(vcx, domain_name, self_type, "bv_shr", "bvlshr");

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

            let (smtlib_interpretation, boogie_interpretation) = task_key.interpretation();

            let domain_data = vcx.mk_domain::<(), !>(
                domain_ident.name(),
                &[],
                &[],
                vcx.alloc_slice(functions),
                Some(vcx.alloc_slice(&[
                    vcx.alloc(BackendInterpretationPair {
                        key: "SMTLIB",
                        value: smtlib_interpretation,
                    }),
                    vcx.alloc(BackendInterpretationPair {
                        key: ("Boogie"),
                        value: boogie_interpretation,
                    }),
                ])),
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
