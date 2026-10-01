use prusti_rustc_interface::middle::ty;
use task_encoder::TaskEncoder;
use vir::{CastType, DomainGenData, FunctionIdn, ViperIdent};

use crate::encoders::ty::{
    RustTyDecomposition,
    interpretation::bitvec::{BitVecDomain, BitVecEnc, BitVecSize},
    use_pure::TyUsePureEnc,
};

/// Conversions between a float and a bitvector of the width of an integer type
/// (used by `as` casts). These live in their own domain, separate from the
/// float domain, so that only the bitvector widths which are actually used in
/// casts are emitted.
#[derive(Debug, Clone, Copy)]
pub struct FloatBitVecConv<'vir> {
    pub bitvec: BitVecDomain<'vir>,
    /// `(_ fp.to_sbv N) RTZ`: unspecified for values outside the range of `iN`.
    pub to_sbv: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    /// `(_ fp.to_ubv N) RTZ`: unspecified for values outside the range of `uN`.
    pub to_ubv: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    /// `(_ to_fp_unsigned eb sb) RNE`: interprets the bitvector as unsigned.
    pub from_ubv: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
}

pub struct FloatBitVecConvEnc;

impl TaskEncoder for FloatBitVecConvEnc {
    task_encoder::encoder_cache!(FloatBitVecConvEnc);
    const ENCODER_NAME: &'static str = "float bitvec conversion encoder";

    type TaskDescription<'vir> = (ty::FloatTy, BitVecSize);

    type OutputFullLocal<'vir> = &'vir DomainGenData<'vir, (), !>;

    type OutputFullDependency<'vir> = FloatBitVecConv<'vir>;

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
        let (float, size) = *task_key;
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let float_ty = match float {
                ty::FloatTy::F16 => vcx.tcx().types.f16,
                ty::FloatTy::F32 => vcx.tcx().types.f32,
                ty::FloatTy::F64 => vcx.tcx().types.f64,
                ty::FloatTy::F128 => vcx.tcx().types.f128,
            };
            let float_snap = deps
                .require_ref::<TyUsePureEnc>(RustTyDecomposition::from_prim_ty(float_ty))?
                .snapshot
                .downcast_ty::<vir::CSnap>();
            let bitvec = deps.require_dep::<BitVecEnc>(size)?;
            let bv_snap = (bitvec.domain)();

            let bits = size.bits();
            let (ebits, sbits) = float_format(float);
            let domain_name =
                vir::vir_format!(vcx, "s_Float_{}_BitVec_{bits}_conv", float.name_str());

            let mk_fn = |name: &str, arg, ret, interpretation| {
                let ident = FunctionIdn::new(
                    ViperIdent::new(vir::vir_format!(vcx, "{domain_name}_{name}")),
                    arg,
                    ret,
                );
                (
                    ident,
                    vcx.mk_domain_function(ident, false, Some(interpretation)),
                )
            };
            let (to_sbv, to_sbv_data) = mk_fn(
                "to_sbv",
                float_snap,
                bv_snap,
                vir::vir_format!(vcx, "(_ fp.to_sbv {bits}) RTZ"),
            );
            let (to_ubv, to_ubv_data) = mk_fn(
                "to_ubv",
                float_snap,
                bv_snap,
                vir::vir_format!(vcx, "(_ fp.to_ubv {bits}) RTZ"),
            );
            let (from_ubv, from_ubv_data) = mk_fn(
                "from_ubv",
                bv_snap,
                float_snap,
                vir::vir_format!(vcx, "(_ to_fp_unsigned {ebits} {sbits}) RNE"),
            );

            let domain_data = vcx.mk_domain::<(), !>(
                ViperIdent::new(domain_name),
                &[],
                &[],
                vcx.alloc_slice(&[to_sbv_data, to_ubv_data, from_ubv_data]),
                None,
            );

            Ok((
                domain_data,
                FloatBitVecConv {
                    bitvec,
                    to_sbv,
                    to_ubv,
                    from_ubv,
                },
            ))
        })
    }
}

/// The SMT-LIB `(eb, sb)` parameters of a float format (`sb` includes the
/// hidden bit).
fn float_format(float: ty::FloatTy) -> (u32, u32) {
    match float {
        ty::FloatTy::F16 => (5, 11),
        ty::FloatTy::F32 => (8, 24),
        ty::FloatTy::F64 => (11, 53),
        ty::FloatTy::F128 => (15, 113),
    }
}

/// The raw bits of the float `±2^exp` (`±inf` if it is out of range).
pub fn float_pow2_bits(float: ty::FloatTy, exp: u32, negative: bool) -> u128 {
    let (ebits, sbits) = float_format(float);
    let bias = (1u128 << (ebits - 1)) - 1;
    let biased_exp = if u128::from(exp) > bias {
        (1u128 << ebits) - 1
    } else {
        u128::from(exp) + bias
    };
    let sign = if negative {
        1u128 << (ebits + sbits - 1)
    } else {
        0
    };
    sign | (biased_exp << (sbits - 1))
}
