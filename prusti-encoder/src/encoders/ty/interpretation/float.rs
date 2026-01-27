use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoderDependencies};
use vir::{BackendInterpretationPair, CallableIdn, FunctionIdn, VirCtxt};

use crate::encoders::ty::{
    interpretation::bitvec::{BitVecEnc, BitVecSize},
    pure::{DomainBuilder, TyPureEnc},
};

pub type FloatDomain<'vir> = &'vir FloatDomainData<'vir>;

#[derive(Debug, Clone, Copy)]
pub struct FloatDomainData<'vir> {
    #[allow(unused)]
    pub from_bv: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    pub fp_eq: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub fp_add: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub fp_sub: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub fp_mul: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub fp_div: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::CSnap>,
    pub fp_trunc: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    pub fp_is_nan: FunctionIdn<'vir, vir::CSnap, vir::Bool>,
    pub fp_is_infinite: FunctionIdn<'vir, vir::CSnap, vir::Bool>,
    pub fp_lt: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub fp_leq: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub fp_gt: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub fp_geq: FunctionIdn<'vir, (vir::CSnap, vir::CSnap), vir::Bool>,
    pub fp_neg: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    pub fp_abs: FunctionIdn<'vir, vir::CSnap, vir::CSnap>,
    pub fp_to_real: FunctionIdn<'vir, vir::CSnap, vir::Perm>,
}

pub(crate) fn ty_pure_float<'vir>(
    vcx: &'vir VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TyPureEnc>,
    builder: &mut DomainBuilder<'vir>,
    float: ty::FloatTy,
    prim_to_snap: FunctionIdn<'vir, vir::Prim, vir::CSnap>,
) -> Result<FloatDomainData<'vir>, EncodeFullError<'vir, TyPureEnc>> {
    let i = match float {
        ty::FloatTy::F16 => vcx.alloc_slice(&[
            vcx.alloc(BackendInterpretationPair {
                key: "SMTLIB",
                value: "(_ FloatingPoint 5 11)",
            }),
            vcx.alloc(BackendInterpretationPair {
                key: ("Boogie"),
                value: ("float11e5"),
            }),
        ]),
        ty::FloatTy::F32 => vcx.alloc_slice(&[
            vcx.alloc(BackendInterpretationPair {
                key: "SMTLIB",
                value: "(_ FloatingPoint 8 24)",
            }),
            vcx.alloc(BackendInterpretationPair {
                key: ("Boogie"),
                value: ("float24e8"),
            }),
        ]),
        ty::FloatTy::F64 => vcx.alloc_slice(&[
            vcx.alloc(BackendInterpretationPair {
                key: "SMTLIB",
                value: "(_ FloatingPoint 11 53)",
            }),
            vcx.alloc(BackendInterpretationPair {
                key: ("Boogie"),
                value: ("float53e11"),
            }),
        ]),
        ty::FloatTy::F128 => vcx.alloc_slice(&[
            vcx.alloc(BackendInterpretationPair {
                key: "SMTLIB",
                value: "(_ FloatingPoint 15 113)",
            }),
            vcx.alloc(BackendInterpretationPair {
                key: ("Boogie"),
                value: ("float113e15"),
            }),
        ]),
    };
    builder.set_interpretation(i);

    let fp_eq = builder.backend_func(
        "eq",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        Some("fp.eq"),
    );

    let fp_add = builder.backend_func(
        "add",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        Some("fp.add RNE"),
    );

    let fp_sub = builder.backend_func(
        "sub",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        Some("fp.sub RNE"),
    );

    let fp_mul = builder.backend_func(
        "mul",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        Some("fp.mul RNE"),
    );

    let fp_div = builder.backend_func(
        "div",
        (builder.self_type(), builder.self_type()),
        builder.self_type(),
        Some("fp.div RNE"),
    );

    let fp_trunc = builder.backend_func(
        "trunc",
        builder.self_type(),
        builder.self_type(),
        Some("fp.roundToIntegral RTZ"),
    );

    let fp_is_nan = builder.backend_func(
        "is_nan",
        builder.self_type(),
        vir::TYPE_BOOL,
        Some("fp.isNaN"),
    );

    let fp_is_infinite = builder.backend_func(
        "is_infinite",
        builder.self_type(),
        vir::TYPE_BOOL,
        Some("fp.isInfinite"),
    );

    let fp_lt = builder.backend_func(
        "lt",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        Some("fp.lt"),
    );
    let fp_leq = builder.backend_func(
        "leq",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        Some("fp.leq"),
    );
    let fp_geq = builder.backend_func(
        "geq",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        Some("fp.geq"),
    );
    let fp_gt = builder.backend_func(
        "gt",
        (builder.self_type(), builder.self_type()),
        vir::TYPE_BOOL,
        Some("fp.gt"),
    );
    let fp_neg = builder.backend_func(
        "neg",
        builder.self_type(),
        builder.self_type(),
        Some("fp.neg"),
    );

    let fp_abs = builder.backend_func(
        "abs",
        builder.self_type(),
        builder.self_type(),
        Some("fp.abs"),
    );

    let bit_vec = deps.require_dep::<BitVecEnc>(match float {
        ty::FloatTy::F16 => BitVecSize::BitVec16,
        ty::FloatTy::F32 => BitVecSize::BitVec32,
        ty::FloatTy::F64 => BitVecSize::BitVec64,
        ty::FloatTy::F128 => BitVecSize::BitVec128,
    })?;

    let i = match float {
        ty::FloatTy::F16 => "(_ to_fp 5 11)",
        ty::FloatTy::F32 => "(_ to_fp 8 24)",
        ty::FloatTy::F64 => "(_ to_fp 11 53)",
        ty::FloatTy::F128 => "(_ to_fp 15 113)",
    };
    let from_bv = builder.backend_func("from_bv", (bit_vec.domain)(), builder.self_type(), Some(i));

    let fp_to_real = builder.backend_func(
        "to_real",
        builder.self_type(),
        vir::TYPE_PERM,
        Some("fp.to_real"),
    );

    builder.axiom("prim_to_snap", vir::expr! {
        forall i: [prim_to_snap.arity()] :: {[prim_to_snap](i)} (([prim_to_snap](i)) == ([from_bv]([bit_vec.from_int](i)))) && (([fp_to_real]([prim_to_snap](i))) == ([fp_to_real]([from_bv]([bit_vec.from_int](i)))))
    });

    Ok(FloatDomainData {
        from_bv,
        fp_eq,
        fp_add,
        fp_sub,
        fp_mul,
        fp_div,
        fp_trunc,
        fp_is_nan,
        fp_is_infinite,
        fp_lt,
        fp_leq,
        fp_gt,
        fp_geq,
        fp_neg,
        fp_abs,
        fp_to_real,
    })
}
