use std::cell::RefCell;
use prusti_interface::environment::EnvBody;
use prusti_rustc_interface::middle::ty;

use crate::data::*;
use crate::gendata::*;
use crate::genrefs::*;
use crate::refs::*;

/// The VIR context is a data structure used throughout the encoding process.
pub struct VirCtxt<'tcx> {
    /// The arena used for bump allocating all VIR AST data. Anything allocated
    /// in the arena (using [VirCtxt::alloc] or similar) is returned as a
    /// shared reference (with the `'tcx` lifetime). This means that different
    /// parts of the AST can refer to the same node, without the need for
    /// unnecessary cloning.
    pub arena: bumpalo::Bump,

    /// The stack of spans during the encoding process. (TODO)
    pub span_stack: Vec<i32>,
    // TODO: span stack
    // TODO: error positions?

    /// The compiler's typing context. This allows convenient access to most
    /// of the compiler's APIs.
    pub tcx: ty::TyCtxt<'tcx>,

    pub body: RefCell<EnvBody<'tcx>>,
    
}

impl<'tcx> VirCtxt<'tcx> {
    pub fn new(tcx: ty::TyCtxt<'tcx>, body: EnvBody<'tcx>) -> Self {
        Self {
            arena: bumpalo::Bump::new(),
            span_stack: vec![],
            tcx,
            body: RefCell::new(body),
        }
    }

    /// Moves `val` into the arena and returns a shared reference to the data.
    pub fn alloc<T>(&self, val: T) -> &T {
        &*self.arena.alloc(val)
    }

    pub fn alloc_str(&self, val: &str) -> &str {
        &*self.arena.alloc_str(val)
    }

/*    pub fn alloc_slice<'a, T: Copy>(&'tcx self, val: &'a [T]) -> &'tcx [T] {
        &*self.arena.alloc_slice_copy(val)
        }*/
    pub fn alloc_slice<T: Copy>(&self, val: &[T]) -> &[T] {
        &*self.arena.alloc_slice_copy(val)
    }

    pub fn mk_local<'vir>(&'vir self, name: &'vir str) -> Local<'vir> {
        self.arena.alloc(LocalData {
            name,
        })
    }
    pub fn mk_local_decl<'vir>(&'vir self, name: &'vir str, ty: Type<'vir>) -> LocalDecl<'vir> {
        self.arena.alloc(LocalDeclData {
            name,
            ty,
        })
    }
    pub fn mk_local_ex_local<'vir, Curr, Next>(&'vir self, local: Local<'vir>) -> ExprGen<'vir, Curr, Next> {
        self.arena.alloc(ExprGenData::Local(local))
    }
    pub fn mk_local_ex<'vir, Curr, Next>(&'vir self, name: &'vir str) -> ExprGen<'vir, Curr, Next> {
        self.mk_local_ex_local(self.mk_local(name))
    }
    pub(crate) fn mk_func_app<'vir, Curr, Next>(
        &'vir self,
        target: &'vir str,
        src_args: &[ExprGen<'vir, Curr, Next>],
    ) -> ExprGen<'vir, Curr, Next> {
        self.arena.alloc(ExprGenData::FuncApp(self.arena.alloc(FuncAppGenData {
            target,
            args: self.alloc_slice(src_args),
        })))
    }
    pub fn mk_pred_app<'vir>(&'vir self, target: &'vir str, src_args: &[Expr<'vir>]) -> Expr<'vir> {
        self.arena.alloc(ExprData::PredicateApp(self.arena.alloc(PredicateAppData {
            target,
            args: self.alloc_slice(src_args),
        })))
    }

    pub const fn mk_bool<'vir, const VALUE: bool>(&'vir self) -> Expr<'vir> {
        &ExprData::Const(&ConstData::Bool(VALUE))
    }
    pub const fn mk_int<'vir, const VALUE: i128>(&'vir self) -> Expr<'vir> {
        if VALUE < 0 {
            &ExprData::UnOp(&UnOpData {
                kind: UnOpKind::Neg,
                expr: &ExprData::Const(&ConstData::Int((-VALUE) as u128)),
            })
        } else {
            &ExprData::Const(&ConstData::Int(VALUE as u128))
        }
    }
    pub const fn mk_uint<'vir, const VALUE: u128>(&'vir self) -> Expr<'vir> {
        &ExprData::Const(&ConstData::Int(VALUE))
    }

    const fn get_int_data(ty: Type, rust_ty: &ty::TyKind) -> (u32, bool) {
        assert!(matches!(rust_ty, ty::Int(_) | ty::Uint(_)));
        let TypeData::Int { bit_width, signed } = *ty else {
            unreachable!();
        };
        assert!(matches!(rust_ty, ty::Int(_)) == signed);
        (bit_width as u32, signed)
    }
    pub const fn get_min_int<'vir>(&'vir self, ty: Type, rust_ty: &ty::TyKind) -> Expr<'vir> {
        match Self::get_int_data(ty, rust_ty) {
            (_, false) => self.mk_uint::<0>(),
            (i8::BITS, true) => self.mk_int::<{ i8::MIN as i128 }>(),
            (i16::BITS, true) => self.mk_int::<{ i16::MIN as i128 }>(),
            (i32::BITS, true) => self.mk_int::<{ i32::MIN as i128 }>(),
            (i64::BITS, true) => self.mk_int::<{ i64::MIN as i128 }>(),
            (i128::BITS, true) => self.mk_int::<{ i128::MIN }>(),
            (_, true) => unreachable!(),
        }
    }
    pub const fn get_max_int<'vir>(&'vir self, ty: Type, rust_ty: &ty::TyKind) -> Expr<'vir> {
        match Self::get_int_data(ty, rust_ty) {
            (u8::BITS, false) => self.mk_uint::<{ u8::MAX as u128 }>(),
            (u16::BITS, false) => self.mk_uint::<{ u16::MAX as u128 }>(),
            (u32::BITS, false) => self.mk_uint::<{ u32::MAX as u128 }>(),
            (u64::BITS, false) => self.mk_uint::<{ u64::MAX as u128 }>(),
            (u128::BITS, false) => self.mk_uint::<{ u128::MAX }>(),
            (i8::BITS, true) => self.mk_int::<{ i8::MAX as i128 }>(),
            (i16::BITS, true) => self.mk_int::<{ i16::MAX as i128 }>(),
            (i32::BITS, true) => self.mk_int::<{ i32::MAX as i128 }>(),
            (i64::BITS, true) => self.mk_int::<{ i64::MAX as i128 }>(),
            (i128::BITS, true) => self.mk_int::<{ i128::MAX }>(),
            _ => unreachable!(),
        }
    }
    pub fn get_modulo_int<'vir>(&'vir self, ty: Type, rust_ty: &ty::TyKind) -> Expr<'vir> {
        match Self::get_int_data(ty, rust_ty) {
            (u8::BITS, _) => self.mk_uint::<{ 1_u128 << u8::BITS }>(),
            (u16::BITS, _) => self.mk_uint::<{ 1_u128 << u16::BITS }>(),
            (u32::BITS, _) => self.mk_uint::<{ 1_u128 << u32::BITS }>(),
            (u64::BITS, _) => self.mk_uint::<{ 1_u128 << u64::BITS }>(),
            (u128::BITS, _) => {
                // TODO: make this a `const` once `Expr` isn't invariant in `'vir` so that it can be `'const` instead
                let half = self.mk_uint::<{ 1_u128 << u64::BITS }>();
                self.alloc(ExprData::BinOp(self.alloc(BinOpGenData { kind: BinOpKind::Add, lhs: half, rhs: half })))
            }
            _ => unreachable!(),
        }
    }
    pub fn get_signed_shift_int<'vir>(&'vir self, ty: Type, rust_ty: &ty::TyKind) -> Option<Expr<'vir>> {
        let int = match Self::get_int_data(ty, rust_ty) {
            (_, false) => return None,
            (u8::BITS, true) => self.mk_uint::<{ 1_u128 << (u8::BITS - 1) }>(),
            (u16::BITS, true) => self.mk_uint::<{ 1_u128 << (u16::BITS - 1) }>(),
            (u32::BITS, true) => self.mk_uint::<{ 1_u128 << (u32::BITS - 1) }>(),
            (u64::BITS, true) => self.mk_uint::<{ 1_u128 << (u64::BITS - 1) }>(),
            (u128::BITS, true) => self.mk_uint::<{ 1_u128 << (u128::BITS - 1) }>(),
            (_, true) => unreachable!(),
        };
        Some(int)
    }
    pub fn get_bit_width_int<'vir>(&'vir self, ty: Type, rust_ty: &ty::TyKind) -> Expr<'vir> {
        match Self::get_int_data(ty, rust_ty) {
            (u8::BITS, _) => self.mk_uint::<{ u8::BITS as u128 }>(),
            (u16::BITS, _) => self.mk_uint::<{ u16::BITS as u128 }>(),
            (u32::BITS, _) => self.mk_uint::<{ u32::BITS as u128 }>(),
            (u64::BITS, _) => self.mk_uint::<{ u64::BITS as u128 }>(),
            (u128::BITS, _) => self.mk_uint::<{ u128::BITS as u128 }>(),
            _ => unreachable!(),
        }
    }

    pub fn mk_conj<'vir>(&'vir self, elems: &[Expr<'vir>]) -> Expr<'vir> {
        if elems.len() == 0 {
            return self.mk_bool::<true>();
        }
        let mut e = elems[0];
        for i in 1..elems.len() {
            e = self.alloc(ExprData::BinOp(self.alloc(BinOpData {
                kind: BinOpKind::And,
                lhs: e,
                rhs: elems[i],
            })));
        }
        e
    }
}

thread_local! {
    static VCTX: RefCell<Option<VirCtxt<'static>>> = RefCell::new(None);
}

/// Initialises the VIR context. Should only be called once, when the type
/// context is available.
pub fn init_vcx<'tcx>(vcx: VirCtxt<'tcx>) {
    VCTX.replace(Some(unsafe { std::mem::transmute(vcx) }));
}

/// Perform an action with the VIR context.
pub fn with_vcx<'vir, 'tcx: 'vir, F, R>(f: F) -> R
where
    F: FnOnce(&'vir VirCtxt<'tcx>) -> R,
{
    VCTX.with_borrow(|vcx: &Option<VirCtxt<'static>>| {
        // SAFETY: the 'vir and 'tcx given to this function will always be
        //   the same (or shorter) than the lifetimes of the VIR arena and
        //   the rustc type context, respectively
        let vcx = vcx.as_ref().unwrap();
        let vcx = unsafe { std::mem::transmute(vcx) };
        f(vcx)
    })
}
