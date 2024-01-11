use prusti_interface::environment::EnvBody;
use prusti_rustc_interface::middle::ty;
use std::cell::RefCell;

use crate::{data::*, gendata::*, genrefs::*, refs::*};

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

    pub fn alloc_slice<T: Copy>(&self, val: &[T]) -> &[T] {
        &*self.arena.alloc_slice_copy(val)
    }
    pub fn alloc_array<T: Copy, const N: usize>(&self, val: &[T; N]) -> &[T; N] {
        &*self.arena.alloc(*val)
    }

    pub fn mk_local<'vir>(&'vir self, name: &'vir str, ty: Type<'vir>) -> Local<'vir> {
        self.alloc(LocalData { name, ty })
    }
    pub fn mk_local_decl<'vir>(&'vir self, name: &'vir str, ty: Type<'vir>) -> LocalDecl<'vir> {
        self.alloc(LocalDeclData { name, ty })
    }
    pub fn mk_local_decl_local<'vir>(&'vir self, local: Local<'vir>) -> LocalDecl<'vir> {
        self.alloc(LocalDeclData { name: local.name, ty: local.ty })
    }

    pub fn mk_local_ex_local<'vir, Curr, Next>(
        &'vir self,
        local: Local<'vir>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {
            kind: self.alloc(ExprKindGenData::Local(local)),
        })
    }
    pub fn mk_local_ex<'vir, Curr, Next>(&'vir self, name: &'vir str, ty: Type<'vir>) -> ExprGen<'vir, Curr, Next> {
        self.mk_local_ex_local(self.mk_local(name, ty))
    }
    pub(crate) fn mk_func_app<'vir, Curr, Next>(
        &'vir self,
        target: &'vir str,
        src_args: &[ExprGen<'vir, Curr, Next>],
        result_ty: Option<Type<'vir>>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {
            kind: self.alloc(ExprKindGenData::FuncApp(self.arena.alloc(FuncAppGenData {
                target,
                args: self.alloc_slice(src_args),
                result_ty,
            }))),
        })
    }

    pub fn mk_lazy_expr<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str,
        func: Box<dyn for<'a> Fn(&'vir VirCtxt<'a>, Curr) -> Next + 'vir>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {
            kind: self.alloc(ExprKindGenData::Lazy(name, func)),
        })
    }

    pub fn mk_ternary_expr<'vir, Curr, Next>(
        &'vir self,
        cond: ExprGen<'vir, Curr, Next>,
        then: ExprGen<'vir, Curr, Next>,
        else_: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {
            kind: self.alloc(ExprKindGenData::Ternary(self.alloc(TernaryGenData {
                cond,
                then,
                else_,
            }))),
        })
    }

    pub fn mk_unary_op_expr<'vir, Curr, Next>(
        &'vir self,
        kind: UnOpKind,
        expr: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {
            kind: self.alloc(ExprKindGenData::UnOp(
                self.alloc(UnOpGenData { kind, expr }),
            )),
        })
    }

    pub fn mk_old_expr<'vir, Curr, Next>(
        &'vir self,
        expr: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {
            kind: self.alloc(ExprKindGenData::Old(expr)),
        })
    }

    pub fn mk_forall_expr<'vir, Curr, Next>(
        &'vir self,
        qvars: &'vir [LocalDecl<'vir>],
        triggers: &'vir [&'vir [ExprGen<'vir, Curr, Next>]],
        body: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {
            kind: self.alloc(ExprKindGenData::Forall(self.alloc(ForallGenData {
                qvars,
                triggers,
                body,
            }))),
        })
    }

    pub fn mk_let_expr<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str,
        val: ExprGen<'vir, Curr, Next>,
        expr: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {
            kind: self.alloc(ExprKindGenData::Let(self.alloc(LetGenData {
                name,
                val,
                expr,
            }))),
        })
    }

    pub fn mk_predicate_app_expr<'vir, Curr, Next>(
        &'vir self,
        pred_app: PredicateAppGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {
            kind: self.alloc(ExprKindGenData::PredicateApp(pred_app)),
        })
    }

    pub fn mk_bin_op_expr<'vir, Curr, Next>(
        &'vir self,
        kind: BinOpKind,
        lhs: ExprGen<'vir, Curr, Next>,
        rhs: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {
            kind: self.alloc(ExprKindGenData::BinOp(self.alloc(BinOpGenData {
                kind,
                lhs,
                rhs,
            }))),
        })
    }
    pub fn mk_eq_expr<'vir, Curr, Next>(
        &'vir self,
        lhs: ExprGen<'vir, Curr, Next>,
        rhs: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.mk_bin_op_expr(BinOpKind::CmpEq, lhs, rhs)
    }

    pub fn mk_field_expr<'vir, Curr, Next>(
        &'vir self,
        recv: ExprGen<'vir, Curr, Next>,
        field: Field<'vir>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {
            kind: self.alloc(ExprKindGenData::Field(recv, field)),
        })
    }

    pub fn mk_unfolding_expr<'vir, Curr, Next>(
        &'vir self,
        target: PredicateAppGen<'vir, Curr, Next>,
        expr: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {
            kind: self.alloc(ExprKindGenData::Unfolding(
                self.alloc(UnfoldingGenData { target, expr }),
            )),
        })
    }

    pub fn mk_acc_field_expr<'vir, Curr, Next>(
        &'vir self,
        recv: ExprGen<'vir, Curr, Next>,
        field: Field<'vir>,
        perm: Option<ExprGen<'vir, Curr, Next>>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {kind : self.alloc(ExprKindGenData::AccField(self.alloc(AccFieldGenData { recv, field, perm })))})
    }

    pub fn mk_const_expr<'vir, Curr, Next>(
        &'vir self,
        value: ConstData,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {kind : self.alloc(ExprKindGenData::Const(self.alloc(value)))})
    }

    pub fn mk_todo_expr<'vir, Curr, Next>(&'vir self, msg: &'vir str) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData {kind : self.alloc(ExprKindGenData::Todo(msg))})
    }

    pub const fn mk_bool<'vir, const VALUE: bool>(&'vir self) -> Expr<'vir> {
        &ExprGenData {kind : &ExprKindGenData::Const(&ConstData::Bool(VALUE))}
    }
    pub const fn mk_int<'vir, const VALUE: i128>(&'vir self) -> Expr<'vir> {
        if VALUE < 0 {
            &ExprGenData {kind : &ExprKindGenData::UnOp(&UnOpData {
                kind: UnOpKind::Neg,
                expr: &ExprGenData {kind : &ExprKindGenData::Const(&ConstData::Int((-VALUE) as u128))},
            })}
        } else {
            &ExprGenData {kind : &ExprKindGenData::Const(&ConstData::Int(VALUE as u128))}
        }
    }
    pub const fn mk_uint<'vir, const VALUE: u128>(&'vir self) -> Expr<'vir> {
        &ExprGenData {kind : &ExprKindGenData::Const(&ConstData::Int(VALUE))}
    }
    pub const fn mk_wildcard<'vir, Curr, Next>(&'vir self) -> ExprGen<'vir, Curr, Next> {
        &ExprGenData { kind : &ExprKindGenData::Const(&ConstData::Wildcard) }
    }
    pub const fn mk_null<'vir, Curr, Next>(&'vir self) -> ExprGen<'vir, Curr, Next> {
        &ExprGenData { kind : &ExprKindGenData::Const(&ConstData::Null) }
    }
    pub const fn mk_result<'vir, Curr, Next>(&'vir self) -> ExprGen<'vir, Curr, Next> {
        &ExprGenData { kind : &ExprKindGenData::Result }
    }

    pub fn mk_field<'vir>(
        &'vir self,
        name: &'vir str,
        ty: Type<'vir>,
    ) -> Field<'vir> {
        self.alloc(FieldData { name, ty })
    }

    pub fn mk_domain_axiom<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str,
        expr: ExprGen<'vir, Curr, Next>
    ) -> DomainAxiomGen<'vir, Curr, Next> {
        self.alloc(DomainAxiomGenData {
            name,
            expr
        })
    }

    pub fn mk_domain_function<'vir>(
        &'vir self,
        unique: bool,
        name: &'vir str,
        args: &'vir [Type<'vir>],
        ret: Type<'vir>,
    ) -> DomainFunction<'vir> {
        self.alloc(DomainFunctionData {
            unique,
            name,
            args,
            ret,
        })
    }

    pub fn mk_function<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str, // TODO: identifiers
        args: &'vir [LocalDecl<'vir>],
        ret: Type<'vir>,
        pres: &'vir [ExprGen<'vir, Curr, Next>],
        posts: &'vir [ExprGen<'vir, Curr, Next>],
        expr: Option<ExprGen<'vir, Curr, Next>>
    ) -> FunctionGen<'vir, Curr, Next> {
        // TODO: Typecheck pre and post conditions, expr and return type
        self.alloc(FunctionGenData {
            name,
            args,
            ret,
            pres,
            posts,
            expr
        })
    }

    pub fn mk_predicate<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str,
        args: &'vir [LocalDecl<'vir>],
        expr: Option<ExprGen<'vir, Curr, Next>>
    ) -> PredicateGen<'vir, Curr, Next> {
        self.alloc(PredicateGenData {
            name,
            args,
            expr
        })
    }

    pub fn mk_domain<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str,
        typarams: &'vir [DomainParamData<'vir>],
        axioms: &'vir [DomainAxiomGen<'vir, Curr, Next>],
        functions: &'vir [DomainFunction<'vir>]
    ) -> DomainGen<'vir, Curr, Next> {
        self.alloc(DomainGenData {
            name,
            typarams,
            axioms,
            functions
        })
    }

    pub fn mk_exhale_stmt<'vir, Curr, Next>(
        &'vir self,
        expr: ExprGen<'vir, Curr, Next>
    ) -> StmtGen<'vir, Curr, Next> {
        self.alloc(StmtGenData::Exhale(expr))
    }

    pub fn mk_unfold_stmt<'vir, Curr, Next>(
        &'vir self,
        pred_app: PredicateAppGen<'vir, Curr, Next>
    ) -> StmtGen<'vir, Curr, Next> {
        self.alloc(StmtGenData::Unfold(pred_app))
    }

    pub fn mk_fold_stmt<'vir, Curr, Next>(
        &'vir self,
        pred_app: PredicateAppGen<'vir, Curr, Next>
    ) -> StmtGen<'vir, Curr, Next> {
        self.alloc(StmtGenData::Fold(pred_app))
    }

    pub fn mk_pure_assign_stmt<'vir, Curr, Next>(
        &'vir self,
        lhs: ExprGen<'vir, Curr, Next>,
        rhs: ExprGen<'vir, Curr, Next>
    ) -> StmtGen<'vir, Curr, Next> {
        self.alloc(
            StmtGenData::PureAssign(
                self.alloc(PureAssignGenData {
                    lhs,
                    rhs
                })
            )
        )
    }

    pub fn mk_local_decl_stmt<'vir, Curr, Next>(
        &'vir self,
        local: LocalDecl<'vir>,
        expr: Option<ExprGen<'vir, Curr, Next>>
    ) ->  StmtGen<'vir, Curr, Next> {
        self.alloc(StmtGenData::LocalDecl(local, expr))
    }

    pub fn mk_assume_false_stmt<'vir, Curr, Next>(
        &'vir self
    ) -> TerminatorStmtGen<'vir, Curr, Next> {
        self.alloc(
            TerminatorStmtGenData::AssumeFalse
        )
    }

    pub fn mk_goto_stmt<'vir, Curr, Next>(
        &'vir self,
        block: CfgBlockLabel<'vir>
    ) -> TerminatorStmtGen<'vir, Curr, Next> {
        self.alloc(
            TerminatorStmtGenData::Goto(block)
        )
    }

    pub fn mk_dummy_stmt<'vir, Curr, Next>(
        &'vir self,
        msg: &'vir str
    ) -> TerminatorStmtGen<'vir, Curr, Next> {
        self.alloc(
            TerminatorStmtGenData::Dummy(msg)
        )
    }

    pub fn mk_comment_stmt<'vir, Curr, Next>(
        &'vir self,
        msg: &'vir str
    ) -> StmtGen<'vir, Curr, Next> {
        self.alloc(
            StmtGenData::Comment(msg)
        )
    }

    pub fn mk_goto_if_stmt<'vir, Curr, Next>(
        &'vir self,
        value: ExprGen<'vir, Curr, Next>,
        targets: &'vir [(ExprGen<'vir, Curr, Next>, CfgBlockLabel<'vir>, &'vir [StmtGen<'vir, Curr, Next>])],
        otherwise: CfgBlockLabel<'vir>,
        otherwise_statements: &'vir [StmtGen<'vir, Curr, Next>],
    ) -> TerminatorStmtGen<'vir, Curr, Next> {
        self.alloc(
            TerminatorStmtGenData::GotoIf(self.alloc(GotoIfGenData {
                value,
                targets,
                otherwise,
                otherwise_statements,
            }))
        )
    }

    pub fn mk_cfg_block<'vir, Curr, Next>(
        &'vir self,
        label: CfgBlockLabel<'vir>,
        stmts: &'vir [StmtGen<'vir, Curr, Next>],
        terminator: TerminatorStmtGen<'vir, Curr, Next>,
    ) -> CfgBlockGen<'vir, Curr, Next> {
        self.alloc(CfgBlockGenData {
            label,
            stmts,
            terminator
        })
    }

    pub fn mk_method<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str, // TODO: identifiers
        args: &'vir [LocalDecl<'vir>],
        rets: &'vir [LocalDecl<'vir>],
        pres: &'vir [ExprGen<'vir, Curr, Next>],
        posts: &'vir [ExprGen<'vir, Curr, Next>],
        blocks: Option<&'vir [CfgBlockGen<'vir, Curr, Next>]>, // first one is the entrypoint
    ) -> MethodGen<'vir, Curr, Next> {
        self.alloc(MethodGenData {
            name,
            args,
            rets,
            pres,
            posts,
            blocks
        })
    }

    pub fn mk_program<'vir, Curr, Next>(
        &'vir self,
        fields: &'vir [Field<'vir>],
        domains: &'vir [DomainGen<'vir, Curr, Next>],
        predicates: &'vir [PredicateGen<'vir, Curr, Next>],
        functions: &'vir [FunctionGen<'vir, Curr, Next>],
        methods: &'vir [MethodGen<'vir, Curr, Next>]
    ) -> ProgramGen<'vir, Curr, Next> {
        self.alloc(ProgramGenData {
            fields,
            domains,
            predicates,
            functions,
            methods
        })
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
                self.mk_bin_op_expr(BinOpKind::Add, half, half)
            }
            _ => unreachable!(),
        }
    }
    pub fn get_signed_shift_int<'vir>(
        &'vir self,
        ty: Type,
        rust_ty: &ty::TyKind,
    ) -> Option<Expr<'vir>> {
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
        elems.split_last().map(|(last, rest)| {
            rest.iter().rfold(*last, |acc, e| {
                self.mk_bin_op_expr(BinOpKind::And, *e, acc)
            })
        }).unwrap_or_else(|| self.mk_bool::<true>())
    }
    pub fn mk_disj<'vir>(&'vir self, elems: &[Expr<'vir>]) -> Expr<'vir> {
        elems.split_last().map(|(last, rest)| {
            rest.iter().rfold(*last, |acc, e| {
                self.mk_bin_op_expr(BinOpKind::Or, *e, acc)
            })
        }).unwrap_or_else(|| self.mk_bool::<false>())
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
