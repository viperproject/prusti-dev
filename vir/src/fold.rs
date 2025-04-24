use crate::{debug_info::DebugInfo, *};

pub trait ExprFolder<'vir, Curr, Next>: Sized {
    fn super_fold(&mut self, e: ExprGen<'vir, Curr, Next>) -> ExprGen<'vir, Curr, Next> {
        match e.kind {
            ExprKindGenData::Local(local) => self.fold_local(local),
            ExprKindGenData::Field(recv, field) => self.fold_field(recv, field),
            ExprKindGenData::Old(expr) => self.fold_old(expr),
            ExprKindGenData::Const(value) => self.fold_const(value, e.debug_info, e.span),
            ExprKindGenData::Result(ty) => self.fold_result(ty, e.debug_info, e.span),
            ExprKindGenData::AccField(AccFieldGenData { recv, field, perm }) => {
                self.fold_acc_field(recv, field, *perm)
            }
            ExprKindGenData::Unfolding(UnfoldingGenData { target, expr }) => {
                self.fold_unfolding(target, expr)
            }
            ExprKindGenData::UnOp(UnOpGenData { kind, expr }) => self.fold_unop(*kind, expr),
            ExprKindGenData::BinOp(BinOpGenData { kind, lhs, rhs }) => {
                self.fold_binop(*kind, lhs, rhs)
            }
            ExprKindGenData::Ternary(TernaryGenData { cond, then, else_ }) => {
                self.fold_ternary(cond, then, else_)
            }
            ExprKindGenData::Forall(ForallGenData {
                qvars,
                triggers,
                body,
            }) => self.fold_forall(qvars, triggers, body),
            ExprKindGenData::Let(LetGenData { name, val, expr }) => self.fold_let(name, val, expr),
            ExprKindGenData::FuncApp(FuncAppGenData {
                target,
                args,
                result_ty,
            }) => self.fold_func_app(target, args, *result_ty),
            ExprKindGenData::PredicateApp(PredicateAppGenData { target, args, perm }) => {
                self.fold_predicate_app(target, args, *perm)
            }
            ExprKindGenData::Lazy(lazy) => self.fold_lazy(lazy),
            ExprKindGenData::Todo(msg) => self.fold_todo(msg),
            ExprKindGenData::Exists(..) => todo!(),
            ExprKindGenData::Wand(..) => todo!(),
        }
    }

    fn fold(&mut self, e: ExprGen<'vir, Curr, Next>) -> ExprGen<'vir, Curr, Next> {
        self.super_fold(e)
    }

    fn fold_option(
        &mut self,
        e: Option<ExprGen<'vir, Curr, Next>>,
    ) -> Option<ExprGen<'vir, Curr, Next>> {
        e.map(|i| self.fold(i))
    }

    fn fold_slice(
        &mut self,
        s: &'vir [ExprGen<'vir, Curr, Next>],
    ) -> &'vir [ExprGen<'vir, Curr, Next>] {
        let vec = s.iter().map(|e| self.fold(e)).collect::<Vec<_>>();

        with_vcx(move |vcx| vcx.alloc_slice(&vec))
    }

    fn fold_slice_slice(
        &mut self,
        s: &'vir [TriggerGen<'vir, Curr, Next>],
    ) -> &'vir [TriggerGen<'vir, Curr, Next>] {
        with_vcx(move |vcx| {
            let vec = s
                .iter()
                .map(|e| vcx.mk_trigger(self.fold_slice(e.exprs)))
                .collect::<Vec<_>>();
            vcx.alloc_slice(&vec)
        })
    }

    fn fold_local(&mut self, local: Local<'vir>) -> ExprGen<'vir, Curr, Next> {
        with_vcx(move |vcx| vcx.mk_local_ex_local(local))
    }

    fn fold_field(
        &mut self,
        recv: ExprGen<'vir, Curr, Next>,
        field: Field<'vir>,
    ) -> ExprGen<'vir, Curr, Next> {
        let recv = self.fold(recv);
        with_vcx(move |vcx| vcx.mk_field_expr(recv, field))
    }

    fn fold_old(&mut self, expr: OldGen<'vir, Curr, Next>) -> ExprGen<'vir, Curr, Next> {
        let expr = self.fold(expr.expr);

        with_vcx(move |vcx| vcx.mk_old_expr(expr))
    }

    fn fold_const(
        &mut self,
        value: Const<'vir>,
        debug_info: DebugInfo<'vir>,
        span: Option<&'vir VirSpan<'vir>>,
    ) -> ExprGen<'vir, Curr, Next> {
        with_vcx(move |vcx| {
            vcx.alloc(ExprGenData {
                kind: vcx.alloc(ExprKindGenData::Const(value)),
                debug_info,
                span,
            })
        })
    }

    fn fold_result(
        &mut self,
        ty: Type<'vir>,
        debug_info: DebugInfo<'vir>,
        span: Option<&'vir VirSpan<'vir>>,
    ) -> ExprGen<'vir, Curr, Next> {
        with_vcx(move |vcx| {
            vcx.alloc(ExprGenData {
                kind: vcx.alloc(ExprKindGenData::Result(ty)),
                debug_info,
                span,
            })
        })
    }

    fn fold_acc_field(
        &mut self,
        recv: ExprGen<'vir, Curr, Next>,
        field: Field<'vir>,
        perm: Option<ExprGen<'vir, Curr, Next>>,
    ) -> ExprGen<'vir, Curr, Next> {
        let recv = self.fold(recv);
        let perm = self.fold_option(perm);

        with_vcx(move |vcx| vcx.mk_acc_field_expr(recv, field, perm))
    }

    fn fold_predicate_app(
        &mut self,
        target: &'vir str, // TODO: identifiers
        args: &'vir [ExprGen<'vir, Curr, Next>],
        perm: Option<ExprGen<'vir, Curr, Next>>,
    ) -> ExprGen<'vir, Curr, Next> {
        let args = self.fold_slice(args);
        let perm = self.fold_option(perm);

        with_vcx(move |vcx| {
            let pred_app = vcx.alloc(PredicateAppGenData { target, args, perm });

            vcx.mk_predicate_app_expr(pred_app)
        })
    }

    fn fold_unfolding(
        &mut self,
        pred: PredicateAppGen<'vir, Curr, Next>,
        expr: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        let expr = self.fold(expr);

        let args = self.fold_slice(pred.args);
        let perm = self.fold_option(pred.perm);

        with_vcx(move |vcx| {
            let target = vcx.alloc(PredicateAppGenData {
                target: pred.target,
                args,
                perm,
            });
            vcx.mk_unfolding_expr(target, expr)
        })
    }

    fn fold_unop(
        &mut self,
        kind: UnOpKind,
        expr: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        let expr = self.fold(expr);
        with_vcx(move |vcx| vcx.mk_unary_op_expr(kind, expr))
    }

    fn fold_binop(
        &mut self,
        kind: BinOpKind,
        lhs: ExprGen<'vir, Curr, Next>,
        rhs: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        let lhs = self.fold(lhs);
        let rhs = self.fold(rhs);

        with_vcx(move |vcx| vcx.mk_bin_op_expr(kind, lhs, rhs))
    }

    fn fold_ternary(
        &mut self,
        cond: ExprGen<'vir, Curr, Next>,
        then: ExprGen<'vir, Curr, Next>,
        else_: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        let cond = self.fold(cond);
        let then = self.fold(then);
        let else_ = self.fold(else_);

        with_vcx(move |vcx| vcx.mk_ternary_expr(cond, then, else_))
    }

    fn fold_forall(
        &mut self,
        qvars: &'vir [LocalDecl<'vir>],
        triggers: &'vir [TriggerGen<'vir, Curr, Next>],
        body: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        let triggers = self.fold_slice_slice(triggers);
        let body = self.fold(body);

        with_vcx(move |vcx| vcx.mk_forall_expr(qvars, triggers, body))
    }

    fn fold_let(
        &mut self,
        name: &'vir str,
        val: ExprGen<'vir, Curr, Next>,
        expr: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        let val = self.fold(val);
        let expr = self.fold(expr);

        with_vcx(move |vcx| vcx.mk_let_expr(name, val, expr))
    }

    fn fold_func_app(
        &mut self,
        target: &'vir str,
        src_args: &'vir [ExprGen<'vir, Curr, Next>],
        result_ty: Type<'vir>,
    ) -> ExprGen<'vir, Curr, Next> {
        let src_args = self.fold_slice(src_args);

        with_vcx(move |vcx| vcx.mk_func_app(target, src_args, result_ty))
    }

    fn fold_todo(&mut self, msg: &'vir str) -> ExprGen<'vir, Curr, Next> {
        with_vcx(move |vcx| vcx.mk_todo_expr(msg))
    }

    fn fold_lazy(&mut self, lazy: LazyGen<'vir, Curr, Next>) -> ExprGen<'vir, Curr, Next> {
        with_vcx(move |vcx| {
            vcx.mk_lazy_expr(
                lazy.name,
                lazy.ty,
                Box::new(move |ctx, c| {
                    let r = (lazy.func)(ctx, c);
                    // TODO
                    r
                }),
            )
        })
    }
}
