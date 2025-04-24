use std::collections::HashMap;

use crate::*;

pub trait Optimizable: Sized {
    fn optimize(&self) -> Self;
}

impl<'vir, T> Optimizable for Option<&'vir T>
where
    T: Optimizable,
{
    fn optimize(&self) -> Self {
        self.map(|inner| {
            let o = inner.optimize();
            with_vcx(move |vcx| vcx.alloc(o))
        })
    }
}

impl<'vir, T> Optimizable for &'vir [&T]
where
    T: Optimizable,
{
    fn optimize(&self) -> Self {
        let v = self
            .iter()
            .map(|e| {
                let e = e.optimize();
                with_vcx(|vcx| vcx.alloc(e))
            })
            .collect::<Vec<_>>();
        with_vcx(move |vcx| vcx.alloc_slice(&v))
    }
}

impl<'vir, Curr, Next> Optimizable for &'vir ExprGenData<'vir, Curr, Next> {
    fn optimize(&self) -> Self {
        let r = *self;
        let s1 = (VariableOptimizerFolder {
            rename: Default::default(),
        })
        .fold(r);

        let s2 = EveryThingInliner::new().fold(s1);
        BoolOptimizerFolder.fold(s2)
    }
}

struct BoolOptimizerFolder;

impl<'vir, Cur, Next> ExprFolder<'vir, Cur, Next> for BoolOptimizerFolder {
    // transforms `a == true` into `a` and `a == false` into `!a`
    fn fold_binop(
        &mut self,
        kind: BinOpKind,
        lhs: ExprGen<'vir, Cur, Next>,
        rhs: ExprGen<'vir, Cur, Next>,
    ) -> ExprGen<'vir, Cur, Next> {
        let lhs = self.fold(lhs);
        let rhs = self.fold(rhs);

        if let BinOpKind::CmpEq = kind {
            if let ExprKindGenData::Const(ConstData::Bool(b)) = rhs.kind {
                return if *b {
                    // case lhs == true
                    lhs
                } else {
                    // case lhs == false
                    with_vcx(move |vcx| vcx.mk_unary_op_expr(UnOpKind::Not, lhs))
                };
            }
        }

        with_vcx(move |vcx| vcx.mk_bin_op_expr(kind, lhs, rhs))
    }

    // Transforms `c? true : false` into `c`
    fn fold_ternary(
        &mut self,
        cond: ExprGen<'vir, Cur, Next>,
        then: ExprGen<'vir, Cur, Next>,
        else_: ExprGen<'vir, Cur, Next>,
    ) -> ExprGen<'vir, Cur, Next> {
        let cond = self.fold(cond);
        let then = self.fold(then);
        let else_ = self.fold(else_);

        if let (
            ExprKindGenData::Const(ConstData::Bool(true)),
            ExprKindGenData::Const(ConstData::Bool(false)),
        ) = (then.kind, else_.kind)
        {
            return cond;
        }

        with_vcx(move |vcx| vcx.mk_ternary_expr(cond, then, else_))
    }
}

pub(crate) struct EveryThingInliner<'vir, Cur, Next> {
    rename: HashMap<&'vir str, ExprGen<'vir, Cur, Next>>,
}

impl<'vir, Cur, Next> EveryThingInliner<'vir, Cur, Next> {
    fn new() -> Self {
        Self {
            rename: HashMap::new(),
        }
    }
}

impl<'vir, Cur, Next> ExprFolder<'vir, Cur, Next> for EveryThingInliner<'vir, Cur, Next> {
    fn fold_let(
        &mut self,
        name: &'vir str,
        val: ExprGen<'vir, Cur, Next>,
        expr: ExprGen<'vir, Cur, Next>,
    ) -> ExprGen<'vir, Cur, Next> {
        let val = self.fold(val);

        self.rename.insert(name, val);

        let expr = self.fold(expr);

        expr
    }

    fn fold_local(&mut self, local: Local<'vir>) -> ExprGen<'vir, Cur, Next> {
        let lcl = with_vcx(move |vcx| vcx.mk_local_ex_local(local));

        self.rename.get(local.name).map(|e| *e).unwrap_or(lcl)
    }

    // Transforms `C ? f(a) : f(b)` into `f(C? a : b)`
    fn fold_ternary(
        &mut self,
        cond: ExprGen<'vir, Cur, Next>,
        then: ExprGen<'vir, Cur, Next>,
        else_: ExprGen<'vir, Cur, Next>,
    ) -> ExprGen<'vir, Cur, Next> {
        let cond = self.fold(cond);
        let then = self.fold(then);
        let else_ = self.fold(else_);

        if let (ExprKindGenData::FuncApp(then_app), ExprKindGenData::FuncApp(else_app)) =
            (then.kind, else_.kind)
        {
            if then_app.args.len() == 1
                && else_app.args.len() == 1
                && else_app.target == then_app.target
                && else_app.result_ty == then_app.result_ty
            {
                return with_vcx(move |vcx| {
                    vcx.mk_func_app(
                        then_app.target,
                        &[vcx.mk_ternary_expr(cond, then_app.args[0], else_app.args[0])],
                        then_app.result_ty,
                    )
                });
            }
        }

        with_vcx(move |vcx| vcx.mk_ternary_expr(cond, then, else_))
    }

    // transforms `foo_read_x(foo_cons(a_1, ... a_n))` into a_x
    fn fold_func_app(
        &mut self,
        target: &'vir str,
        src_args: &'vir [ExprGen<'vir, Cur, Next>],
        result_ty: Type<'vir>,
    ) -> ExprGen<'vir, Cur, Next> {
        let src_args = self.fold_slice(src_args);
        let default = || with_vcx(move |vcx| vcx.mk_func_app(target, src_args, result_ty));

        // Hacky way to do read of cons:
        if src_args.len() != 1 {
            return default();
        }
        let ExprKindGenData::FuncApp(inner) = src_args[0].kind else {
            return default();
        };
        if target.strip_prefix("make_generic_s_").is_some_and(|other| inner.target.strip_prefix("make_concrete_s_") == Some(other)) {
            assert_eq!(inner.args.len(), 1);
            return inner.args[0];
        }
        if target.strip_prefix("make_concrete_s_").is_some_and(|other| inner.target.strip_prefix("make_generic_s_") == Some(other)) {
            assert_eq!(inner.args.len(), 1);
            return inner.args[0];
        }

        if target == "s_Ref_immutable_value" && inner.target == "s_Ref_immutable_cons" {
            assert_eq!(inner.args.len(), 2);
            return inner.args[1];
        }
        let strip_both = |s: &'vir str, pre, post| {
            s.strip_prefix(pre)
                .and_then(move |s| s.strip_suffix(post))
        };
        if strip_both(target, "s_", "_value").is_some_and(|middle|
            strip_both(inner.target, "s_", "_cons") == Some(middle)) {
            assert_eq!(inner.args.len(), 1);
            return inner.args[0];
        }

        // let Some((outer_lhs, read_nr)) = target.rsplit_once("_") else {
        //     return default();
        // };
        // let Some((start, "cons")) = inner.target.rsplit_once("_") else {
        //     return default();
        // };
        // if target.ends_with(&format!("read_{}", read_nr))
        //     && target.starts_with(start)
        // {
        //     if let Ok(read_nr) = read_nr.parse::<usize>() {
        //         return innerfuncapp.args[read_nr];
        //     } else {
        //         println!("ERROR: Not a number: {} {}", innerfuncapp.target, target);
        //     }
        // }
        default()
    }
}

pub(crate) struct VariableOptimizerFolder<'vir> {
    rename: HashMap<String, &'vir str>,
}

impl<'vir, Cur, Next> ExprFolder<'vir, Cur, Next> for VariableOptimizerFolder<'vir> {
    fn fold_local(&mut self, local: Local<'vir>) -> ExprGen<'vir, Cur, Next> {
        let nam = self
            .rename
            .get(local.name)
            .map(|e| *e)
            .unwrap_or(local.name);
        with_vcx(move |vcx| vcx.mk_local_ex(&nam, local.ty))
    }

    fn fold_old(&mut self, expr: &'vir OldGenData<'vir, Cur, Next>) -> ExprGen<'vir, Cur, Next> {
        expr.expr
    }

    fn fold_let(
        &mut self,
        name: &'vir str,
        val: ExprGen<'vir, Cur, Next>,
        expr: ExprGen<'vir, Cur, Next>,
    ) -> ExprGen<'vir, Cur, Next> {
        let val = self.fold(val);

        match val.kind {
            // let name = loc.name
            ExprKindGenData::Local(loc) => {
                let t = self
                    .rename
                    .get(loc.name)
                    .map(|e| e.to_owned())
                    .unwrap_or(loc.name);
                assert!(self.rename.insert(name.to_string(), t).is_none());
                return self.fold(expr);
            }
            _ => {}
        }

        let expr = self.fold(expr);

        if let ExprKindGenData::Local(inner_local) = expr.kind {
            if inner_local.name == name {
                // if we encounter the case `let X = val in X` then just return `val`
                return val;
            }
        }
        with_vcx(move |vcx| vcx.mk_let_expr(name, val, expr))
    }
}
