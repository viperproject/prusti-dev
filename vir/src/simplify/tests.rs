//! Expressions and the Viper syntax they simplify to, by equation.

use prusti_rustc_interface::span::DUMMY_SP;

use super::{walk::Simplifier, LiteralInverse, SimplifyCtx};
use crate::{
    data::*, gendata::*, refs::*, BinOpKind::*, CastType, Dyn, TypeData, TypeKind, VirCtxt,
    TYPE_BOOL, TYPE_INT, TYPE_REF,
};

/// Builds expressions over `Bool` and `Int` locals and the adt
/// `P = P_cons(f0: Int, f1: Int)`.
struct Builder<'vir, 'tcx> {
    vcx: &'vir VirCtxt<'tcx>,
    p_ty: TypeDyn<'vir>,
}

impl<'vir> Builder<'vir, '_> {
    fn node(&self, kind: ExprKindGenData<'vir, (), !>) -> ExprDyn<'vir> {
        self.vcx
            .alloc(ExprGenData::<_, _, Dyn>::new(self.vcx.alloc(kind)))
    }
    fn local(&self, name: &'vir str, ty: TypeDyn<'vir>) -> ExprDyn<'vir> {
        self.vcx.mk_local_ex(self.vcx.mk_local_decl(name, ty))
    }
    fn b(&self, name: &'vir str) -> ExprDyn<'vir> {
        self.local(name, TYPE_BOOL.as_dyn())
    }
    fn i(&self, name: &'vir str) -> ExprDyn<'vir> {
        self.local(name, TYPE_INT.as_dyn())
    }
    fn int(&self, v: u128) -> ExprDyn<'vir> {
        self.vcx.mk_const_expr(ConstData::Int(v)).as_dyn()
    }
    fn tt(&self) -> ExprDyn<'vir> {
        self.vcx.mk_bool::<true>().as_dyn()
    }
    fn ff(&self) -> ExprDyn<'vir> {
        self.vcx.mk_bool::<false>().as_dyn()
    }
    fn not(&self, e: ExprDyn<'vir>) -> ExprDyn<'vir> {
        self.node(ExprKindGenData::UnOp(self.vcx.alloc(UnOpGenData {
            kind: UnOpKind::Not,
            expr: e.inner_cast_ty(),
        })))
    }
    fn bin(&self, kind: BinOpKind, lhs: ExprDyn<'vir>, rhs: ExprDyn<'vir>) -> ExprDyn<'vir> {
        self.node(ExprKindGenData::BinOp(self.vcx.alloc(BinOpGenData {
            kind,
            lhs,
            rhs,
        })))
    }
    fn ite(&self, c: ExprDyn<'vir>, a: ExprDyn<'vir>, b: ExprDyn<'vir>) -> ExprDyn<'vir> {
        self.node(ExprKindGenData::Ternary(self.vcx.alloc(TernaryGenData {
            cond: c.inner_cast_ty(),
            then: a,
            else_: b,
        })))
    }
    fn let_(&self, name: &'vir str, val: ExprDyn<'vir>, body: ExprDyn<'vir>) -> ExprDyn<'vir> {
        self.node(ExprKindGenData::Let(self.vcx.alloc(LetGenData {
            name,
            val,
            expr: body,
        })))
    }
    /// `forall q: Int :: {triggers} body`.
    fn forall(
        &self,
        q: &'vir str,
        triggers: &[ExprDyn<'vir>],
        body: ExprDyn<'vir>,
    ) -> ExprDyn<'vir> {
        let qvars = self.vcx.alloc_slice(&[self.vcx.mk_local_decl(q, TYPE_INT)]);
        let triggers = if triggers.is_empty() {
            &[]
        } else {
            self.vcx.alloc_slice(&[self.vcx.mk_trigger(triggers)])
        };
        self.vcx
            .mk_forall_expr::<(), !, _>(qvars, triggers, body.inner_cast_ty())
            .as_dyn()
    }
    fn old(&self, e: ExprDyn<'vir>) -> ExprDyn<'vir> {
        self.vcx.mk_old_expr(e).as_dyn()
    }
    fn p(&self, args: &[ExprDyn<'vir>]) -> ExprDyn<'vir> {
        self.vcx
            .mk_func_app("P_cons", self.vcx.alloc_slice(args), self.p_ty, &[])
    }
    fn field(&self, recv: ExprDyn<'vir>, name: &'vir str) -> ExprDyn<'vir> {
        let destr = self.vcx.mk_adt_destructor(name, self.p_ty, TYPE_INT);
        self.vcx.mk_adt_destructor_expr(recv, destr).as_dyn()
    }
    /// The `Int` application `name(args..)`.
    fn app(&self, name: &'vir str, args: &[ExprDyn<'vir>]) -> ExprDyn<'vir> {
        self.vcx
            .mk_func_app(name, self.vcx.alloc_slice(args), TYPE_INT, &[])
            .as_dyn()
    }
    /// `acc(r.f)` for a `Ref` local `r`.
    fn acc(&self, r: &'vir str) -> ExprDyn<'vir> {
        let recv = self.vcx.mk_local_ex(self.vcx.mk_local_decl(r, TYPE_REF));
        let field = self.vcx.mk_field("f", TYPE_INT);
        self.vcx.mk_acc_field_expr(recv, field, None).as_dyn()
    }
}

/// Runs `f` with a fresh context and a [`SimplifyCtx`] for a program with
/// the adt `P`, a function `h` without and a function `g` with a
/// precondition, and the literal inverse `value`/`cons` on the bytes without
/// `10..=19`.
fn with_ctx(f: impl for<'vir> FnOnce(&SimplifyCtx<'vir>, &Builder<'vir, 'vir>)) {
    crate::init_vcx(VirCtxt::new_without_tcx());
    crate::with_vcx(|vcx| {
        let fields = vcx.alloc_slice(&[
            vcx.mk_local_decl("f0", TYPE_INT),
            vcx.mk_local_decl("f1", TYPE_INT),
        ]);
        let cons = vcx.mk_adt_constructor::<(), !, _>("P_cons", fields);
        let adt = vcx.mk_adt(crate::ViperIdent::new("P"), &[], vcx.alloc_slice(&[cons]));
        let function = |name, pres| -> Function<'_> {
            vcx.alloc(FunctionGenData {
                name,
                args: &[],
                ret: TYPE_INT.as_dyn(),
                pres,
                posts: &[],
                decreases: vcx.alloc(DecreasesGenData::None),
                expr: None,
            })
        };
        let functions = [
            function("h", &[]),
            function("g", vcx.alloc_slice(&[vcx.mk_bool::<true>()])),
        ];
        let byte = LiteralInverse {
            outer: crate::ViperIdent::new("value"),
            inner: crate::ViperIdent::new("cons"),
            ranges: vcx.alloc_slice(&[
                (vcx.mk_uint::<0>(), vcx.mk_uint::<9>()),
                (vcx.mk_uint::<20>(), vcx.mk_uint::<255>()),
            ]),
        };
        let ctx = SimplifyCtx::new(&[adt], &[], &functions, &[byte]);
        let p_ty = vcx.alloc(TypeData::<Dyn>::new(TypeKind::Domain("P", &[])));
        f(&ctx, &Builder { vcx, p_ty });
    });
}

/// Checks the Viper syntax of the simplified expression `build` makes.
fn check_with(
    build: impl for<'vir> FnOnce(&Builder<'vir, 'vir>) -> ExprDyn<'vir>,
    check: impl FnOnce(&str),
) {
    with_ctx(|ctx, c| {
        let e = build(c);
        let simplified = Simplifier::new(c.vcx, ctx).simplify(e).unwrap_or(e);
        check(&format!("{simplified:?}"));
    });
}

fn check(expected: &str, build: impl for<'vir> FnOnce(&Builder<'vir, 'vir>) -> ExprDyn<'vir>) {
    check_with(build, |actual| assert_eq!(actual, expected));
}

/// Checks that the simplified expression starts with `prefix`.
fn check_prefix(prefix: &str, build: impl for<'vir> FnOnce(&Builder<'vir, 'vir>) -> ExprDyn<'vir>) {
    check_with(build, |actual| {
        assert!(actual.starts_with(prefix), "{actual}")
    });
}

#[test]
fn not() {
    check("false", |c| c.not(c.tt()));
    check("b", |c| c.not(c.not(c.b("b"))));
    check("(x) >= (y)", |c| c.not(c.bin(CmpLt, c.i("x"), c.i("y"))));
}

#[test]
fn bin_op() {
    check("b", |c| c.bin(And, c.tt(), c.b("b")));
    check("false", |c| c.bin(And, c.b("b"), c.ff()));
    check("b", |c| c.bin(Or, c.b("b"), c.ff()));
    check("true", |c| c.bin(Or, c.b("b"), c.tt()));
    check("b", |c| c.bin(Implies, c.tt(), c.b("b")));
    check("true", |c| c.bin(Implies, c.ff(), c.b("b")));
    check("!(b)", |c| c.bin(CmpEq, c.b("b"), c.ff()));
    check("b", |c| c.bin(CmpNe, c.ff(), c.b("b")));
    check("false", |c| c.bin(CmpEq, c.tt(), c.ff()));
    check("((x) == (z)) && ((y) == (w))", |c| {
        c.bin(
            CmpEq,
            c.p(&[c.i("x"), c.i("y")]),
            c.p(&[c.i("z"), c.i("w")]),
        )
    });
}

#[test]
fn ternary() {
    check("x", |c| c.ite(c.b("c"), c.i("x"), c.i("x")));
    check("(c) || (b)", |c| c.ite(c.b("c"), c.tt(), c.b("b")));
    check("(!(c)) && (b)", |c| c.ite(c.b("c"), c.ff(), c.b("b")));
    check("(c) ==> (b)", |c| c.ite(c.b("c"), c.b("b"), c.tt()));
    check("c", |c| c.ite(c.b("c"), c.tt(), c.ff()));
    // Adt constructors and functions without preconditions move out of a
    // ternary, a function with a precondition stays inside.
    check_prefix("P_cons(x, c\n", |c| {
        let then = c.p(&[c.i("x"), c.i("y")]);
        c.ite(c.b("c"), then, c.p(&[c.i("x"), c.i("z")]))
    });
    check_prefix("h(c\n", |c| {
        c.ite(c.b("c"), c.app("h", &[c.i("x")]), c.app("h", &[c.i("y")]))
    });
    check_prefix("c\n? g(x)", |c| {
        c.ite(c.b("c"), c.app("g", &[c.i("x")]), c.app("g", &[c.i("y")]))
    });
}

#[test]
fn field() {
    check("x", |c| c.field(c.p(&[c.i("x"), c.i("y")]), "f0"));
    check("c\n? x\n: r.f0", |c| {
        let recv = c.ite(c.b("c"), c.p(&[c.i("x"), c.i("y")]), c.local("r", c.p_ty));
        c.field(recv, "f0")
    });
    // Through a local bound to a constructor application, and into a `let`.
    check("(y) == (x)", |c| {
        let q = c.local("q", c.p_ty);
        c.let_(
            "q",
            c.p(&[c.i("x"), c.i("y")]),
            c.bin(CmpEq, c.field(q, "f1"), c.field(q, "f0")),
        )
    });
    check("(x) + (1)", |c| {
        let a = c.i("a");
        c.field(
            c.let_("a", c.bin(Add, c.i("x"), c.int(1)), c.p(&[a, a])),
            "f0",
        )
    });
}

#[test]
fn app() {
    check("q", |c| {
        let q = c.local("q", c.p_ty);
        c.p(&[c.field(q, "f0"), c.field(q, "f1")])
    });
    check("7", |c| c.app("value", &[c.app("cons", &[c.int(7)])]));
    check("20", |c| c.app("value", &[c.app("cons", &[c.int(20)])]));
    check("value(cons(15))", |c| {
        c.app("value", &[c.app("cons", &[c.int(15)])])
    });
}

#[test]
fn quantifier() {
    check("true", |c| {
        c.forall("q", &[], c.bin(Implies, c.ff(), c.b("b")))
    });
    check("true", |c| c.forall("q", &[], c.tt()));
}

#[test]
fn i128_min_literal() {
    with_ctx(|_, c| {
        let min = c.node(ExprKindGenData::UnOp(c.vcx.alloc(UnOpGenData {
            kind: UnOpKind::Neg,
            expr: c.int(1 << 127).inner_cast_ty(),
        })));
        assert_eq!(super::equations::as_int(min), Some(i128::MIN));
    });
}

#[test]
fn let_() {
    check("y", |c| c.let_("a", c.i("x"), c.i("y")));
    check("((x) + (1)) == (y)", |c| {
        c.let_(
            "a",
            c.bin(Add, c.i("x"), c.int(1)),
            c.bin(CmpEq, c.i("a"), c.i("y")),
        )
    });
    // A value whose other uses fold away is inlined at the remaining one.
    check("(y) == ((x) + (1))", |c| {
        let a = c.i("a");
        let body = c.bin(CmpEq, c.field(c.p(&[c.i("y"), a]), "f0"), a);
        c.let_("a", c.bin(Add, c.i("x"), c.int(1)), body)
    });
    // Likewise when a field read moved into the `let` folds the other uses.
    check("c\n? h((x) + (1))\n: r.f0", |c| {
        let a = c.i("a");
        let val = c.bin(Add, c.i("x"), c.int(1));
        let l = c.let_("a", val, c.p(&[c.app("h", &[a]), a]));
        c.field(c.ite(c.b("c"), l, c.local("r", c.p_ty)), "f0")
    });
    // A trivial value is inlined into every use, and the uses then fold.
    check("b", |c| {
        let body = c.bin(And, c.b("a"), c.bin(Or, c.b("b"), c.not(c.b("a"))));
        c.let_("a", c.tt(), body)
    });
}

#[test]
fn let_scopes() {
    // A value mentioning its own local means the outer one.
    check_with(
        |c| {
            let val = c.bin(Add, c.i("a"), c.int(1));
            c.let_("a", val, c.bin(CmpEq, c.i("a"), c.i("y")))
        },
        |actual| assert!(actual.ends_with("(a) == (y))"), "{actual}"),
    );
    check_prefix("(let b ==", |c| {
        let trigger = c.app("f", &[c.i("b")]);
        let body = c.bin(CmpEq, c.app("f", &[c.i("q")]), c.i("b"));
        c.let_("b", c.i("b"), c.forall("q", &[trigger], body))
    });
    // A heap-dependent value cannot move into `old`.
    check_prefix("(let a ==", |c| {
        let val = c.bin(Add, c.i("x"), c.int(1));
        c.let_("a", val, c.bin(CmpEq, c.old(c.i("a")), c.i("y")))
    });
    // Nor into the body of `unfolding`, where other permissions are held;
    // its predicate arguments are evaluated outside.
    check_prefix("(let a ==", |c| {
        let val = c.bin(Add, c.i("x"), c.int(1));
        let target = c.vcx.alloc(PredicateAppGenData {
            target: "P",
            args: c.vcx.alloc_slice(&[c.local("r", TYPE_REF.as_dyn())]),
            perm: None,
        });
        let body = c.bin(CmpEq, c.i("a"), c.i("y"));
        c.let_("a", val, c.vcx.mk_unfolding_expr(target, body))
    });
    check_with(
        |c| {
            let val = c.bin(Add, c.i("x"), c.int(1));
            let target = c.vcx.alloc(PredicateAppGenData {
                target: "P",
                args: c.vcx.alloc_slice(&[c.i("a")]),
                perm: None,
            });
            let body = c.bin(CmpEq, c.i("z"), c.i("y"));
            c.let_("a", val, c.vcx.mk_unfolding_expr(target, body))
        },
        |actual| assert!(actual.starts_with("unfolding P((x) + (1))"), "{actual}"),
    );
    // Nor can a value move under a binder of one of its locals.
    check_prefix("(let a ==", |c| {
        let body = c.bin(CmpEq, c.i("a"), c.i("q"));
        c.let_("a", c.i("q"), c.forall("q", &[], body))
    });
    check_with(
        |c| {
            let read = c.field(c.local("a", c.p_ty), "f0");
            let body = c.let_("x", c.int(5), c.bin(CmpEq, read, c.i("x")));
            c.let_("a", c.p(&[c.i("x"), c.i("y")]), body)
        },
        |actual| assert!(actual.contains("a.f0"), "{actual}"),
    );
    // Uses in triggers and wands stay as encoded.
    check_prefix("(let a ==", |c| {
        let trigger = c.app("f", &[c.i("a")]);
        let body = c.bin(CmpEq, c.app("f", &[c.i("q")]), c.i("q"));
        c.let_("a", c.i("x"), c.forall("q", &[trigger], body))
    });
    check_prefix("(let a ==", |c| {
        let lhs = c.bin(CmpEq, c.i("a"), c.i("y"));
        let wand = c.vcx.mk_wand(lhs.inner_cast_ty(), c.vcx.mk_bool::<true>());
        c.let_("a", c.i("x"), c.vcx.mk_wand_expr(wand).as_dyn())
    });
}

#[test]
fn assertions() {
    // `c || acc(r.f)` would not be a valid assertion; the pure branch is
    // still simplified.
    check_prefix("c\n? true\n: acc(", |c| {
        c.ite(c.b("c"), c.not(c.not(c.tt())), c.acc("r"))
    });
    // A `let` around an assertion is dropped once its use is inlined.
    check_with(
        |c| {
            let eq = c.bin(CmpEq, c.i("a"), c.i("y"));
            let val = c.bin(Add, c.i("x"), c.int(1));
            c.let_("a", val, c.bin(And, c.acc("r"), eq))
        },
        |actual| {
            assert!(!actual.starts_with("(let"), "{actual}");
            assert!(actual.contains("((x) + (1)) == (y)"), "{actual}");
        },
    );
}

#[test]
fn shared_subexpressions() {
    // Each level reads both fields of the shared level below, which is only
    // linear with shared subexpressions simplified once.
    check("q", |c| {
        let mut e = c.local("q", c.p_ty);
        for _ in 0..40 {
            e = c.p(&[c.field(e, "f0"), c.field(e, "f1")]);
        }
        e
    });
}

#[test]
fn roots_keep_their_span() {
    with_ctx(|ctx, c| {
        let mut s = Simplifier::new(c.vcx, ctx);
        // `true && x` is `x`, but keeps the span of the root.
        let root = c.vcx.with_span(DUMMY_SP, |_| c.bin(And, c.tt(), c.b("x")));
        let simplified = s.root(root).unwrap();
        assert!(matches!(simplified.kind, ExprKindGenData::Local(l) if l.name == "x"));
        assert!(std::ptr::eq(simplified.span.unwrap(), root.span.unwrap()));
        // A root without a span keeps the result's own.
        let y = c.vcx.with_span(DUMMY_SP, |_| c.b("y"));
        let simplified = s.root(c.bin(And, c.tt(), y)).unwrap();
        assert!(std::ptr::eq(simplified.span.unwrap(), y.span.unwrap()));
    });
}

#[test]
fn unchanged_expressions_are_not_reallocated() {
    with_ctx(|ctx, c| {
        let e = c.bin(CmpEq, c.i("x"), c.i("y"));
        assert!(Simplifier::new(c.vcx, ctx).simplify(e).is_none());
    });
}
