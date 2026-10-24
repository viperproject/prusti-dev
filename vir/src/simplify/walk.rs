//! The traversal: simplifies each expression tree bottom-up, keeping track
//! of the `let` bindings in scope, and hands each node, once its children
//! are simplified, to the [equations](super::equations).

use prusti_rustc_interface::data_structures::fx::{FxHashMap, FxHashSet};

use super::SimplifyCtx;
use crate::{
    collect_locals, gendata::*, refs::*, CastType, Foldable, Folder, VirCtxt, Visitable, Visitor,
};

type Ptr<'vir> = *const ExprGenData<'vir, (), !, crate::Dyn>;

/// A `let`-bound local in scope.
#[derive(Clone, Copy)]
pub(super) struct Binding<'vir> {
    pub(super) val: ExprDyn<'vir>,
    /// The locals `val` mentions.
    locals: &'vir [&'vir str],
    /// Whether `val` is a local or constant: it means the same in any state
    /// and costs nothing to copy.
    trivial: bool,
    /// How often the `let` body mentions the local.
    uses: usize,
}

pub(super) struct Simplifier<'a, 'vir, 'tcx> {
    pub(super) vcx: &'vir VirCtxt<'tcx>,
    pub(super) ctx: &'a SimplifyCtx<'vir>,
    /// The bindings whose values mean the same at the current node as at
    /// their `let`: a binder hides the bindings it rebinds or whose values
    /// mention a local it binds, and `old(..)` and `unfolding` hide those
    /// with a non-trivial value.
    pub(super) env: FxHashMap<&'vir str, Binding<'vir>>,
    /// The node being rewritten, whose span and debug information the nodes
    /// built for it take.
    pub(super) orig: Option<ExprDyn<'vir>>,
    /// Identifies the bindings in scope: a fresh number for every scope
    /// entered.
    scope: usize,
    scopes: usize,
    /// Memoized [`Self::simplify`], by node and scope: an expression shared
    /// in a tree is simplified once.
    simplified: FxHashMap<(Ptr<'vir>, usize), Option<ExprDyn<'vir>>>,
    /// Memoized [`Self::is_impure`].
    impure: FxHashMap<Ptr<'vir>, bool>,
}

/// Hands the roots of the expression trees of an item (contract clauses,
/// invariants, bodies, axioms and statement operands) to
/// [`Simplifier::root`].
pub(super) struct Roots<'s, 'a, 'vir, 'tcx>(pub &'s mut Simplifier<'a, 'vir, 'tcx>);

impl<'vir> Folder<'vir, (), !> for Roots<'_, '_, 'vir, '_> {
    fn fold_expr(&mut self, e: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        self.0.root(e)
    }

    fn fold_wand(&mut self, _: Wand<'vir>) -> Option<Wand<'vir>> {
        None
    }
}

/// Magic wands are left untouched, wherever they occur: Viper matches
/// packaged wand instances syntactically, and evaluates the heap-dependent
/// subterms of a wand only when applying it, in the order of its conjuncts,
/// so moving them around inside a wand changes which permissions are there.
impl<'vir> Folder<'vir, (), !> for Simplifier<'_, 'vir, '_> {
    fn fold_expr(&mut self, e: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        self.simplify(e)
    }

    fn fold_wand(&mut self, _: Wand<'vir>) -> Option<Wand<'vir>> {
        None
    }
}

impl<'a, 'vir, 'tcx> Simplifier<'a, 'vir, 'tcx> {
    pub(super) fn new(vcx: &'vir VirCtxt<'tcx>, ctx: &'a SimplifyCtx<'vir>) -> Self {
        Self {
            vcx,
            ctx,
            env: FxHashMap::default(),
            orig: None,
            scope: 0,
            scopes: 0,
            simplified: FxHashMap::default(),
            impure: FxHashMap::default(),
        }
    }

    /// Simplifies the root of an expression tree, keeping the root's span.
    /// Viper blames e.g. a failing postcondition on the clause's root node,
    /// and the error handler is registered on the span of that node only (see
    /// `realloc_span`); replacing the root by a subexpression would make the
    /// error impossible to backtranslate.
    pub(super) fn root(&mut self, e: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        let simplified = self.simplify(e)?;
        // A root without a span has no handler; keep the result's own.
        Some(match e.span {
            None => simplified,
            Some(_) => self.node_of_kind(e, simplified.kind),
        })
    }

    /// The simplified `e`, `None` if nothing about it changes.
    pub(super) fn simplify(&mut self, e: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        let key = (std::ptr::from_ref(e), self.scope);
        if let Some(&simplified) = self.simplified.get(&key) {
            return simplified;
        }
        let simplified = self.simplify_node(e);
        self.simplified.insert(key, simplified);
        simplified
    }

    /// The simplified `e`. A local bound to a trivial value, or used only
    /// once, is replaced by its value; the `let` is then dropped by the
    /// equations, unless a use the traversal does not substitute (in a
    /// trigger, a wand, or where the binding is hidden) remains.
    fn simplify_node(&mut self, e: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        let children = match e.kind {
            ExprKindGenData::Local(l) => {
                let b = self.env.get(l.name)?;
                return (b.trivial || b.uses == 1).then_some(b.val);
            }
            ExprKindGenData::Let(l) => {
                let new_val = self.simplify(l.val);
                let val = new_val.unwrap_or(l.val);
                let binding = Binding::new(self.vcx, val, l.name, l.expr);
                let mut body = self.with_binding(l.name, binding, |s| s.simplify(l.expr));
                // Folding may leave a single use of a local used more than
                // once before; a second pass substitutes it.
                if let Some(b) = body.filter(|b| binding.uses > 1 && occurrences(l.name, b) == 1) {
                    let binding = Binding::new(self.vcx, val, l.name, b);
                    body = self
                        .with_binding(l.name, binding, |s| s.simplify(b))
                        .or(body);
                }
                (new_val.is_some() || body.is_some()).then(|| {
                    let expr = body.unwrap_or(l.expr);
                    let l = LetGenData {
                        name: l.name,
                        val,
                        expr,
                    };
                    self.node_at(e, ExprKindGenData::Let(self.vcx.alloc(l)))
                })
            }
            // `old(..)` evaluates in another heap and the body of `unfolding`
            // with other permissions, so only trivial values move into them.
            ExprKindGenData::Old(_) => self.scoped(|_, b| b.trivial, |s| e.super_fold_with(s)),
            ExprKindGenData::Unfolding(u) => {
                let target = u.target.fold_with(self);
                let body = self.scoped(|_, b| b.trivial, |s| s.simplify(u.expr));
                (target.is_some() || body.is_some()).then(|| {
                    let u = UnfoldingGenData {
                        target: target.unwrap_or(u.target),
                        expr: body.unwrap_or(u.expr),
                    };
                    self.node_at(e, ExprKindGenData::Unfolding(self.vcx.alloc(u)))
                })
            }
            // The triggers are left as encoded.
            ExprKindGenData::Forall(ForallGenData {
                qvars,
                triggers,
                body,
            })
            | ExprKindGenData::Exists(ExistsGenData {
                qvars,
                triggers,
                body,
            }) => self
                .in_quantifier(qvars, |s| s.simplify(body.as_dyn()))
                .map(|body| {
                    let (qvars, triggers, body) = (*qvars, *triggers, body.inner_cast_ty());
                    let kind = match e.kind {
                        ExprKindGenData::Forall(_) => {
                            let q = ForallGenData {
                                qvars,
                                triggers,
                                body,
                            };
                            ExprKindGenData::Forall(self.vcx.alloc(q))
                        }
                        _ => {
                            let q = ExistsGenData {
                                qvars,
                                triggers,
                                body,
                            };
                            ExprKindGenData::Exists(self.vcx.alloc(q))
                        }
                    };
                    self.node_at(e, kind)
                }),
            _ => e.super_fold_with(self),
        };
        let node = children.unwrap_or(e);
        let outer = self.orig.replace(node);
        let folded = self.fold(node);
        self.orig = outer;
        folded.or(children)
    }

    /// Runs `f` in the body of a `let` binding `local`. A value that mentions
    /// the local it is bound to means the outer local, which the body cannot
    /// see, so such a binding is not entered.
    pub(super) fn with_binding<R>(
        &mut self,
        local: &'vir str,
        binding: Binding<'vir>,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.scoped(
            |name, b| name != local && !b.mentions(local),
            |s| {
                if !binding.mentions(local) {
                    s.env.insert(local, binding);
                }
                f(s)
            },
        )
    }

    /// Runs `f` in the body of a quantifier over `qvars`.
    fn in_quantifier<R>(
        &mut self,
        qvars: &[LocalDeclDyn<'vir>],
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        self.scoped(
            |name, b| qvars.iter().all(|q| q.name != name && !b.mentions(q.name)),
            f,
        )
    }

    /// Runs `f` with only the bindings that `visible` keeps in scope.
    fn scoped<R>(
        &mut self,
        visible: impl Fn(&str, &Binding<'vir>) -> bool,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let saved = self.env.clone();
        self.env.retain(|name, b| visible(name, b));
        self.scopes += 1;
        let outer = std::mem::replace(&mut self.scope, self.scopes);
        let result = f(self);
        self.scope = outer;
        self.env = saved;
        result
    }

    /// A node of kind `kind` with the span and debug information of `e`.
    pub(super) fn node_at(
        &self,
        e: ExprDyn<'vir>,
        kind: ExprKindGenData<'vir, (), !>,
    ) -> ExprDyn<'vir> {
        self.node_of_kind(e, self.vcx.alloc(kind))
    }

    /// A node of the allocated kind `kind` with the span and debug
    /// information of `e`.
    pub(super) fn node_of_kind(
        &self,
        e: ExprDyn<'vir>,
        kind: &'vir ExprKindGenData<'vir, (), !>,
    ) -> ExprDyn<'vir> {
        self.vcx.alloc(ExprGenData::new_inner(
            kind,
            e.debug_info,
            e.span,
            kind.ty(),
        ))
    }

    /// Whether `e` contains an assertion (an access predicate, magic wand or
    /// inhale-exhale expression).
    pub(super) fn is_impure(&mut self, e: ExprDyn<'vir>) -> bool {
        if let Some(&impure) = self.impure.get(&std::ptr::from_ref(e)) {
            return impure;
        }
        let impure = match e.kind {
            ExprKindGenData::AccField(_)
            | ExprKindGenData::PredicateApp(_)
            | ExprKindGenData::Wand(_)
            | ExprKindGenData::InhaleExhale(_) => true,
            _ => {
                let mut children = Children(Vec::new());
                e.super_visit_with(&mut children);
                children.0.into_iter().any(|child| self.is_impure(child))
            }
        };
        self.impure.insert(std::ptr::from_ref(e), impure);
        impure
    }
}

impl<'vir> Binding<'vir> {
    /// The binding of `name` to `val` in `body`.
    pub(super) fn new(
        vcx: &'vir VirCtxt<'_>,
        val: ExprDyn<'vir>,
        name: &str,
        body: ExprDyn<'vir>,
    ) -> Self {
        let mut locals = FxHashSet::default();
        collect_locals(val, &mut locals);
        Self {
            val,
            locals: vcx.alloc_slice(&locals.into_iter().collect::<Vec<_>>()),
            trivial: matches!(
                val.kind,
                ExprKindGenData::Local(_) | ExprKindGenData::Const(_)
            ),
            uses: occurrences(name, body),
        }
    }

    fn mentions(&self, name: &str) -> bool {
        self.locals.contains(&name)
    }
}

/// How often `e` mentions the local `name`, also where it is rebound.
pub(super) fn occurrences(name: &str, e: ExprDyn<'_>) -> usize {
    struct Count<'n>(&'n str, usize);
    impl<'vir> Visitor<'vir, (), !> for Count<'_> {
        fn visit_expr(&mut self, e: ExprDyn<'vir>) {
            if matches!(e.kind, ExprKindGenData::Local(l) if l.name == self.0) {
                self.1 += 1;
            }
            e.super_visit_with(self);
        }
    }
    let mut count = Count(name, 0);
    e.visit_with(&mut count);
    count.1
}

/// Collects the direct subexpressions of an expression.
struct Children<'vir>(Vec<ExprDyn<'vir>>);

impl<'vir> Visitor<'vir, (), !> for Children<'vir> {
    fn visit_expr(&mut self, e: ExprDyn<'vir>) {
        self.0.push(e);
    }
}
