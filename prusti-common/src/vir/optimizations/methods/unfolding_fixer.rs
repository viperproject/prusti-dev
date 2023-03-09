use crate::vir::polymorphic_vir as vir;
use log::debug;
use rustc_hash::FxHasher;
use std::{
    hash::{Hash, Hasher},
    mem,
};

/// Looks for nested `unfolding (A) in B` Viper statements for which `A` is identical
/// and then replaces the most inner `unfolding (A) in B` by `B` (otherwise, Viper
/// will complain about unfolding the same predicate more than once).
///
/// Note: this can fix permission problems when the `optimize_folding` optimization is disabled.
pub fn fix_unfoldings(cfg: vir::CfgMethod) -> vir::CfgMethod {
    let mut optimizer = Optimizer::new();
    optimizer.replace_cfg(cfg)
}

/// Hashes only the fields that are needed for testing equality of nested `unfolding`s.
fn hash_unfolding(unfolding: &vir::Unfolding) -> u64 {
    let mut hasher = FxHasher::default();
    unfolding.predicate.hash(&mut hasher);
    unfolding.arguments.hash(&mut hasher);
    unfolding.permission.hash(&mut hasher);
    hasher.finish()
}

struct Optimizer {
    counter: u32,
    stack: Vec<u64>,
}

impl Optimizer {
    fn new() -> Self {
        Self {
            counter: 0,
            stack: vec![],
        }
    }

    fn replace_cfg(&mut self, mut cfg: vir::CfgMethod) -> vir::CfgMethod {
        let mut sentinel_stmt = vir::Stmt::comment("moved out stmt");
        for block in &mut cfg.basic_blocks {
            for stmt in &mut block.stmts {
                mem::swap(&mut sentinel_stmt, stmt);
                sentinel_stmt = self.replace_stmt(sentinel_stmt);
                mem::swap(&mut sentinel_stmt, stmt);
            }
        }
        cfg
    }

    fn replace_stmt(&mut self, stmt: vir::Stmt) -> vir::Stmt {
        use self::vir::StmtFolder;
        self.fold(stmt)
    }

    fn replace_expr_unfolding(&mut self, expr: vir::Expr) -> vir::Expr {
        use self::vir::ExprFolder;
        self.fold(expr)
    }
}

impl vir::StmtFolder for Optimizer {
    fn fold_assert(&mut self, vir::Assert { expr, position }: vir::Assert) -> vir::Stmt {
        vir::Stmt::Assert(vir::Assert {
            expr: self.replace_expr_unfolding(expr),
            position,
        })
    }
    fn fold_inhale(&mut self, vir::Inhale { expr }: vir::Inhale) -> vir::Stmt {
        vir::Stmt::Inhale(vir::Inhale {
            expr: self.replace_expr_unfolding(expr),
        })
    }
}

impl vir::ExprFolder for Optimizer {
    #[tracing::instrument(level = "debug", skip(self, unfolding))]
    fn fold_unfolding(&mut self, unfolding: vir::Unfolding) -> vir::Expr {
        let is_nested_duplicate = self
            .stack
            .iter()
            .any(|ancestor_hash| *ancestor_hash == hash_unfolding(&unfolding));
        if is_nested_duplicate {
            // remove the nested `unfolding (...) in` part because it's duplicate
            self.counter += 1;
            debug!("Removing outer `unfolding` from: {}", &unfolding);
            self.fold(*unfolding.base)
        } else {
            // this is not a duplicate `unfolding (...) in`, keep folding
            self.stack.push(hash_unfolding(&unfolding));
            let vir::Unfolding {
                predicate,
                arguments,
                base,
                permission,
                variant,
                position,
            } = unfolding;
            let arguments = arguments.into_iter().map(|e| self.fold(e)).collect();
            let base = self.fold_boxed(base);
            self.stack.pop().unwrap();
            vir::Expr::Unfolding(vir::Unfolding {
                predicate,
                arguments,
                base,
                permission,
                variant,
                position,
            })
        }
    }
}
