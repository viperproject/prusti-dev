//! Peephole simplification of hole-free expressions, run over the final
//! program (domain axioms, predicates, functions and methods).
//!
//! Composing independently encoded snapshot operations produces wrap/unwrap
//! round trips: reference snapshots built and immediately dereferenced,
//! generic casts cancelled out, snapshot constructors compared field by
//! field. The pass undoes them with [equations](equations), listed by the
//! kind of node they rewrite, each of which can be checked on its own. The
//! [traversal](walk) applies them bottom-up and takes care of everything
//! that depends on the context of a node:
//!  - `let`-bound locals are replaced by their values where that means the
//!    same: inside an `old(..)` or `unfolding` only locals and constants
//!    (other values may depend on the heap or the permissions held), and
//!    not values whose locals a binder (a quantifier or `let`) rebinds,
//!  - the span of the root of an expression tree is kept, since Prusti
//!    backtranslates Viper errors through it,
//!  - quantifier triggers and magic wands are left as encoded.
//!
//! Equations may drop subexpressions together with their well-definedness
//! checks: Prusti checks all side conditions explicitly in impure code.

mod equations;
#[cfg(test)]
mod tests;
mod walk;

use prusti_rustc_interface::data_structures::fx::{FxHashMap, FxHashSet};

use crate::{refs::*, Foldable, ViperIdent, VirCtxt};

/// A declaration that `outer(inner(k))` is `k` for every integer literal `k`
/// in one of the inclusive `ranges` (pairs of literal bounds), such as for the
/// value and constructor of a primitive snapshot domain, whose axiom only
/// holds for the values of the type.
#[derive(Clone, Copy, Debug)]
pub struct LiteralInverse<'vir> {
    pub outer: ViperIdent<'vir>,
    pub inner: ViperIdent<'vir>,
    pub ranges: &'vir [(ExprInt<'vir>, ExprInt<'vir>)],
}

/// What the simplification knows about the program: its adt constructors and
/// destructors, its total functions and the literal inverses its encoder
/// declares, used to recognize the foldable applications.
pub struct SimplifyCtx<'vir> {
    /// Constructor name to its ordered field (destructor) declarations.
    constructors: FxHashMap<&'vir str, &'vir [crate::LocalDeclDyn<'vir>]>,
    /// Destructor name to its constructor's name and field index.
    destructors: FxHashMap<&'vir str, (&'vir str, usize)>,
    /// The constructors of single-constructor adts.
    eta: FxHashSet<&'vir str>,
    /// Names of the total functions: domain functions and functions without
    /// preconditions (which therefore cannot read the heap either).
    total_functions: FxHashSet<&'vir str>,
    /// The declared literal inverses, by the name of `outer`.
    literal_inverses: FxHashMap<&'vir str, LiteralInverse<'vir>>,
}

impl<'vir> SimplifyCtx<'vir> {
    pub fn new(
        adts: &[Adt<'vir>],
        domains: &[Domain<'vir>],
        functions: &[Function<'vir>],
        literal_inverses: &[LiteralInverse<'vir>],
    ) -> Self {
        let total_functions = domains
            .iter()
            .flat_map(|d| d.functions.iter().map(|f| f.name.to_str()))
            .chain(
                functions
                    .iter()
                    .filter(|f| f.pres.is_empty())
                    .map(|f| f.name),
            )
            .collect();
        let mut constructors = FxHashMap::default();
        let mut destructors = FxHashMap::default();
        let mut eta = FxHashSet::default();
        for adt in adts {
            let eta_adt = adt.constructors.len() == 1;
            for cons in adt.constructors {
                constructors.insert(cons.name, cons.args);
                for (idx, field) in cons.args.iter().enumerate() {
                    destructors.insert(field.name, (cons.name, idx));
                }
                if eta_adt {
                    eta.insert(cons.name);
                }
            }
        }
        Self {
            constructors,
            destructors,
            eta,
            total_functions,
            literal_inverses: literal_inverses
                .iter()
                .map(|inverse| (inverse.outer.to_str(), *inverse))
                .collect(),
        }
    }
}

/// Simplifies the expressions of a program item (a domain, predicate,
/// function or method).
pub fn simplify<'vir, 'tcx, T: Foldable<'vir, (), !> + Copy>(
    vcx: &'vir VirCtxt<'tcx>,
    ctx: &SimplifyCtx<'vir>,
    item: T,
) -> T {
    let mut s = walk::Simplifier::new(vcx, ctx);
    item.fold_with(&mut walk::Roots(&mut s)).unwrap_or(item)
}
