// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use vir_crate::polymorphic::{
    Expr, ExprFolder, ExprIterator, ResourceAccessPredicate,
};

struct Changer<'a> {
    scope_ids: &'a [isize],
}

impl<'a> ExprFolder for Changer<'a> {
    fn fold_resource_access_predicate(&mut self, expr: ResourceAccessPredicate) -> Expr {
        self.scope_ids
            .iter()
            .map(|&scope_id| expr.clone().replace_scope_id(scope_id))
            .conjoin()
    }
}

pub fn change_scope_id(expr: Expr, scope_ids: &[isize]) -> Expr {
    let mut changer = Changer { scope_ids };
    changer.fold(expr)
}
