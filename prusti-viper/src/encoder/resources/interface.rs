// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::super::errors::ErrorCtxt;
use prusti_rustc_interface::errors::MultiSpan;
use vir_crate::polymorphic as vir;

pub trait ResourcesEncoderInterface {
    fn get_tick_call<T: Into<MultiSpan>>(
        &self,
        span: T,
        amount: usize,
        scope_ids: &[isize],
    ) -> Vec<vir::Stmt>;
}

// TODO: differentiate between loops' and functions' bodies errors

impl<'p, 'v: 'p, 'tcx: 'v> ResourcesEncoderInterface
    for super::super::procedure_encoder::ProcedureEncoder<'p, 'v, 'tcx>
{
    fn get_tick_call<T: Into<MultiSpan>>(
        &self,
        span: T,
        amount: usize,
        scope_ids: &[isize],
    ) -> Vec<vir::Stmt> {
        let pos = self.register_error(span, ErrorCtxt::NotEnoughTimeCredits);
        let mut stmts = vec![vir::Stmt::comment("tick call")];
        stmts.extend(scope_ids.iter().map(|&scope_id| {
            vir::Stmt::exhale(
                vir::Expr::resource_access_predicate(
                    vir::ResourceType::TimeCredits,
                    amount.into(),
                    scope_id,
                ),
                pos,
            )
        }));
        stmts.extend(scope_ids.iter().map(|&scope_id| {
            vir::Stmt::inhale(vir::Expr::resource_access_predicate(
                vir::ResourceType::TimeReceipts,
                amount.into(),
                scope_id,
            ))
        }));
        stmts
    }
}
