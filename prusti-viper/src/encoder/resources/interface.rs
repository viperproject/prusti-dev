// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::super::errors::ErrorCtxt;
use prusti_rustc_interface::errors::MultiSpan;
use vir_crate::polymorphic as vir;

pub trait ResourcesEncoderInterface {
    fn get_tick_call<T: Into<MultiSpan>>(&self, span: T, amount: usize) -> Vec<vir::Stmt>;
}

impl<'p, 'v: 'p, 'tcx: 'v> ResourcesEncoderInterface
    for super::super::procedure_encoder::ProcedureEncoder<'p, 'v, 'tcx>
{
    fn get_tick_call<T: Into<MultiSpan>>(&self, span: T, amount: usize) -> Vec<vir::Stmt> {
        let pos = self.register_error(span, ErrorCtxt::NotEnoughTimeCredits);
        vec![
            vir::Stmt::Exhale(vir::Exhale {
                expr: vir::Expr::resource_access_predicate(
                    vir::common::ResourceType::TimeCredits,
                    amount.into(),
                ).set_pos(pos),
                position: pos,
            }),
            vir::Stmt::Inhale(vir::Inhale {
                expr: vir::Expr::resource_access_predicate(
                    vir::common::ResourceType::TimeReceipts,
                    amount.into(),
                ),
            }),
        ]
    }
}
