// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::errors::{ErrorCtxt, SpannedEncodingError, SpannedEncodingResult};
use prusti_rustc_interface::{errors::MultiSpan, hir::def_id::DefId};
use std::fmt::Debug;
use vir_crate::polymorphic as vir;

use super::super::PureFunctionEncoderInterface;

pub trait TimeReasoningInterface<'tcx> {
    fn get_tick_call<T: Into<MultiSpan> + Debug>(
        &self,
        span: T,
        amount: usize,
        scope_ids: &[isize],
        parent_def_id: DefId,
    ) -> SpannedEncodingResult<Vec<vir::Stmt>>;
}

impl<'v, 'tcx: 'v> TimeReasoningInterface<'tcx> for crate::encoder::encoder::Encoder<'v, 'tcx> {
    fn get_tick_call<T: Into<MultiSpan> + Debug>(
        &self,
        span: T,
        amount: usize,
        scope_ids: &[isize],
        parent_def_id: DefId,
    ) -> SpannedEncodingResult<Vec<vir::Stmt>> {
        let multispan = span.into();
        let pos = self.error_manager().register_error(
            multispan.clone(),
            ErrorCtxt::NotEnoughTimeCredits,
            parent_def_id,
        );

        let credits_def_id = self
            .get_procedure_def_id("prusti_contracts::time_credits")
            .ok_or_else(|| {
                SpannedEncodingError::internal(
                    "couldn't find DefId of time_credits",
                    multispan.clone(),
                )
            })?;
        let credits_substs = self.env().query.identity_substs(credits_def_id);
        let receipts_def_id = self
            .get_procedure_def_id("prusti_contracts::time_receipts")
            .ok_or_else(|| {
                SpannedEncodingError::internal(
                    "couldn't find DefId of time_receipts",
                    multispan.clone(),
                )
            })?;
        let receipts_substs = self.env().query.identity_substs(credits_def_id);
        let (credits_func_name, credits_return_type) =
            self.encode_pure_function_use(credits_def_id, parent_def_id, credits_substs)?;
        assert!(credits_return_type == vir::Type::Bool);
        let (receipts_func_name, receipts_return_type) =
            self.encode_pure_function_use(receipts_def_id, parent_def_id, receipts_substs)?;
        assert!(receipts_return_type == vir::Type::Bool);

        let encoded_amount: vir::Expr = amount.into();
        let mut stmts = vec![vir::Stmt::comment("tick call")];
        stmts.extend(scope_ids.iter().map(|&scope_id| {
            vir::Stmt::exhale(
                vir::Expr::resource_access_predicate(
                    credits_func_name.clone(),
                    vec![scope_id.into()],
                    vec![vir::LocalVar::new("scope_id", vir::Type::Int)],
                    encoded_amount.clone(),
                    pos,
                ),
                pos,
            )
        }));
        stmts.extend(scope_ids.iter().map(|&scope_id| {
            vir::Stmt::inhale(
                vir::Expr::resource_access_predicate(
                    receipts_func_name.clone(),
                    vec![scope_id.into()],
                    vec![vir::LocalVar::new("scope_id", vir::Type::Int)],
                    encoded_amount.clone(),
                    pos,
                ),
                pos,
            )
        }));
        Ok(stmts)
    }
}
