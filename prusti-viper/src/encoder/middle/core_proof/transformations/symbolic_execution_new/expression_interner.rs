use super::{egg::EGraphState, program_context::ProgramContext};
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        snapshots::SnapshotDomainInfo, transformations::encoder_context::EncoderContext,
    },
};
use egg::Id;
use rustc_hash::FxHashMap;
use vir_crate::low::{self as vir_low};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub(super) struct ExpressionId(u64);

/// FIXME: Rename this to Equality Manager or something like that.
#[derive(Default)]
pub(super) struct ExpressionInterner {
    bool_expression_ids: FxHashMap<vir_low::Expression, ExpressionId>,
}

/// Interning boolean expressions for consistency checker.
impl ExpressionInterner {
    pub(super) fn intern_bool_expression(
        &mut self,
        expression: &vir_low::Expression,
    ) -> SpannedEncodingResult<ExpressionId> {
        assert!(
            expression.is_heap_independent(),
            "expression: {}",
            expression
        );
        if let Some(expression_id) = self.bool_expression_ids.get(expression) {
            Ok(*expression_id)
        } else {
            let id = self.bool_expression_ids.len() as u64;
            let expression_id = ExpressionId(id);
            self.bool_expression_ids
                .insert(expression.clone(), expression_id);
            Ok(expression_id)
        }
    }
}
