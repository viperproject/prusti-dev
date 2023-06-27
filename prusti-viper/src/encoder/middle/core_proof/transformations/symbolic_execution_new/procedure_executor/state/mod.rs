use self::block::State;
use super::{super::super::encoder_context::EncoderContext, ProcedureExecutor};
use crate::encoder::errors::SpannedEncodingResult;

use vir_crate::low::{self as vir_low};

mod block;
mod keeper;

pub(super) use self::keeper::StateKeeper;

impl<'a, 'c, EC: EncoderContext> ProcedureExecutor<'a, 'c, EC> {
    pub(super) fn initialize_state_for(
        &mut self,
        new_block: &vir_low::Label,
    ) -> SpannedEncodingResult<()> {
        let predecessors = if let Some(predecessors) = self.reaching_predecessors.get(new_block) {
            &**predecessors
        } else {
            &[]
        };
        self.state_keeper.create_state_for_block(
            new_block,
            predecessors,
            &mut self.expression_interner,
            self.program_context,
            &mut self.global_heap_state,
            &mut self.trace_builder,
            self.procedure.position,
        )?;
        Ok(())
    }

    pub(super) fn finalize_current_block(&mut self) -> SpannedEncodingResult<()> {
        let current_block = self.current_block.as_ref().unwrap();
        self.state_keeper
            .finalize_block(current_block, &mut self.expression_interner)?;
        Ok(())
    }

    pub(super) fn current_state_mut(&mut self) -> &mut State {
        let current_block = self.current_block.as_ref().unwrap();
        self.state_keeper.states.get_mut(current_block).unwrap()
    }

    pub(super) fn current_state(&self) -> &State {
        let current_block = self.current_block.as_ref().unwrap();
        self.state_keeper.states.get(current_block).unwrap()
    }
}
