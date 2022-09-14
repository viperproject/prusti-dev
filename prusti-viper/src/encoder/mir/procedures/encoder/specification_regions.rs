use crate::encoder::errors::SpannedEncodingResult;
use prusti_rustc_interface::middle::mir::{self};
use rustc_hash::FxHashSet;

// pub(super) struct SpecificationRegionEncoding {
//     pub(super) exit_target_block: mir::BasicBlock,
//     /// FIXME: We currently assume no branching in the specification region.
//     pub(super) statements: Vec<vir_high::Statement>,
// }

impl<'p, 'v: 'p, 'tcx: 'v> super::ProcedureEncoder<'p, 'v, 'tcx> {
    pub(super) fn encode_specification_regions(&mut self) -> SpannedEncodingResult<()> {
        for (entry_block, exit_target_block, region) in
            self.specification_blocks.take_specification_regions()
        {
            // First, encode all specification expressions because they are sometimes used before they are declared.
            let mut encoded_blocks = FxHashSet::default();
            for bb in &region {
                let block = &self.mir[*bb];
                if self.try_encode_specification_expression(*bb, block)? {
                    encoded_blocks.insert(*bb);
                }
            }

            // Encode the remaining specification blocks.
            let mut statements = Vec::new();
            for bb in &region {
                if !encoded_blocks.contains(bb) {
                    self.encode_specification_block(*bb, &mut statements, Some(entry_block))?;
                }
            }

            // let encoding = SpecificationRegionEncoding {
            //     exit_target_block,
            //     statements,
            // };
            assert!(self
                .specification_region_encoding_statements
                .insert(entry_block, statements,)
                .is_none());
            assert!(self
                .specification_region_exit_target_block
                .insert(entry_block, exit_target_block,)
                .is_none());
            for bb in &region {
                for statement in &self.mir.basic_blocks[*bb].statements {
                    match statement.kind {
                        mir::StatementKind::StorageLive(local)
                        | mir::StatementKind::StorageDead(local) => {
                            self.locals_used_only_in_specification_regions.insert(local);
                        }
                        _ => {}
                    }
                }
            }
        }
        Ok(())
    }
}
