use super::block_builder::BlockBuilder;
use crate::encoder::errors::SpannedEncodingResult;
use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

pub(super) struct TraceBuilder {
    pub(super) blocks: BTreeMap<vir_low::Label, BlockBuilder>,
    pub(super) edge_blocks: BTreeMap<(vir_low::Label, vir_low::Label), Vec<vir_low::Statement>>,
}

impl TraceBuilder {
    pub(super) fn new() -> SpannedEncodingResult<Self> {
        let builder = Self {
            blocks: BTreeMap::new(),
            edge_blocks: BTreeMap::new(),
        };
        Ok(builder)
    }

    pub(super) fn add_block(
        &mut self,
        label: vir_low::Label,
        block: BlockBuilder,
    ) -> SpannedEncodingResult<()> {
        self.blocks.insert(label, block);
        Ok(())
    }

    // pub(super) fn get_block_mut(
    //     &mut self,
    //     label: &vir_low::Label,
    // ) -> SpannedEncodingResult<&mut BlockBuilder> {
    //     Ok(self.blocks.get_mut(label).unwrap())
    // }

    pub(super) fn add_edge_block(
        &mut self,
        source: vir_low::Label,
        target: vir_low::Label,
        statements: Vec<vir_low::Statement>,
    ) -> SpannedEncodingResult<()> {
        self.edge_blocks.insert((source, target), statements);
        Ok(())
    }
}
