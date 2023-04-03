use rustc_hash::FxHashMap;

use crate::vir::polymorphic_vir::cfg;

/// Merge consequitive basic blocks that are joined by only one edge.
pub fn clean_cfg(mut method: cfg::CfgMethod) -> cfg::CfgMethod {
    let predecessors = method.predecessors();
    let traversal_order = method.get_topological_sort();
    assert_eq!(
        traversal_order[0].block_index, 0,
        "The start block should be first."
    );
    let mut new_basic_blocks = Vec::new();
    let mut basic_blocks: FxHashMap<_, _> = method.basic_blocks.into_iter().enumerate().collect();
    let mut new_indices = FxHashMap::default();

    for cfg::CfgBlockIndex { block_index, .. } in traversal_order {
        if let Some(mut basic_block) = basic_blocks.remove(&block_index) {
            let new_index = new_basic_blocks.len();
            assert!(new_indices.insert(block_index, new_index).is_none());
            while let cfg::Successor::Goto(target) = &basic_block.successor {
                // If the current basic block has only one successor.
                if predecessors[&target.block_index].len() == 1 {
                    // If the successor block has only one predecessor.

                    assert!(new_indices.insert(target.block_index, new_index).is_none());
                    let target_block = basic_blocks.remove(&target.block_index).unwrap();

                    basic_block.stmts.extend(target_block.stmts);
                    basic_block.successor = target_block.successor;
                } else {
                    break;
                }
            }
            new_basic_blocks.push(basic_block);
        }
    }
    for basic_block in &mut new_basic_blocks {
        match &mut basic_block.successor {
            cfg::Successor::Undefined | cfg::Successor::Return => {}
            cfg::Successor::Goto(target) => {
                target.block_index = new_indices[&target.index()];
            }
            cfg::Successor::GotoSwitch(conditional_targets, default_target) => {
                default_target.block_index = new_indices[&default_target.index()];
                for (_, target) in conditional_targets {
                    target.block_index = new_indices[&target.index()];
                }
            }
        }
    }
    method.basic_blocks = new_basic_blocks;
    method
}
