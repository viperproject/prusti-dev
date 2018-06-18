// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir::ast::*;
use encoder::vir::cfg::method::*;
use std::fmt::Debug;

/// A `CfgAugmenter` can be used to introduce new behaviour-preserving statements before existing
/// statements, and before branches join.
/// In particular, a `CfgAugmenter` is *not* intended to be used to change the structure or content
/// of a CFG.
pub trait CfgAugmenter<BranchCtxt: Clone> {
    /// Return the initial branch context
    fn initial_context(&self) -> BranchCtxt;

    /// Prepend some statements to an existing statement, mutating the branch context
    fn prepend_stmt(&self, stmt: &Stmt, bctxt: &mut BranchCtxt) -> Vec<Stmt>;

    /// Prepend some statements to an existing successor, mutating the branch context
    fn prepend_successor(&self, succ: &Successor, bctxt: &mut BranchCtxt) -> Vec<Stmt>;

    /// Prepend some statements to an existing join point, returning the merged branch context.
    fn prepend_join(&self, bctxts: Vec<&BranchCtxt>) -> (Vec<Vec<Stmt>>, BranchCtxt);

    /// Prepend some statements to a back jump
    fn prepend_back_jump(&self, bctxt: &BranchCtxt, target_bctxt: &BranchCtxt) -> Vec<Stmt>;
}

impl CfgMethod {
    pub fn augment<BranchCtxt, Augmenter: CfgAugmenter<BranchCtxt>>(
        &self,
        augmenter: Augmenter
    ) -> Self
        where BranchCtxt: Debug, BranchCtxt: Clone
    {
        let mut new_method = CfgMethod::new(
            self.method_name.clone(),
            self.formal_args.clone(),
            self.formal_returns.clone(),
            self.local_vars.clone(),
            self.get_all_labels(),
        );

        for (index, block) in self.basic_blocks.iter().enumerate() {
            let label = &self.basic_blocks_labels[index];
            new_method.add_block(
                label,
                block.invs.clone(),
                vec![]
            );
        }

        let to_visit: Vec<usize> = self.get_topological_sort().iter().map(|x| x.block_index).collect();
        let mut visited: Vec<bool> = vec![false; self.basic_blocks.len()];
        let mut initial_bctxt: Vec<Option<BranchCtxt>> = vec![None; self.basic_blocks.len()];
        let mut final_bctxt: Vec<Option<BranchCtxt>> = vec![None; self.basic_blocks.len()];

        for curr_index in to_visit {
            assert!(!visited[curr_index]);
            visited[curr_index] = true;

            let curr_block_index = new_method.block_index(curr_index);
            let curr_block = &self.basic_blocks[curr_index];

            // Join incomin visited edges. This may add one basic block for each incoming edge.
            debug!("Incoming blocks to {:?}: {:?}", curr_block_index, self.get_preceding(self.block_index(curr_index)));
            let incoming_edges: Vec<usize> = self.get_preceding(self.block_index(curr_index)).into_iter()
                .map(|x| x.block_index)
                .filter(|i| visited[*i])
                .collect();
            debug!("Incoming visited blocks to {:?}: {:?}", curr_block_index, &incoming_edges);
            let incoming_bctxt: Vec<&BranchCtxt> = incoming_edges.iter()
                .map(|i| final_bctxt[*i].as_ref().unwrap())
                .collect();
            let mut bctxt: BranchCtxt;
            if incoming_bctxt.is_empty() {
                bctxt = augmenter.initial_context();
            } else {
                let new_stmts_and_bctxt = augmenter.prepend_join(incoming_bctxt);
                let new_stmts = new_stmts_and_bctxt.0;
                bctxt = new_stmts_and_bctxt.1;
                for (&src_index, mut stmts_to_add) in incoming_edges.iter().zip(new_stmts) {
                    if !stmts_to_add.is_empty() {
                        // TODO: add to previous block, if possible
                        let src_block_index = new_method.block_index(src_index);
                        trace!("Prepend to {:?} coming from {:?}: {:?}", curr_block_index, src_block_index, &stmts_to_add);
                        let new_label = new_method.get_fresh_label_name();
                        stmts_to_add.insert(0, Stmt::comment(format!("========== {} ==========", new_label)));
                        let new_block_index = new_method.add_block(&new_label, vec![], stmts_to_add.clone());
                        new_method.set_successor(
                            new_block_index,
                            Successor::Goto(curr_block_index),
                        );
                        new_method.set_successor(
                            src_block_index,
                            new_method.basic_blocks[src_index].successor.clone().replace_target(
                                curr_block_index,
                                new_block_index
                            ),
                        );
                    }
                }
            }

            // Store initial bctxt
            trace!("Initial bctxt of {:?}: {:?}", curr_block_index, &bctxt);
            initial_bctxt[curr_index] = Some(bctxt.clone());

            // Prepend statements
            for stmt in &curr_block.stmts {
                let new_stmts = augmenter.prepend_stmt(stmt, &mut bctxt);
                trace!("Prepend {:?} to stmt '{}'", &new_stmts, &stmt);
                for new_stmt in new_stmts {
                    new_method.add_stmt(curr_block_index, new_stmt);
                }
                // Add original statement
                new_method.add_stmt(curr_block_index, stmt.clone());
            }

            // Prepend successor
            let new_stmts = augmenter.prepend_successor(&curr_block.successor, &mut bctxt);
            trace!("Prepend {:?} to successor of {:?}", &new_stmts, curr_block_index);
            for new_stmt in new_stmts {
                new_method.add_stmt(curr_block_index, new_stmt);
            }
            // Add original successor
            new_method.set_successor(
                curr_block_index,
                curr_block.successor.clone().replace_uuid(new_method.uuid),
            );

            // Check if there is any back edge
            let following = new_method.basic_blocks[curr_index].successor.get_following();
            for following_index in following {
                let index = following_index.block_index;
                if visited[index] {
                    debug!("Back edge from {:?} to {:?}", curr_block_index, following_index);
                    let mut stmts_to_add = augmenter.prepend_back_jump(&bctxt, &initial_bctxt[index].as_ref().unwrap());
                    if !stmts_to_add.is_empty() {
                        // TODO: add to previous block, if possible
                        let new_label = new_method.get_fresh_label_name();
                        stmts_to_add.insert(0, Stmt::comment(format!("========== {} ==========", new_label)));
                        let new_block_index = new_method.add_block(&new_label, vec![], stmts_to_add);
                        new_method.set_successor(
                            new_block_index,
                            Successor::Goto(following_index),
                        );
                        new_method.set_successor(
                            new_method.block_index(curr_index),
                            new_method.basic_blocks[curr_index].successor.clone().replace_target(
                                following_index,
                                new_block_index
                            ),
                        );
                    }
                }
            }

            // Store final bctxt
            trace!("Final bctxt of {:?}: {:?}", curr_block_index, &bctxt);
            final_bctxt[curr_index] = Some(bctxt);
        }

        new_method
    }
}
