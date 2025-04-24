use std::collections::BTreeSet;

use pcg::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPCGEdgeLike, BorrowPCGEdgeRef},
        edge::{abstraction::AbstractionType, kind::BorrowPCGEdgeKind},
        graph::BorrowsGraph,
        region_projection::RegionProjection,
        state::BorrowsState,
        unblock_graph::UnblockGraph,
    },
    combined_pcs::PCGNode,
    utils::{maybe_old::MaybeOldPlace, maybe_remote::MaybeRemotePlace},
};
use task_encoder::TaskEncoder;

use crate::encoders::ImpureEncVisitor;

use super::r#loop::WandOldOuter;

type Inputs<'a> = BTreeSet<PCGNode<'a, MaybeRemotePlace<'a>, MaybeRemotePlace<'a>>>;
type Outputs<'a> = BTreeSet<RegionProjection<'a, MaybeOldPlace<'a>>>;

impl<'vir, 'enc, E: TaskEncoder> ImpureEncVisitor<'vir, 'enc, E> {
    pub(crate) fn ignore_abstraction_edge(
        at: &AbstractionType<'vir>,
    ) -> Option<(Inputs<'vir>, Outputs<'vir>)> {
        let inputs: Inputs<'vir> = at.inputs();
        let skip = inputs
            .iter()
            .any(|i| matches!(i, PCGNode::Place(MaybeRemotePlace::Remote(_))));
        if skip {
            None
        } else {
            Some((inputs, at.outputs()))
        }
    }

    pub(super) fn get_abstraction_edges<'a>(
        g: &'a BorrowsGraph<'vir>,
    ) -> impl Iterator<Item = (BorrowPCGEdgeRef<'vir, 'a>, Inputs<'vir>, Outputs<'vir>)> + 'a {
        g.edges().filter_map(|edge| match edge.kind() {
            BorrowPCGEdgeKind::Abstraction(at) => {
                Self::ignore_abstraction_edge(at).map(|(inputs, outputs)| (edge, inputs, outputs))
            }
            _ => None,
        })
    }

    pub(crate) fn pcs_handle_wand(
        &mut self,
        borrows_state: &BorrowsState<'vir>,
        package: bool,
        edge: &AbstractionType<'vir>,
        label: Option<&'vir str>,
        edge_to_loop: bool,
    ) {
        // TODO: there is something in the pcs which emits spurious? opaque edge creation, skip these
        if package && !edge_to_loop {
            return;
        }
        let Some((inputs, outputs)) = Self::ignore_abstraction_edge(edge) else {
            return;
        };
        let mut old_outer = WandOldOuter::Label(label);
        let mut proof_block = Vec::new();
        let mut wand_rhs = Vec::new();
        for i in inputs {
            self.encode_pcg_node(&i, &mut wand_rhs, &mut old_outer);
            if package {
                proof_block.extend(self.create_package_script(borrows_state, i, &mut old_outer));
            }
        }
        let mut wand_lhs = Vec::new();
        for i in outputs {
            let exprs = self.encode_region_projection(i, &mut old_outer);
            wand_lhs.extend(exprs);
        }
        let wand = self.vcx.mk_wand(
            self.vcx.mk_conj(self.vcx.alloc_slice(&wand_lhs)),
            self.vcx.mk_conj(self.vcx.alloc_slice(&wand_rhs)),
        );
        if package {
            let proof_block = self.vcx.alloc_slice(&proof_block);
            self.stmt(self.vcx.mk_package_stmt(wand, proof_block));
        } else {
            self.stmt(self.vcx.mk_apply_stmt(wand));
        }
    }

    fn create_package_script(
        &mut self,
        borrows_state: &BorrowsState<'vir>,
        rhs: impl Into<PCGNode<'vir>>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> Vec<vir::Stmt<'vir>> {
        let ug = UnblockGraph::for_node(rhs, borrows_state, self.fpcs_analysis.repacker());

        let WandOldOuter::Label(label) = old_outer else {
            unreachable!()
        };
        let label = *label.get_or_insert_with(|| self.new_label("outer_package"));
        let actions = ug.actions(self.fpcs_analysis.repacker()).unwrap();
        let package_script = self.block(|visitor| {
            visitor.pcs_unblock_actions(borrows_state, &actions, Some(label));
        });
        package_script
    }
}
