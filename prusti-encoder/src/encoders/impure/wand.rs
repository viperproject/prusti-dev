use pcg::{
    borrow_pcg::{
        AbstractionInputTarget, AbstractionOutputTarget,
        borrow_pcg_edge::{BorrowPcgEdgeLike, BorrowPcgEdgeRef},
        edge::{abstraction::AbstractionEdge, kind::BorrowPcgEdgeKind},
        graph::{
            BorrowsGraph,
            coupling::{PcgCoupledEdge, PcgCoupledEdges},
        },
        state::BorrowsState,
        unblock_graph::UnblockGraph,
    },
    pcg::PcgNode,
    utils::maybe_remote::MaybeRemotePlace,
};
use task_encoder::TaskEncoder;

use crate::encoders::ImpureEncVisitor;

use super::r#loop::WandOldOuter;

type Input<'a> = AbstractionInputTarget<'a>;
type Output<'a> = AbstractionOutputTarget<'a>;
type Inputs<'a> = Vec<Input<'a>>;
type Outputs<'a> = Vec<Output<'a>>;

impl<'vir, 'enc, E: TaskEncoder> ImpureEncVisitor<'vir, 'enc, E> {
    pub(crate) fn without_remote_places(
        &self,
        at: &PcgCoupledEdge<'vir>,
    ) -> Option<(Inputs<'vir>, Outputs<'vir>)> {
        let inputs = at.inputs(self.pcg_ctxt());
        if inputs.iter().any(|input| input.is_remote_place()) {
            None
        } else {
            Some((inputs, at.outputs()))
        }
    }

    pub(super) fn get_abstraction_edges<'a>(
        &self,
        g: &'a BorrowsGraph<'vir>,
    ) -> Vec<(Inputs<'vir>, Outputs<'vir>)> {
        g.coupled_edges()
            .into_iter()
            .filter_map(|edge| self.without_remote_places(&edge))
            .collect()
    }

    pub(crate) fn pcs_handle_wand(
        &mut self,
        borrows_state: &BorrowsState<'vir>,
        package: bool,
        edge: &PcgCoupledEdge<'vir>,
        label: Option<&'vir str>,
        edge_to_loop: bool,
    ) {
        // TODO: there is something in the pcs which emits spurious? opaque edge creation, skip these
        if package && !edge_to_loop {
            return;
        }
        let Some((inputs, outputs)) = self.without_remote_places(edge) else {
            return;
        };
        let mut old_outer = WandOldOuter::Label(label);
        let mut proof_block = Vec::new();
        let mut wand_rhs = Vec::new();
        for i in inputs {
            self.encode_pcg_node(&*i, &mut wand_rhs, &mut old_outer);
            if package {
                proof_block.extend(self.create_package_script(borrows_state, *i, &mut old_outer));
            }
        }
        let mut wand_lhs = Vec::new();
        for i in outputs {
            let i = i.expect_lifetime_projection();
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
        rhs: impl Into<PcgNode<'vir>>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> Vec<vir::Stmt<'vir>> {
        let ug = UnblockGraph::for_node(rhs, borrows_state, self.pcg_ctxt());

        let WandOldOuter::Label(label) = old_outer else {
            unreachable!()
        };
        let label = *label.get_or_insert_with(|| self.new_label("outer_package"));
        let actions = ug.actions(self.pcg_ctxt()).unwrap();
        let package_script = self.block(|visitor| {
            visitor.pcs_unblock_actions(borrows_state, &actions, Some(label));
        });
        package_script
    }
}
