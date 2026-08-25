use pcg::{
    borrow_pcg::{
        AbstractionInputTarget, AbstractionOutputTarget, graph::BorrowsGraph, state::BorrowsState,
        unblock_graph::UnblockGraph,
    },
    coupling::PcgCoupledEdgeKind,
    pcg::PcgNode,
};
use task_encoder::TaskEncoder;

use crate::encoders::{EncodeResult, ImpureEncVisitor};

use super::r#loop::WandOldOuter;

type Input<'a> = AbstractionInputTarget<'a>;
type Output<'a> = AbstractionOutputTarget<'a>;
type Inputs<'a> = Vec<Input<'a>>;
type Outputs<'a> = Vec<Output<'a>>;

impl<'vir, 'enc, E: TaskEncoder> ImpureEncVisitor<'vir, 'enc, E> {
    pub(super) fn get_abstraction_edges<'a>(
        &self,
        g: &'a BorrowsGraph<'vir>,
    ) -> Vec<(Inputs<'vir>, Outputs<'vir>)> {
        g.coupled_edges()
            .into_iter()
            .map(|edge| (edge.value().inputs(self.pcg_ctxt()), edge.value().outputs()))
            .collect()
    }

    pub(crate) fn pcs_handle_wand(
        &mut self,
        borrows_state: &BorrowsState<'_, 'vir>,
        package: bool,
        edge: &PcgCoupledEdgeKind<'vir>,
        label: Option<&'vir str>,
        edge_to_loop: bool,
    ) -> EncodeResult<'vir, (), E> {
        // TODO: there is something in the pcs which emits spurious? opaque edge creation, skip these
        if package && !edge_to_loop {
            return Ok(());
        }
        let inputs = edge.inputs(self.pcg_ctxt());
        let outputs = edge.outputs();
        let mut old_outer = WandOldOuter::Label(label);
        let mut proof_block = Vec::new();
        let mut wand_rhs = Vec::new();
        for i in inputs {
            self.encode_pcg_node(&*i, &mut wand_rhs, &mut old_outer)?;
            if package {
                proof_block.extend(self.create_package_script(
                    borrows_state,
                    *i,
                    &mut old_outer,
                )?);
            }
        }
        let mut wand_lhs = Vec::new();
        for i in outputs {
            let i = i.expect_lifetime_projection();
            let exprs = self.encode_lifetime_projection(i, &mut old_outer)?;
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
        Ok(())
    }

    fn create_package_script(
        &mut self,
        borrows_state: &BorrowsState<'_, 'vir>,
        rhs: impl Into<PcgNode<'vir>>,
        old_outer: &mut WandOldOuter<'vir>,
    ) -> EncodeResult<'vir, Vec<vir::Stmt<'vir>>, E> {
        let ug = UnblockGraph::for_node(rhs, borrows_state, self.pcg_ctxt());

        let WandOldOuter::Label(label) = old_outer else {
            unreachable!()
        };
        let label = *label.get_or_insert_with(|| self.new_label("outer_package"));
        let actions = ug.actions(self.pcg_ctxt()).unwrap();

        self.block(|visitor| visitor.pcs_unblock_actions(borrows_state, &actions, Some(label)))
    }
}
