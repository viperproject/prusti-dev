use super::ProcedureExecutor;
use crate::encoder::middle::core_proof::transformations::{
    encoder_context::EncoderContext, symbolic_execution_new::block_builder::BlockBuilder,
};
use vir_crate::{
    common::graphviz::{escape_html_wrap, Graph, NodeBuilder, ToGraphviz},
    low::{self as vir_low},
};

fn label_to_string(label: &vir_low::Label) -> String {
    label.name.clone()
}

fn build_block(mut node_builder: NodeBuilder, statements: &[vir_low::Statement]) {
    for statement in statements {
        let statement_string = match statement {
            vir_low::Statement::Comment(statement) => {
                format!(
                    "<font color=\"orange\">{}</font>",
                    escape_html_wrap(statement)
                )
            }
            _ => escape_html_wrap(statement.to_string()),
        };
        node_builder.add_row_sequence(vec![statement_string]);
    }
    node_builder.build();
}

impl<'a, 'c, EC: EncoderContext> ToGraphviz for ProcedureExecutor<'a, 'c, EC> {
    fn to_graph(&self) -> Graph {
        let mut graph = Graph::with_columns(&["statement"]);
        for (label, block) in &self.trace_builder.blocks {
            let node_builder = graph.create_node(label_to_string(label));
            build_block(node_builder, &block.statements);
            for successor in &block.successors {
                if let Some(edge_block) = self
                    .trace_builder
                    .edge_blocks
                    .get(&(label.clone(), successor.clone()))
                {
                    let edge_label = format!(
                        "{}__{}__edge",
                        label_to_string(label),
                        label_to_string(successor)
                    );
                    let node_builder = graph.create_node(edge_label.clone());
                    build_block(node_builder, edge_block);
                    graph.add_regular_edge(label_to_string(label), edge_label.clone());
                    graph.add_regular_edge(edge_label, label_to_string(successor));
                } else {
                    graph.add_regular_edge(label_to_string(label), label_to_string(successor));
                }
            }
        }
        if let Some(label) = &self.current_block {
            let block = self.current_block_builder.as_ref().unwrap();
            let node_builder = graph.create_node_with_custom_style(
                label_to_string(label),
                "bgcolor=\"red\"".to_string(),
            );
            build_block(node_builder, &block.statements);
            for successor in &block.successors {
                graph.add_regular_edge(label_to_string(label), label_to_string(successor));
            }
        }
        graph
    }
}
