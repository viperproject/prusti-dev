use super::ExecutionTraceBuilder;
use vir_crate::{
    common::graphviz::{escape_html_wrap, Graph, ToGraphviz},
    low::{self as vir_low},
};

pub(in super::super) struct ExecutionTraceOriginalView<'a> {
    pub(super) trace: &'a ExecutionTraceBuilder<'a>,
}

impl<'a> ToGraphviz for ExecutionTraceOriginalView<'a> {
    fn to_graph(&self) -> Graph {
        let mut graph = Graph::with_columns(&["statement"]);
        for (block_id, block) in self.trace.blocks.iter().enumerate() {
            let mut node_builder = graph.create_node(format!("block{block_id}"));
            for statement in &block.original_statements {
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
            if let Some(parent) = block.parent {
                graph.add_regular_edge(format!("block{parent}"), format!("block{block_id}"));
            }
        }
        graph
    }
}
