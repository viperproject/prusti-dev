use super::HeapEntry;
use crate::encoder::middle::core_proof::transformations::symbolic_execution::trace_builder::ExecutionTraceHeapView;
use vir_crate::common::graphviz::{escape_html_wrap, Graph, ToGraphviz};

impl<'a> ToGraphviz for ExecutionTraceHeapView<'a> {
    fn to_graph(&self) -> Graph {
        let mut graph = Graph::with_columns(&["statement"]);
        for (block_id, block) in self.iter_blocks().enumerate() {
            let mut node_builder = graph.create_node(format!("block{block_id}"));
            for statement in block.iter_entries() {
                let statement_string = match statement {
                    HeapEntry::Comment(statement) => {
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
            if let Some(parent) = block.parent() {
                graph.add_regular_edge(format!("block{parent}"), format!("block{block_id}"));
            }
        }
        graph
    }
}
