use super::super::{
    ast::statement::Statement,
    cfg::procedure::{BasicBlock, Label, ProcedureDecl, Successor},
};
use crate::common::graphviz::{escape_html, escape_html_wrap, Graph, NodeBuilder, ToGraphviz};
use std::{collections::BTreeMap, io::Write};

impl ToGraphviz for ProcedureDecl {
    fn to_graph(&self) -> Graph {
        self.basic_blocks.to_graph()
    }
}

// impl ToGraphviz for Vec<BasicBlock> {
//     fn to_graph(&self) -> Graph {
//         let mut graph = Graph::with_columns(&["statement"]);
//         for block in self {
//             let label = &block.label;
//             let mut node_builder = graph.create_node(label.name.to_string());
//             block_to_graph_node(block, &mut node_builder);
//             node_builder.build();
//             match &block.successor {
//                 Successor::Return => {
//                     graph.add_exit_edge(label.name.to_string(), "return".to_string())
//                 }
//                 Successor::Goto(target) => {
//                     graph.add_regular_edge(label.name.to_string(), target.name.to_string())
//                 }
//                 Successor::GotoSwitch(targets) => {
//                     for (condition, target) in targets {
//                         graph.add_regular_annotated_edge(
//                             label.name.to_string(),
//                             target.name.to_string(),
//                             escape_html(condition.to_string()),
//                         );
//                     }
//                 }
//             }
//         }
//         graph
//     }
// }

impl ToGraphviz for BTreeMap<Label, BasicBlock> {
    fn to_graph(&self) -> Graph {
        let mut graph = Graph::with_columns(&["statement"]);
        for (label, block) in self {
            let mut node_builder = graph.create_node(label.name.to_string());
            block_to_graph_node(block, &mut node_builder);
            node_builder.build();
            match &block.successor {
                Successor::Return => {
                    graph.add_exit_edge(label.name.to_string(), "return".to_string())
                }
                Successor::Goto(target) => {
                    graph.add_regular_edge(label.name.to_string(), target.name.to_string())
                }
                Successor::GotoSwitch(targets) => {
                    for (condition, target) in targets {
                        graph.add_regular_annotated_edge(
                            label.name.to_string(),
                            target.name.to_string(),
                            escape_html(condition.to_string()),
                        );
                    }
                }
            }
        }
        graph
    }
}

fn block_to_graph_node(block: &BasicBlock, node_builder: &mut NodeBuilder) {
    for statement in &block.statements {
        let statement_string = match statement {
            Statement::Comment(statement) => {
                format!(
                    "<font color=\"orange\">{}</font>",
                    escape_html_wrap(statement)
                )
            }
            _ => escape_html_wrap(statement.to_string()),
        };
        node_builder.add_row_sequence(vec![statement_string]);
    }
}
