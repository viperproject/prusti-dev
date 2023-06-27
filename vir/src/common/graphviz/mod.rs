use std::io::Write;

mod builders;
mod graph;
mod helpers;
mod writer;

pub use self::{
    builders::{NodeBuilder, RowBuilder, TableBuilder},
    graph::Graph,
    helpers::{escape_html, escape_html_wrap},
};

pub trait ToGraphviz {
    fn to_graphviz(&self, writer: &mut dyn Write) -> std::io::Result<()> {
        let graph = self.to_graph();
        graph.write(writer)
    }
    fn to_graph(&self) -> Graph;
}
