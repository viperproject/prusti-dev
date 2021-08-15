// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::vir;
use vir_crate::polymorphic as polymorphic_vir;
use std::collections::HashMap;
use std::io;

pub(super) struct BasicBlock<'a> {
    pub guard: polymorphic_vir::Expr,
    pub current_guard: polymorphic_vir::Expr,
    pub node: &'a polymorphic_vir::borrows::Node,
    pub predecessors: Vec<usize>,
    pub statements: Vec<polymorphic_vir::Stmt>,
    pub successors: Vec<usize>,
}

pub(super) struct CFG<'a> {
    pub basic_blocks: Vec<BasicBlock<'a>>,
    /// Basic blocks that connect a pair of basic blocks. They are needed for performing
    /// fold-unfold operations on an edge.
    pub edges: HashMap<(usize, usize), Vec<polymorphic_vir::Stmt>>,
}

impl<'a> CFG<'a> {
    pub(super) fn new() -> Self {
        Self {
            basic_blocks: Vec::new(),
            edges: HashMap::new(),
        }
    }
    pub(super) fn add_block(&mut self, block: BasicBlock<'a>) {
        self.basic_blocks.push(block);
    }
}

impl<'a> CFG<'a> {
    fn block_label(&self, index: usize) -> String {
        format!("block_{}", index)
    }
    fn edge_label(&self, from: usize, to: usize) -> String {
        format!("edge_{}_{}", from, to)
    }
    fn write_to_graphviz(
        &self,
        graph: &mut dyn io::Write,
        curr_block_index: usize,
    ) -> Result<(), io::Error> {
        fn escape_html<S: ToString>(s: S) -> String {
            s.to_string()
                .replace("&", "&amp;")
                .replace(">", "&gt;")
                .replace("<", "&lt;")
                .replace("\n", "<br/>")
        }

        writeln!(graph, "digraph CFG {{")?;
        writeln!(graph, "graph [fontname=monospace];")?;
        writeln!(graph, "node [fontname=monospace];")?;
        writeln!(graph, "edge [fontname=monospace];")?;

        for (index, block) in self.basic_blocks.iter().enumerate() {
            write!(graph, "{} [shape=none,", self.block_label(index))?;
            if index == curr_block_index {
                write!(graph, "color=green,")?;
            }
            write!(graph, "label=<")?;
            write!(graph, "<table>")?;
            write!(
                graph,
                "<tr><td>borrow:</td><td>{:?}</td></tr>",
                block.node.borrow
            )?;
            for (i, stmt) in block.statements.iter().enumerate() {
                write!(
                    graph,
                    "<tr><td>{}</td><td>{}</td></tr>",
                    i,
                    escape_html(stmt)
                )?;
            }
            write!(graph, "</table>")?;
            writeln!(graph, ">];")?;
            for &predecessor in &block.predecessors {
                writeln!(
                    graph,
                    "{} -> {};",
                    self.block_label(predecessor),
                    self.block_label(index)
                )?;
            }
            for &successor in &block.successors {
                writeln!(
                    graph,
                    "{} -> {};",
                    self.block_label(index),
                    self.block_label(successor)
                )?;
            }
        }

        for (&(from, to), stmts) in &self.edges {
            write!(graph, "{} [shape=none,label=<", self.edge_label(from, to))?;
            write!(graph, "<table>")?;
            for (i, stmt) in stmts.iter().enumerate() {
                write!(
                    graph,
                    "<tr><td>{}</td><td>{}</td></tr>",
                    i,
                    escape_html(stmt)
                )?;
            }
            write!(graph, "</table>")?;
            writeln!(graph, ">];")?;
            writeln!(
                graph,
                "{} -> {};",
                self.block_label(from),
                self.edge_label(from, to)
            )?;
            writeln!(
                graph,
                "{} -> {};",
                self.edge_label(from, to),
                self.block_label(to)
            )?;
        }

        writeln!(graph, "}}")
    }
    pub(super) fn to_graphviz(&self, graph: &mut dyn io::Write, curr_block_index: usize) {
        self.write_to_graphviz(graph, curr_block_index).unwrap();
    }
}
