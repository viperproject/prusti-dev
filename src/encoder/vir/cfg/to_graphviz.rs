// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir::cfg::method::*;
use std::io::Write;

fn escape_html<S: ToString>(s: S) -> String {
    s.to_string()
        .replace("{", "\\{")
        .replace("}", "\\}")
        .replace("&", "&amp;")
        .replace(">", "&gt;")
        .replace("<", "&lt;")
        .replace("\n", "<br/>")
}

impl CfgMethod {
    pub fn to_graphviz(&self, graph: &mut Write) {
        writeln!(graph, "digraph CFG {{").unwrap();
        writeln!(graph, "node[shape=box];").unwrap();

        for (index, block) in self.basic_blocks.iter().enumerate() {
            let label = self.index_to_label(index);
            writeln!(
                graph,
                "\"{}\" node[label=\"{}\"];",
                escape_html(&label),
                escape_html(self.block_to_graphviz(&label, block)),
            ).unwrap();
        }

        for (index, block) in self.basic_blocks.iter().enumerate() {
            let block_label = self.index_to_label(index);
            let targets = block.successor.get_following();
            for target in targets {
                let target_label = self.index_to_label(target.block_index);
                writeln!(
                    graph,
                    "\"{}\" -> \"{}\";",
                    escape_html(&block_label),
                    escape_html(&target_label),
                ).unwrap();
            }
        }

        // Add title
        writeln!(graph, "labelloc=\"t\";").unwrap();
        writeln!(graph, "label=\"Method {}\";", escape_html(self.name())).unwrap();
        writeln!(graph, "}}").unwrap();
    }

    fn index_to_label(&self, index: usize) -> String {
        self.basic_blocks_labels[index].clone()
    }

    fn block_to_graphviz(&self, label: &str, block: &CfgBlock) -> String {
        label.to_string()
    }
}
