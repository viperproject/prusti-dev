// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir::cfg::method::*;
use std::io::Write;

fn escape_html<S: ToString>(s: S) -> String {
    s.to_string()
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
                "\"block_{}\" [shape=plaintext,label=<{}>];",
                escape_html(&label),
                self.block_to_graphviz(&label, block),
            ).unwrap();
        }

        for (index, block) in self.basic_blocks.iter().enumerate() {
            let block_label = self.index_to_label(index);
            let targets = block.successor.get_following();
            for target in targets {
                let target_label = self.index_to_label(target.block_index);
                writeln!(
                    graph,
                    "\"block_{}\" -> \"block_{}\";",
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
        let mut lines: Vec<String> = vec![];
        lines.push("<table>".to_string());

        lines.push("<th><td>".to_string());
        lines.push(escape_html(label));
        lines.push("</td></th>".to_string());

        lines.push("<tr><td>".to_string());
        lines.push("<table BORDER=\"0\">".to_string());
        for stmt in &block.stmts {
            lines.push("<tr><td ALIGN=\"LEFT\">".to_string());
            lines.push(escape_html(stmt.to_string()));
            lines.push("</td></tr>".to_string());
        }
        lines.push("</table>".to_string());
        lines.push("</td></tr>".to_string());

        lines.push("<tr><td ALIGN=\"LEFT\">".to_string());
        lines.push(escape_html(format!("{:?}", &block.successor)));
        lines.push("</td></tr>".to_string());

        lines.push("</table>".to_string());

        lines.join("")
    }
}
