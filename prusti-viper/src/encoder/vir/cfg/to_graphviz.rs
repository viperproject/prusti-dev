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
        writeln!(graph, "graph [fontname=monospace];").unwrap();
        writeln!(graph, "node [fontname=monospace];").unwrap();
        writeln!(graph, "edge [fontname=monospace];").unwrap();

        // Add title
        writeln!(graph, "labelloc=\"t\";").unwrap();
        writeln!(graph, "label=\"Method {}\";", escape_html(self.name())).unwrap();

        for (index, block) in self.basic_blocks.iter().enumerate() {
            let label = self.index_to_label(index);
            writeln!(
                graph,
                "\"block_{}\" [shape=none,label=<{}>];",
                escape_html(&label),
                self.block_to_graphviz(index, &label, block),
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

         writeln!(graph, "}}").unwrap();
    }

    fn index_to_label(&self, index: usize) -> String {
        self.basic_blocks_labels[index].clone()
    }

    fn block_to_graphviz(&self, index: usize, label: &str, block: &CfgBlock) -> String {
        let mut lines: Vec<String> = vec![];
        lines.push("<table border=\"0\" cellborder=\"1\" cellspacing=\"0\">".to_string());

        lines.push("<tr><td bgcolor=\"gray\" align=\"center\">".to_string());
        lines.push(format!("{} (cfg:{})", escape_html(label), index));
        lines.push("</td></tr>".to_string());

        lines.push("<tr><td align=\"left\" balign=\"left\">".to_string());
        let mut first_row = true;
        for stmt in &block.stmts {
            if !first_row {
                lines.push("<br/>".to_string());
            }
            first_row = false;
            {
                let full_stmt = stmt.to_string();
                let splitted_stmt = sub_strings(&full_stmt, 120, 116);
                let stmt_html = splitted_stmt
                    .into_iter()
                    .map(|x| escape_html(x))
                    .collect::<Vec<_>>()
                    .join(" \\ <br/>    ");
                if stmt.is_comment() {
                    lines.push(format!("<font color=\"orange\">{}</font>", stmt_html));
                } else {
                    lines.push(stmt_html);
                }
            }
        }
        lines.push("</td></tr>".to_string());

        match block.successor {
            // Red
            Successor::Undefined => lines.push("<tr><td align=\"left\" bgcolor=\"#F43E3E\">".to_string()),
            // Green
            Successor::Return => lines.push("<tr><td align=\"left\" bgcolor=\"#82CA9D\">".to_string()),
            _ => lines.push("<tr><td align=\"left\">".to_string()),
        }
        {
            let full_successor = block.successor.to_string();
            let splitted_successor = sub_strings(&full_successor, 120, 116);
            lines.push(splitted_successor.into_iter().map(|x| escape_html(x)).collect::<Vec<_>>().join(" \\ <br/>    "));
        }
        lines.push("</td></tr>".to_string());

        lines.push("</table>".to_string());

        lines.join("")
    }
}

fn sub_strings(string: &str, first_sub_len: usize, sub_len: usize) -> Vec<&str> {
    let mut subs = Vec::with_capacity(string.len() / sub_len);
    let mut iter = string.chars();
    let mut pos = 0;
    let mut is_first = true;

    while pos < string.len() {
        let mut len = 0;
        if is_first {
            for ch in iter.by_ref().take(first_sub_len) {
                len += ch.len_utf8();
            }
            is_first = false;
        } else {
            for ch in iter.by_ref().take(sub_len) {
                len += ch.len_utf8();
            }
        }
        subs.push(&string[pos..pos + len]);
        pos += len;
    }
    subs
}
