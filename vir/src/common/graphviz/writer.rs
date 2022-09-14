use super::graph::{Edge, EdgeKind, Graph, HeaderRow, Node, Row, Table};
use std::io::Write;

fn create_node_id(node_id: &str) -> String {
    format!("node{node_id}")
}

impl Graph {
    pub fn write(&self, writer: &mut dyn Write) -> std::io::Result<()> {
        writeln!(writer, "digraph CFG {{")?;
        writeln!(writer, "graph [fontname=monospace];")?;
        writeln!(writer, "node [fontname=monospace];")?;
        writeln!(writer, "edge [fontname=monospace];")?;
        for (i, table) in self.tables.iter().enumerate() {
            table.write(format!("table{i}"), writer)?;
        }
        for node in &self.nodes {
            node.write(&self.column_names, writer)?;
        }
        for exit_target in &self.exit_targets {
            writeln!(
                writer,
                "{} [label=\"{}\"]",
                create_node_id(exit_target),
                exit_target
            )?;
        }
        for edge in &self.edges {
            edge.write(writer)?;
        }
        writeln!(writer, "}}")?;
        Ok(())
    }
}

impl Table {
    fn write(&self, table_id: String, writer: &mut dyn Write) -> std::io::Result<()> {
        writeln!(writer, "{} [", create_node_id(&table_id))?;
        writeln!(writer, "  style=filled")?;
        writeln!(writer, "  shape = \"record\"")?;
        writeln!(writer, "  label =<<table>")?;
        writeln!(
            writer,
            "    <tr><td colspan=\"{}\">{}</td></tr>",
            self.header.column_names.len(),
            self.table_name
        )?;
        self.header.write(writer)?;
        for row in &self.rows {
            row.write(&self.header.column_names, writer)?;
        }
        writeln!(writer, "  </table>>")?;
        writeln!(writer, "]")?;
        Ok(())
    }
}

impl HeaderRow {
    fn write(&self, writer: &mut dyn Write) -> std::io::Result<()> {
        write!(writer, "    <tr>")?;
        for name in &self.column_names {
            write!(writer, "<td><b>{name}</b></td>")?;
        }
        writeln!(writer, "</tr>")?;
        Ok(())
    }
}

impl Row {
    fn write(&self, column_names: &[String], writer: &mut dyn Write) -> std::io::Result<()> {
        write!(writer, "    <tr>")?;
        match self {
            Row::Single(value) => {
                write!(
                    writer,
                    "<td colspan=\"{}\" align=\"left\" balign=\"left\">{}</td>",
                    column_names.len(),
                    value
                )?;
            }
            Row::Seq(values) => {
                for value in values {
                    write!(writer, "<td align=\"left\" balign=\"left\">{value}</td>")?;
                }
            }
            Row::Map(values) => {
                for column in column_names {
                    if let Some(value) = values.get(column) {
                        write!(writer, "<td align=\"left\" balign=\"left\">{value}</td>")?;
                    } else {
                        write!(writer, "<td align=\"left\" balign=\"left\">n/a</td>")?;
                    }
                }
            }
        }
        writeln!(writer, "</tr>")?;
        Ok(())
    }
}

impl Node {
    fn write(&self, column_names: &[String], writer: &mut dyn Write) -> std::io::Result<()> {
        writeln!(writer, "{} [", create_node_id(&self.node_id))?;
        writeln!(writer, "  shape = \"record\"")?;
        writeln!(
            writer,
            "  label =<<table border=\"0\" cellborder=\"0\" cellspacing=\"0\">"
        )?;
        writeln!(
            writer,
            "    <tr><td colspan=\"{}\" {}>{}</td></tr>",
            column_names.len(),
            self.node_id_style,
            self.node_id
        )?;
        write!(writer, "    <tr>")?;
        for name in column_names {
            write!(writer, "<td><b>{name}</b></td>")?;
        }
        writeln!(writer, "</tr>")?;
        for row in &self.rows {
            row.write(column_names, writer)?;
        }
        writeln!(writer, "  </table>>")?;
        writeln!(writer, "]")?;
        Ok(())
    }
}

impl Edge {
    fn write(&self, writer: &mut dyn Write) -> std::io::Result<()> {
        let source = create_node_id(&self.source);
        let target = create_node_id(&self.target);
        let annotation = if let Some(annotation) = &self.annotation {
            format!("label=\"{annotation}\"")
        } else {
            "".to_string()
        };
        match self.kind {
            EdgeKind::Normal => {
                writeln!(writer, "\"{source}\" -> \"{target}\" [{annotation}]")?;
            }
            EdgeKind::Unwind => {
                writeln!(
                    writer,
                    "\"{source}\" -> \"{target}\" [color=red {annotation}]"
                )?;
            }
            EdgeKind::Imaginary => {
                writeln!(
                    writer,
                    "\"{source}\" -> \"{target}\" [style=\"dashed\" {annotation}]"
                )?;
            }
        };
        Ok(())
    }
}
