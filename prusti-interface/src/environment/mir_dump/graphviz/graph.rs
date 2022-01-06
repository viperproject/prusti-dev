use std::{
    collections::{BTreeMap, BTreeSet},
    io::Write,
};

use super::{
    builders::{NodeBuilder, TableBuilder},
    to_text::ToText,
};

pub(in super::super) struct Graph {
    pub(super) column_names: Vec<String>,
    pub(super) nodes: Vec<Node>,
    pub(super) edges: Vec<Edge>,
    pub(super) exit_targets: BTreeSet<String>,
    pub(super) tables: Vec<Table>,
}

pub(super) struct Node {
    pub(super) node_id: String,
    pub(super) rows: Vec<Row>,
}

pub(super) enum EdgeKind {
    Normal,
    Unwind,
    Imaginary,
}

pub(super) struct Edge {
    source: String,
    target: String,
    kind: EdgeKind,
}

pub(super) enum Row {
    Map(BTreeMap<String, String>),
    Seq(Vec<String>),
    Single(String),
}

pub(super) struct HeaderRow {
    pub(super) column_names: Vec<String>,
}

pub(super) struct Table {
    pub(super) table_name: String,
    pub(super) header: HeaderRow,
    pub(super) rows: Vec<Row>,
}

fn to_string_vector(slice: &[&str]) -> Vec<String> {
    slice.iter().map(|s| s.to_text()).collect()
}

fn create_node_id<S: ToText>(node_id: &S) -> String {
    format!("node{}", node_id.to_text())
}

impl Graph {
    pub(in super::super) fn with_columns(column_names: &[&str]) -> Self {
        Self {
            column_names: to_string_vector(column_names),
            nodes: Default::default(),
            edges: Default::default(),
            exit_targets: Default::default(),
            tables: Default::default(),
        }
    }
    pub(in super::super) fn write(&self, writer: &mut dyn Write) -> std::io::Result<()> {
        writeln!(writer, "digraph CFG {{")?;
        writeln!(writer, "graph [fontname=monospace];")?;
        writeln!(writer, "node [fontname=monospace];")?;
        writeln!(writer, "edge [fontname=monospace];")?;
        for (i, table) in self.tables.iter().enumerate() {
            table.write(format!("table{}", i), writer)?;
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
    pub(in super::super) fn create_table<'a>(
        &'a mut self,
        table_name: &str,
        column_names: &[&str],
    ) -> TableBuilder<'a> {
        TableBuilder {
            graph: self,
            table_name: table_name.to_string(),
            header: HeaderRow {
                column_names: to_string_vector(column_names),
            },
            rows: Vec::new(),
        }
    }
    pub(in super::super) fn create_node<S: ToText>(&mut self, node_id: S) -> NodeBuilder<'_> {
        NodeBuilder {
            graph: self,
            node_id: node_id.to_text(),
            rows: Vec::new(),
        }
    }
    pub(in super::super) fn add_regular_edge<S1: ToText, S2: ToText>(
        &mut self,
        source: &S1,
        target: &S2,
    ) {
        self.edges.push(Edge {
            source: source.to_text(),
            target: target.to_text(),
            kind: EdgeKind::Normal,
        })
    }
    pub(in super::super) fn add_unwind_edge<S1: ToText, S2: ToText>(
        &mut self,
        source: &S1,
        target: &S2,
    ) {
        self.edges.push(Edge {
            source: source.to_text(),
            target: target.to_text(),
            kind: EdgeKind::Unwind,
        })
    }
    pub(in super::super) fn add_imaginary_edge<S1: ToText, S2: ToText>(
        &mut self,
        source: &S1,
        target: &S2,
    ) {
        self.edges.push(Edge {
            source: source.to_text(),
            target: target.to_text(),
            kind: EdgeKind::Imaginary,
        })
    }
    pub(in super::super) fn add_exit_edge<S1: ToText>(&mut self, source: &S1, target: &str) {
        self.exit_targets.insert(target.to_text());
        self.edges.push(Edge {
            source: source.to_text(),
            target: target.to_text(),
            kind: EdgeKind::Normal,
        })
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
            write!(writer, "<td><b>{}</b></td>", name)?;
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
                    "<td colspan=\"{}\">{}</td>",
                    column_names.len(),
                    value
                )?;
            }
            Row::Seq(values) => {
                for value in values {
                    write!(writer, "<td>{}</td>", value)?;
                }
            }
            Row::Map(values) => {
                for column in column_names {
                    if let Some(value) = values.get(column) {
                        write!(writer, "<td>{}</td>", value)?;
                    } else {
                        write!(writer, "<td>n/a</td>")?;
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
        writeln!(writer, "  label =<<table>")?;
        writeln!(
            writer,
            "    <tr><td colspan=\"{}\">{}</td></tr>",
            column_names.len(),
            self.node_id
        )?;
        write!(writer, "    <tr>")?;
        for name in column_names {
            write!(writer, "<td><b>{}</b></td>", name)?;
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
        match self.kind {
            EdgeKind::Normal => {
                writeln!(writer, "\"{}\" -> \"{}\"", source, target)?;
            }
            EdgeKind::Unwind => {
                writeln!(writer, "\"{}\" -> \"{}\" [color=red]", source, target)?;
            }
            EdgeKind::Imaginary => {
                writeln!(
                    writer,
                    "\"{}\" -> \"{}\" [style=\"dashed\"]",
                    source, target
                )?;
            }
        };
        Ok(())
    }
}
