use super::graph::{Graph, HeaderRow, Node, Row, Table};
use std::collections::BTreeMap;

pub struct TableBuilder<'a> {
    pub(super) graph: &'a mut Graph,
    pub(super) table_name: String,
    pub(super) header: HeaderRow,
    pub(super) rows: Vec<Row>,
}

pub struct NodeBuilder<'a> {
    pub(super) graph: &'a mut Graph,
    pub(super) node_id: String,
    pub(super) node_id_style: String,
    pub(super) rows: Vec<Row>,
}

pub struct RowBuilder<'a, 'b: 'a> {
    node_builder: &'a mut NodeBuilder<'b>,
    values: BTreeMap<String, String>,
}

impl<'a> TableBuilder<'a> {
    pub fn build(self) {
        let table = Table {
            table_name: self.table_name,
            header: self.header,
            rows: self.rows,
        };
        self.graph.tables.push(table);
    }

    pub fn columns_count(&self) -> usize {
        self.header.column_names.len()
    }

    pub fn add_row(&mut self, contents: Vec<String>) {
        assert!(contents.len() == self.columns_count());
        self.rows.push(Row::Seq(contents))
    }
}

impl<'b> NodeBuilder<'b> {
    pub fn build(self) {
        let node = Node {
            node_id: self.node_id,
            node_id_style: self.node_id_style,
            rows: self.rows,
        };
        self.graph.nodes.push(node);
    }

    pub fn create_row<'a>(&'a mut self) -> RowBuilder<'a, 'b> {
        RowBuilder {
            node_builder: self,
            values: Default::default(),
        }
    }

    pub fn add_row_single(&mut self, value: String) {
        self.rows.push(Row::Single(value));
    }

    pub fn add_row_sequence(&mut self, values: Vec<String>) {
        self.rows.push(Row::Seq(values));
    }
}

impl<'a, 'b> RowBuilder<'a, 'b> {
    pub fn set(&mut self, column: &str, value: String) {
        self.values.insert(column.to_string(), value);
    }

    pub fn build(self) {
        let row = Row::Map(self.values);
        self.node_builder.rows.push(row);
    }
}
