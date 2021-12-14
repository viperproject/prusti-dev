use super::{
    graph::{Graph, HeaderRow, Node, Row, Table},
    to_row::ToRow,
    to_text::ToText,
};
use std::collections::BTreeMap;

pub(in super::super) struct TableBuilder<'a> {
    pub(super) graph: &'a mut Graph,
    pub(super) table_name: String,
    pub(super) header: HeaderRow,
    pub(super) rows: Vec<Row>,
}

pub(in super::super) struct NodeBuilder<'a> {
    pub(super) graph: &'a mut Graph,
    pub(super) node_id: String,
    pub(super) rows: Vec<Row>,
}

pub(in super::super) struct RowBuilder<'a, 'b: 'a> {
    node_builder: &'a mut NodeBuilder<'b>,
    values: BTreeMap<String, String>,
}

impl<'a> TableBuilder<'a> {
    pub(in super::super) fn build(self) {
        let table = Table {
            table_name: self.table_name,
            header: self.header,
            rows: self.rows,
        };
        self.graph.tables.push(table);
    }
    fn columns_count(&self) -> usize {
        self.header.column_names.len()
    }
    pub(in super::super) fn add_row<S: ToText>(&mut self, contents: Vec<S>) {
        assert!(contents.len() == self.columns_count());
        self.rows.push(contents.to_row())
    }
}

impl<'b> NodeBuilder<'b> {
    pub(in super::super) fn build(self) {
        let node = Node {
            node_id: self.node_id,
            rows: self.rows,
        };
        self.graph.nodes.push(node);
    }
    pub(in super::super) fn create_row<'a>(&'a mut self) -> RowBuilder<'a, 'b> {
        RowBuilder {
            node_builder: self,
            values: Default::default(),
        }
    }
    pub(in super::super) fn add_value_row<S: ToText>(&mut self, value: &S) {
        self.rows.push(Row::Single(value.to_text()));
    }
}

impl<'a, 'b> RowBuilder<'a, 'b> {
    pub(in super::super) fn set<S: ToText + ?Sized>(&mut self, column: &str, value: &S) {
        self.values.insert(column.to_string(), value.to_text());
    }

    pub(in super::super) fn build(self) {
        let row = Row::Map(self.values);
        self.node_builder.rows.push(row);
    }
}
