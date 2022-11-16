use std::{
    collections::{BTreeMap, BTreeSet},
    io::Write,
};

use super::builders::{NodeBuilder, TableBuilder};

pub struct Graph {
    pub(super) column_names: Vec<String>,
    pub(super) nodes: Vec<Node>,
    pub(super) edges: Vec<Edge>,
    pub(super) exit_targets: BTreeSet<String>,
    pub(super) tables: Vec<Table>,
}

pub(super) struct Node {
    pub(super) node_id: String,
    pub(super) node_id_style: String,
    pub(super) rows: Vec<Row>,
}

pub(super) enum EdgeKind {
    Normal,
    Unwind,
    Imaginary,
}

pub(super) struct Edge {
    pub(super) source: String,
    pub(super) target: String,
    pub(super) annotation: Option<String>,
    pub(super) kind: EdgeKind,
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
    slice.iter().map(|s| s.to_string()).collect()
}

impl Graph {
    pub fn with_columns(column_names: &[&str]) -> Self {
        Self {
            column_names: to_string_vector(column_names),
            nodes: Default::default(),
            edges: Default::default(),
            exit_targets: Default::default(),
            tables: Default::default(),
        }
    }
    pub fn create_table<'a>(
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
    pub fn create_node(&mut self, node_id: String) -> NodeBuilder<'_> {
        self.create_node_with_custom_style(node_id, "bgcolor=\"grey\"".to_string())
    }
    pub fn create_node_with_custom_style(
        &mut self,
        node_id: String,
        node_id_style: String,
    ) -> NodeBuilder<'_> {
        NodeBuilder {
            graph: self,
            node_id,
            node_id_style,
            rows: Vec::new(),
        }
    }
    pub fn add_regular_edge(&mut self, source: String, target: String) {
        self.edges.push(Edge {
            source,
            target,
            annotation: None,
            kind: EdgeKind::Normal,
        })
    }
    pub fn add_regular_annotated_edge(
        &mut self,
        source: String,
        target: String,
        annotation: String,
    ) {
        self.edges.push(Edge {
            source,
            target,
            annotation: Some(annotation),
            kind: EdgeKind::Normal,
        })
    }
    pub fn add_unwind_edge(&mut self, source: String, target: String) {
        self.edges.push(Edge {
            source,
            target,
            annotation: None,
            kind: EdgeKind::Unwind,
        })
    }
    pub fn add_imaginary_edge(&mut self, source: String, target: String) {
        self.edges.push(Edge {
            source,
            target,
            annotation: None,
            kind: EdgeKind::Imaginary,
        })
    }
    pub fn add_exit_edge(&mut self, source: String, target: String) {
        self.exit_targets.insert(target.clone());
        self.edges.push(Edge {
            source,
            target,
            annotation: None,
            kind: EdgeKind::Normal,
        })
    }
}
