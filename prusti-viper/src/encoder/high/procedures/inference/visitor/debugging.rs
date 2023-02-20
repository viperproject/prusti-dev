use super::Visitor;
use rustc_hash::FxHashMap;
use vir_crate::{
    common::graphviz::{escape_html, Graph, NodeBuilder},
    middle::{self as vir_mid},
};

impl<'p, 'v, 'tcx> Visitor<'p, 'v, 'tcx> {
    pub(super) fn to_crashing_graphviz(
        &self,
        namespace: &str,
        label_markers: Option<&FxHashMap<String, bool>>,
    ) {
        let graph = self.render_crash_state(label_markers);
        let source_filename = self.encoder.env().name.source_file_name();
        let procedure_name = self.procedure_name.clone().unwrap();
        // TODO: Include all relevant information:
        // 1. Fold-unfold state.
        // 2. Mark which nodes were successfully visited.
        // 3. Mark which edges were successfully visited.
        // 4. Mark where the crash happened.
        prusti_common::report::log::report_with_writer(
            namespace,
            format!("{source_filename}.{procedure_name}.dot"),
            |writer| graph.write(writer).unwrap(),
        );
    }
    fn render_state(
        &self,
        label: &vir_mid::BasicBlockId,
        label_markers: Option<&FxHashMap<String, bool>>,
    ) -> bool {
        if let Some(label_markers) = label_markers {
            if let Some(should_display) = label_markers.get(&label.name) {
                return *should_display;
            }
        }
        false
    }
    fn render_crash_state(&self, label_markers: Option<&FxHashMap<String, bool>>) -> Graph {
        let mut graph = Graph::with_columns(&["statement"]);
        for (label, block) in &self.basic_blocks {
            let mut node_builder = self.create_node_builder(label, &mut graph);
            if self.render_state(label, label_markers) {
                self.render_state_at_entry(label, &mut node_builder);
            }
            self.render_block(label, block, &mut node_builder);
            if self.render_state(label, label_markers) {
                self.render_state_at_crash(label, &mut node_builder);
                self.render_state_at_exit(label, &mut node_builder);
            }
            node_builder.build();
            self.render_successor(label, &block.successor, &mut graph);
        }
        graph
    }
    fn is_crash_label(&self, label: &vir_mid::BasicBlockId) -> bool {
        if let Some(crash_label) = self.current_label.as_ref() {
            crash_label == label
        } else {
            false
        }
    }
    fn create_node_builder<'a>(
        &self,
        label: &vir_mid::BasicBlockId,
        graph: &'a mut Graph,
    ) -> NodeBuilder<'a> {
        if self.is_crash_label(label) {
            graph.create_node_with_custom_style(label.to_string(), "bgcolor=\"red\"".to_string())
        } else if self.successfully_processed_blocks.contains(label) {
            graph.create_node_with_custom_style(label.to_string(), "bgcolor=\"green\"".to_string())
        } else {
            graph.create_node(label.to_string())
        }
    }
    fn render_block(
        &self,
        label: &vir_mid::BasicBlockId,
        block: &vir_mid::BasicBlock,
        node_builder: &mut NodeBuilder,
    ) {
        for statement in &block.statements {
            let statement_string = match statement {
                vir_mid::Statement::Comment(statement) => {
                    format!("<font color=\"orange\">{}</font>", escape_html(statement))
                }
                _ => escape_html(statement.to_string()),
            };
            node_builder.add_row_sequence(vec![statement_string]);
        }
        if self.is_crash_label(label) {
            for statement in &self.current_statements {
                let statement_string =
                    format!("<font color=\"red\">{}</font>", escape_html(statement));
                node_builder.add_row_sequence(vec![statement_string]);
            }
        }
    }
    fn render_state_at_entry(&self, label: &vir_mid::BasicBlockId, node_builder: &mut NodeBuilder) {
        if let Some(state) = self.state_at_entry.get(label) {
            for line in state.to_string().split('\n') {
                if !line.is_empty() {
                    node_builder.add_row_single(format!(
                        "<font color=\"brown\">{}</font>",
                        escape_html(line)
                    ));
                }
            }
        }
    }
    fn render_state_at_exit(&self, label: &vir_mid::BasicBlockId, node_builder: &mut NodeBuilder) {
        if let Some(state) = self.state_at_exit.get(label) {
            for line in state.to_string().split('\n') {
                if !line.is_empty() {
                    node_builder.add_row_single(format!(
                        "<font color=\"brown\">{}</font>",
                        escape_html(line)
                    ));
                }
            }
        }
    }
    fn render_state_at_crash(&self, label: &vir_mid::BasicBlockId, node_builder: &mut NodeBuilder) {
        if self.is_crash_label(label) {
            node_builder.add_row_single("<font color=\"red\">no state object</font>".to_string());
        }
    }
    fn render_successor(
        &self,
        label: &vir_mid::BasicBlockId,
        successor: &vir_mid::Successor,
        graph: &mut Graph,
    ) {
        match successor {
            vir_mid::Successor::Exit => graph.add_exit_edge(label.to_string(), "exit".to_string()),
            vir_mid::Successor::Goto(target) => {
                graph.add_regular_edge(label.to_string(), target.to_string())
            }
            vir_mid::Successor::GotoSwitch(targets) => {
                for (condition, target) in targets {
                    graph.add_regular_annotated_edge(
                        label.to_string(),
                        target.to_string(),
                        condition.to_string(),
                    );
                }
            }
            vir_mid::Successor::NonDetChoice(first, second) => {
                graph.add_regular_annotated_edge(
                    label.to_string(),
                    first.to_string(),
                    "*".to_string(),
                );
                graph.add_regular_annotated_edge(
                    label.to_string(),
                    second.to_string(),
                    "*".to_string(),
                );
            }
        }
    }
}

impl<'p, 'v, 'tcx> Drop for Visitor<'p, 'v, 'tcx> {
    fn drop(&mut self) {
        if self.graphviz_on_crash {
            self.to_crashing_graphviz("graphviz_method_crashing_foldunfold", None);
        }
    }
}
