use std::collections::BTreeMap;
use vir_crate::low::{self as vir_low};

pub(super) struct Trace {
    pub statements: Vec<vir_low::Statement>,
    pub variables: Vec<vir_low::VariableDecl>,
    pub labels: Vec<vir_low::Label>,
}

impl Trace {
    pub(super) fn write(&self, writer: &mut dyn std::io::Write) -> std::io::Result<()> {
        for statement in &self.statements {
            writeln!(writer, "{statement}")?;
        }
        Ok(())
    }

    pub(super) fn into_procedure(
        self,
        trace_index: usize,
        original_procedure: &vir_low::ProcedureDecl,
    ) -> vir_low::ProcedureDecl {
        let entry = vir_low::Label::new("trace_start");
        let exit = vir_low::Label::new("trace_end");
        let entry_block =
            vir_low::BasicBlock::new(self.statements, vir_low::Successor::Goto(exit.clone()));
        let exit_block = vir_low::BasicBlock::new(Vec::new(), vir_low::Successor::Return);
        let mut basic_blocks = BTreeMap::new();
        basic_blocks.insert(entry.clone(), entry_block);
        basic_blocks.insert(exit.clone(), exit_block);
        let mut locals = original_procedure.locals.clone();
        locals.extend(self.variables);
        let mut custom_labels = original_procedure.custom_labels.clone();
        custom_labels.extend(self.labels);
        vir_low::ProcedureDecl::new_with_pos(
            format!("{}$trace_{}", original_procedure.name, trace_index),
            locals,
            custom_labels,
            entry,
            exit,
            basic_blocks,
            original_procedure.position,
        )
    }
}
