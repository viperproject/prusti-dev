use super::{language::ExpressionLanguage, EGraphState};
use crate::encoder::errors::SpannedEncodingResult;
use egg::{Id, Language};
use rustc_hash::FxHashSet;
use std::{fmt::Write, path::Path};

impl EGraphState {
    pub(in super::super) fn eclass_to_dot_file(
        &self,
        id: Id,
        filename: impl AsRef<Path>,
    ) -> SpannedEncodingResult<()> {
        use std::io::Write;
        let mut file = std::fs::File::create(filename).unwrap();
        let mut buffer = String::new();
        self.eclass_to_dot(id, &mut buffer).unwrap();
        writeln!(file, "{buffer}").unwrap();
        Ok(())
    }

    pub(in super::super) fn eclass_to_dot(
        &self,
        id: Id,
        writer: &mut dyn Write,
    ) -> std::fmt::Result {
        writeln!(writer, "digraph {{")?;

        writeln!(writer, "  compound=true")?;
        writeln!(writer, "  clusterrank=local")?;

        let mut printed_classes = FxHashSet::default();
        let mut classes_to_print = vec![id];
        while let Some(id) = classes_to_print.pop() {
            self.print_eclass(id, writer, &mut printed_classes, &mut classes_to_print)?;
        }

        writeln!(writer, "}}")?;
        Ok(())
    }

    fn print_eclass(
        &self,
        id: Id,
        writer: &mut dyn Write,
        printed_classes: &mut FxHashSet<Id>,
        classes_to_print: &mut Vec<Id>,
    ) -> std::fmt::Result {
        if !printed_classes.contains(&id) {
            printed_classes.insert(id);
            let class = &self.egraph[id];
            writeln!(writer, "  subgraph cluster_{id} {{")?;
            writeln!(writer, "    style=dotted")?;
            for (i, node) in class.iter().enumerate() {
                match node {
                    ExpressionLanguage::Variable(symbol)
                        if symbol.as_str().starts_with("snapshot$") =>
                    {
                        // ignore snapshot variables
                        writeln!(writer, "    {id}.{i}[label = \"\"]")?;
                    }
                    _ => {
                        writeln!(writer, "    {id}.{i}[label = \"{id} {node}\"]")?;
                    }
                }
            }
            writeln!(writer, "  }}")?;

            for (i_in_class, node) in class.iter().enumerate() {
                let mut arg_i = 0;
                node.try_for_each(|child| {
                    let child_class_id = self.egraph.find(child);
                    classes_to_print.push(child_class_id);
                    if child_class_id == class.id {
                        // We have a self-loop.
                        writeln!(
                            writer,
                            "  {}.{} -> {}.{}:n [lhead = cluster_{}, label=\"{}:{}\"]",
                            class.id, i_in_class, class.id, i_in_class, class.id, arg_i, child
                        )?;
                    } else {
                        writeln!(
                            writer,
                            "  {}.{} -> {}.0 [lhead = cluster_{}, label=\"{}:{}\"]",
                            class.id, i_in_class, child, child_class_id, arg_i, child
                        )?;
                    }
                    arg_i += 1;
                    Ok::<_, std::fmt::Error>(())
                })?;
            }
        }
        Ok(())
    }
}
