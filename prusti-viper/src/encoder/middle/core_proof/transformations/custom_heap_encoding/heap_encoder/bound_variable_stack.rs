use super::HeapEncoder;
use crate::encoder::errors::SpannedEncodingResult;
use rustc_hash::FxHashMap;
use vir_crate::low::{self as vir_low};

impl<'p, 'v: 'p, 'tcx: 'v> HeapEncoder<'p, 'v, 'tcx> {
    pub(super) fn create_quantifier_variables_remap(
        &mut self,
        bound_variables: &[vir_low::VariableDecl],
    ) -> SpannedEncodingResult<()> {
        let mut remaps = FxHashMap::default();
        for bound_variable in bound_variables {
            let remap = self.fresh_variable(bound_variable)?;
            remaps.insert(bound_variable.clone(), remap);
        }
        self.bound_variable_remap_stack.push(remaps);
        Ok(())
    }
}

#[derive(Default)]
pub(super) struct BoundVariableRemapStack {
    stack: Vec<FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl>>,
}

impl BoundVariableRemapStack {
    pub(super) fn push(&mut self, remaps: FxHashMap<vir_low::VariableDecl, vir_low::VariableDecl>) {
        self.stack.push(remaps);
    }

    pub(super) fn pop(&mut self) {
        self.stack.pop();
    }

    pub(super) fn get(&self, variable: &vir_low::VariableDecl) -> Option<&vir_low::VariableDecl> {
        for remaps in self.stack.iter().rev() {
            if let Some(remap) = remaps.get(variable) {
                return Some(remap);
            }
        }
        None
    }

    pub(super) fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }
}
