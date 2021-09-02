// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{HashMap, HashSet};
use log::{debug, trace};
use rustc_hir as hir;
use rustc_middle::mir;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty;
use prusti_interface::environment::Environment;

/// Structure to collect closure instantiations annotated with `prusti::spec_only`.
pub struct SpecsClosuresCollector<'tcx> {
    visited: HashSet<LocalDefId>,
    /// For each instantiation of each closure: DefId, location, operands and types of operands.
    #[allow(clippy::type_complexity)]
    instantiations: HashMap<
        DefId,
        Vec<(
            DefId,
            mir::Location,
            Vec<mir::Operand<'tcx>>,
            Vec<ty::Ty<'tcx>>,
        )>,
    >,
}

impl<'tcx> SpecsClosuresCollector<'tcx> {
    pub fn new() -> Self {
        SpecsClosuresCollector {
            visited: HashSet::new(),
            instantiations: HashMap::new(),
        }
    }

    /// Collect instantiations of `prusti::spec_only` closures from all `prusti::spec_only` items.
    pub fn collect_from_all_spec_items(&mut self, env: &Environment<'tcx>) {
        debug!("Collecting closure instantiations...");
        let tcx = env.tcx();
        for &def_id in tcx.mir_keys(()).iter() {
            if env.has_prusti_attribute(def_id.to_def_id(), "spec_only") {
                self.collect(env, def_id);
            }
        }
    }

    /// Collect instantiations of `prusti::spec_only` closures from a given procedure.
    pub fn collect(&mut self, env: &Environment<'tcx>, def_id: LocalDefId) {
        debug!("Collecting closure instantiations in {:?}", def_id);
        // Avoid visiting the same procedure multiple times
        if self.visited.contains(&def_id) {
            debug!("ClosuresCollector already visited {:?} in the past.", def_id);
            return;
        } else {
            self.visited.insert(def_id);
        }
        let tcx = env.tcx();
        let mir = env.local_mir(def_id);
        for (bb_index, bb_data) in mir.basic_blocks().iter_enumerated() {
            for (stmt_index, stmt) in bb_data.statements.iter().enumerate() {
                if let mir::StatementKind::Assign(
                    box (
                        _,
                        mir::Rvalue::Aggregate(
                            box mir::AggregateKind::Closure(cl_def_id, _),
                            ref operands,
                        ),
                    )
                ) = stmt.kind {
                    // Skip closures that are not annotated with `prusti::spec_only`.
                    if !env.has_prusti_attribute(cl_def_id, "spec_only") {
                        continue;
                    }
                    trace!("Found closure instantiation at {:?}", stmt);
                    let operand_tys = operands.iter().map(
                        |operand| operand.ty(&*mir, tcx)
                    ).collect();
                    let instantiations =
                        self.instantiations.entry(cl_def_id).or_insert_with(Vec::new);
                    instantiations.push((
                        def_id.to_def_id(),
                        mir::Location {
                            block: bb_index,
                            statement_index: stmt_index,
                        },
                        operands.clone(),
                        operand_tys
                    ));
                }
            }
        }
    }

    #[allow(clippy::type_complexity)]
    fn get_instantiations(&self, closure_def_id: DefId) -> Option<&[(
        DefId,
        mir::Location,
        Vec<mir::Operand<'tcx>>,
        Vec<ty::Ty<'tcx>>,
    )]> {
        trace!("Get closure instantiations for {:?}", closure_def_id);
        self.instantiations.get(&closure_def_id).map(|x| &x[..])
    }

    pub fn get_single_instantiation(&self, closure_def_id: DefId) -> Option<(
        DefId,
        mir::Location,
        Vec<mir::Operand<'tcx>>,
        Vec<ty::Ty<'tcx>>,
    )> {
        self.get_instantiations(closure_def_id).and_then(|instantiations| {
            assert!(instantiations.len() <= 1);
            instantiations.get(0).cloned()
        })
    }
}
