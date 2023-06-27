use super::facts::{
    replace_terminator::ReplaceTerminatorDesugaring, AllInputFacts, BorrowckFacts, Loan,
    LocationTable, Point, Region, RichLocation,
};
use crate::environment::debug_utils::to_text::{opaque_lifetime_string, ToText};
use prusti_rustc_interface::middle::mir;
use std::collections::{BTreeMap, BTreeSet};
use vir::high::ty::LifetimeConst;

mod graphviz;

pub use self::graphviz::LifetimesGraphviz;

pub struct Lifetimes {
    facts: BorrowckFacts,
    /// We ignore the loans that are either successfully killed or outlive the
    /// function body. This is currently an heuristic to avoid f-equalize rule.
    ignored_loans: BTreeSet<Loan>,
}

pub struct LifetimeWithInclusions {
    lifetime: Region,
    loan: Loan,
    included_in: Vec<Region>,
}

impl Lifetimes {
    pub fn new<'tcx>(
        mut input_facts: AllInputFacts,
        location_table: LocationTable,
        replace_terminator_locations: Vec<ReplaceTerminatorDesugaring>,
        body: &mir::Body<'tcx>,
    ) -> Self {
        let entry_block = mir::START_BLOCK;
        let entry_point = location_table.location_to_point(RichLocation::Start(mir::Location {
            block: entry_block,
            statement_index: 0,
        }));
        for (origin, loan) in &input_facts.placeholder {
            input_facts
                .loan_issued_at
                .push((*origin, *loan, entry_point));
        }
        for (origin1, origin2) in &input_facts.known_placeholder_subset {
            input_facts
                .subset_base
                .push((*origin1, *origin2, entry_point));
        }
        let mut output_facts = prusti_rustc_interface::polonius_engine::Output::compute(
            &input_facts,
            prusti_rustc_interface::polonius_engine::Algorithm::Naive,
            true,
        );
        assert!(output_facts.errors.is_empty());
        for ReplaceTerminatorDesugaring {
            replacing_drop_location,
            target_block,
            unwinding_block,
        } in replace_terminator_locations
        {
            let drop_point =
                location_table.location_to_point(RichLocation::Mid(replacing_drop_location));
            let alive_origins = output_facts.origin_live_on_entry[&drop_point].clone();
            let origin_contains_loan_at = output_facts
                .origin_contains_loan_at
                .get(&drop_point)
                .cloned()
                .unwrap_or_default();
            let mut copy_to_point = |target_point| {
                let target_alive_origins = output_facts
                    .origin_live_on_entry
                    .entry(target_point)
                    .or_default();
                for origin in &alive_origins {
                    if !target_alive_origins.contains(origin) {
                        target_alive_origins.push(*origin);
                        let target_origin_contains_loan_at = output_facts
                            .origin_contains_loan_at
                            .entry(target_point)
                            .or_default();
                        if let Some(loan_set) = origin_contains_loan_at.get(origin) {
                            let old_loan_set =
                                target_origin_contains_loan_at.insert(*origin, loan_set.clone());
                            if let Some(old_loan_set) = old_loan_set {
                                assert_eq!(&old_loan_set, loan_set);
                            }
                        }
                    }
                }
                let drop_loan_live_at = output_facts.loan_live_at[&drop_point].clone();
                let target_loan_live_at = output_facts.loan_live_at.get_mut(&target_point).unwrap();
                target_loan_live_at.extend(drop_loan_live_at);
            };
            let mut copy_to_location = |location: mir::Location| {
                copy_to_point(location_table.location_to_point(RichLocation::Start(location)));
                copy_to_point(location_table.location_to_point(RichLocation::Mid(location)));
            };
            // Note: This code assumes that the desugaring of `DropAndReplace`
            // on both target and unwinding paths have a single statement that
            // does the replace. This is asserted in
            // prusti-interface/src/environment/mir_body/borrowck/facts/replace_terminator.rs
            copy_to_location(mir::Location {
                block: target_block,
                statement_index: 0,
            });
            copy_to_location(mir::Location {
                block: target_block,
                statement_index: 1,
            });
            copy_to_location(mir::Location {
                block: unwinding_block,
                statement_index: 0,
            });
            copy_to_location(mir::Location {
                block: unwinding_block,
                statement_index: 1,
            });
        }
        let mut lifetimes = Self {
            facts: BorrowckFacts::new(input_facts, output_facts, location_table),
            ignored_loans: BTreeSet::new(),
        };
        {
            // Compute the successfully killed loans.
            let all_locations: Vec<_> = lifetimes.facts.location_table.iter_locations().collect();
            for location in all_locations {
                let killed_loans = lifetimes.get_loan_successfully_killed_at(location);
                lifetimes.ignored_loans.extend(killed_loans);
            }
        }
        {
            // Compute the loans that outlive the function.
            let entry_loans = lifetimes.get_loan_live_at(RichLocation::Start(mir::Location {
                block: entry_block,
                statement_index: 0,
            }));
            let mut exit_locations = Vec::new();
            for (block, data) in body.basic_blocks.iter_enumerated() {
                match data.terminator().kind {
                    mir::TerminatorKind::Goto { .. }
                    | mir::TerminatorKind::SwitchInt { .. }
                    | mir::TerminatorKind::Drop { .. }
                    | mir::TerminatorKind::Call { .. }
                    | mir::TerminatorKind::Assert { .. }
                    | mir::TerminatorKind::Yield { .. }
                    | mir::TerminatorKind::GeneratorDrop
                    | mir::TerminatorKind::FalseEdge { .. }
                    | mir::TerminatorKind::FalseUnwind { .. }
                    | mir::TerminatorKind::InlineAsm { .. } => {}
                    mir::TerminatorKind::Resume
                    | mir::TerminatorKind::Abort
                    | mir::TerminatorKind::Return
                    | mir::TerminatorKind::Unreachable => {
                        exit_locations.push(mir::Location {
                            block,
                            statement_index: data.statements.len(),
                        });
                    }
                }
            }
            for location in exit_locations {
                let loans = lifetimes.get_loan_live_at(RichLocation::Mid(location));
                for loan in loans {
                    if !entry_loans.contains(&loan) {
                        lifetimes.ignored_loans.insert(loan);
                    }
                }
            }
        }
        lifetimes
    }

    pub fn get_loan_live_at_start(&self, location: mir::Location) -> BTreeSet<String> {
        let info = self.get_loan_live_at(RichLocation::Start(location));
        info.into_iter()
            .map(|x| opaque_lifetime_string(x.index()))
            .collect()
    }

    pub fn get_loan_live_at_mid(&self, location: mir::Location) -> BTreeSet<String> {
        let info = self.get_loan_live_at(RichLocation::Mid(location));
        info.into_iter()
            .map(|x| opaque_lifetime_string(x.index()))
            .collect()
    }

    pub fn get_origin_contains_loan_at_start(
        &self,
        location: mir::Location,
    ) -> BTreeMap<String, BTreeSet<String>> {
        self.get_origin_contains_loan_at_location(RichLocation::Start(location))
    }

    pub fn get_origin_contains_loan_at_mid(
        &self,
        location: mir::Location,
    ) -> BTreeMap<String, BTreeSet<String>> {
        self.get_origin_contains_loan_at_location(RichLocation::Mid(location))
    }

    pub fn get_origin_contains_loan_at_location(
        &self,
        location: RichLocation,
    ) -> BTreeMap<String, BTreeSet<String>> {
        let info = self.get_origin_contains_loan_at(location);
        info.iter()
            .map(|(k, v)| {
                (
                    k.to_text(),
                    v.iter()
                        .map(|x| opaque_lifetime_string(x.index()))
                        .collect(),
                )
            })
            .collect()
    }

    pub fn lifetime_count(&self) -> usize {
        let original_lifetimes_count = self.get_original_lifetimes().len();
        let subset_lifetimes: BTreeSet<Region> = self
            .facts
            .input_facts
            .subset_base
            .iter()
            .flat_map(|&(r1, r2, _)| [r1, r2])
            .collect();
        let opaque_lifetimes_count = self
            .get_opaque_lifetimes_with_inclusions_names()
            .keys()
            .count();
        let subset_lifetimes_count = subset_lifetimes.len();
        original_lifetimes_count + subset_lifetimes_count + opaque_lifetimes_count
    }

    pub fn get_opaque_lifetimes_with_inclusions_names(&self) -> BTreeMap<String, BTreeSet<String>> {
        let opaque_lifetimes = self.get_opaque_lifetimes_with_inclusions();
        let mut result = BTreeMap::new();
        for lifetime_with_inclusions in opaque_lifetimes {
            result.insert(
                lifetime_with_inclusions.lifetime.to_text(),
                lifetime_with_inclusions
                    .included_in
                    .iter()
                    .map(|x| x.to_text())
                    .collect(),
            );
        }
        result
    }

    pub fn get_opaque_lifetimes_with_names(&self) -> Vec<String> {
        self.facts
            .input_facts
            .placeholder
            .iter()
            .map(|(_, loan)| opaque_lifetime_string(loan.index()))
            .collect()
    }

    fn get_original_lifetimes(&self) -> Vec<Region> {
        self.facts
            .input_facts
            .loan_issued_at
            .iter()
            .map(|(region, _, _)| *region)
            .collect()
    }

    fn location_to_point(&self, location: RichLocation) -> Point {
        self.facts.location_table.location_to_point(location)
    }

    fn get_loan_live_at(&self, location: RichLocation) -> Vec<Loan> {
        let point = self.location_to_point(location);
        if let Some(loans) = self.facts.output_facts.loan_live_at.get(&point) {
            loans.clone()
        } else {
            Vec::new()
        }
    }

    fn get_loan_killed_at(&self, location: RichLocation) -> Vec<Loan> {
        let point = self.location_to_point(location);
        self.facts
            .input_facts
            .loan_killed_at
            .iter()
            .flat_map(|&(loan, p)| if p == point { Some(loan) } else { None })
            .collect()
    }

    fn get_loan_successfully_killed_at(&self, location: RichLocation) -> Vec<Loan> {
        let live_loans = self.get_loan_live_at(location);
        let killed_loans = self.get_loan_killed_at(location);
        killed_loans
            .into_iter()
            .filter(|killed_loan| live_loans.contains(killed_loan))
            .collect()
    }

    pub fn get_all_ignored_loans(&self) -> Vec<String> {
        self.ignored_loans
            .iter()
            .map(|loan| opaque_lifetime_string(loan.index()))
            .collect()
    }

    fn get_origin_contains_loan_at(
        &self,
        location: RichLocation,
    ) -> BTreeMap<Region, BTreeSet<Loan>> {
        let point = self.location_to_point(location);
        if let Some(map) = self.facts.output_facts.origin_contains_loan_at.get(&point) {
            map.clone()
        } else {
            BTreeMap::new()
        }
    }

    fn get_subset_base(&self, location: RichLocation) -> Vec<(Region, Region)> {
        let point = self.location_to_point(location);
        self.facts
            .input_facts
            .subset_base
            .iter()
            .flat_map(|&(r1, r2, p)| if p == point { Some((r1, r2)) } else { None })
            .collect()
    }

    pub fn get_subset_base_at_start(&self, location: mir::Location) -> Vec<(Region, Region)> {
        let rich_location = RichLocation::Start(location);
        self.get_subset_base(rich_location)
    }

    pub fn get_subset_base_at_mid(&self, location: mir::Location) -> Vec<(Region, Region)> {
        let rich_location = RichLocation::Mid(location);
        self.get_subset_base(rich_location)
    }

    pub fn get_lifetimes_dead_on_edge(&self, from: RichLocation, to: RichLocation) -> Vec<Region> {
        let from_point = self.location_to_point(from);
        let to_point = self.location_to_point(to);
        if let Some(from_origins) = self
            .facts
            .output_facts
            .origin_live_on_entry
            .get(&from_point)
        {
            if let Some(to_origins) = self.facts.output_facts.origin_live_on_entry.get(&to_point) {
                from_origins
                    .iter()
                    .filter(|origin| !to_origins.contains(origin))
                    .cloned()
                    .collect()
            } else {
                from_origins.clone()
            }
        } else {
            Vec::new()
        }
    }

    /// When the Rust compiler generates Polonius facts, it creates many
    /// temporary lifetimes. Sometimes (for example, when encoding the
    /// constructing assignment of the aggregate with a reference-typed field)
    /// we need to unify the lifetimes. This method constructs a map from
    /// lifetimes known to Polonius to `base_lifetimes` indicating with which
    /// `base_lifetimes` the lifetimes could be replaced.
    pub fn construct_replacement_map(
        &self,
        location: mir::Location,
        base_lifetimes: Vec<LifetimeConst>,
    ) -> BTreeMap<LifetimeConst, LifetimeConst> {
        let mut map = BTreeMap::new();
        fn to_lifetime(region: Region) -> LifetimeConst {
            LifetimeConst::new(region.to_text())
        }
        let subset_base = self.get_subset_base_at_mid(location);
        for lifetime in &base_lifetimes {
            map.insert(lifetime.clone(), lifetime.clone());
        }
        let mut changed = true;
        while changed {
            changed = false;
            for (constrained_lifetime, constraining_lifetime) in &subset_base {
                let constrained_lifetime = to_lifetime(*constrained_lifetime);
                let constraining_lifetime = to_lifetime(*constraining_lifetime);
                if !map.contains_key(&constrained_lifetime) {
                    if let Some(constraining_base_lifetime) = map.get(&constraining_lifetime) {
                        map.insert(constrained_lifetime, constraining_base_lifetime.clone());
                        changed = true;
                    }
                }
            }
        }
        map
    }
}
