// FIXME: Delete this file.

use crate::environment::{
    borrowck::facts::{AllInputFacts, AllOutputFacts, BorrowckFacts, Loan, PointIndex, Region},
    mir_dump::graphviz::{loan_to_text, opaque_lifetime_string, to_sorted_text, ToText},
};
use rustc_borrowck::consumers::{LocationTable, RichLocation};
use std::{
    cell::Ref,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use rustc_middle::mir;

pub struct Lifetimes {
    facts: Rc<BorrowckFacts>,
    output_facts: AllOutputFacts,
}

pub(super) struct LifetimeWithInclusions {
    lifetime: Region,
    loan: Loan,
    included_in: Vec<Region>,
}

impl super::graphviz::ToText for super::lifetimes::LifetimeWithInclusions {
    fn to_text(&self) -> String {
        let lifetimes = to_sorted_text(&self.included_in);
        format!(
            "{} ⊑ {} ({})",
            self.lifetime.to_text(),
            lifetimes.join(" ⊓ "),
            loan_to_text(&self.loan)
        )
    }
}

impl Lifetimes {
    pub fn new(facts: Rc<BorrowckFacts>) -> Self {
        let output_facts = polonius_engine::Output::compute(
            facts.input_facts.borrow().as_ref().unwrap(),
            polonius_engine::Algorithm::Naive,
            true,
        );
        Self {
            facts,
            output_facts,
        }
    }
    pub fn get_loan_live_at_start(&self, location: mir::Location) -> BTreeSet<String> {
        let info = self.get_loan_live_at(RichLocation::Start(location));
        info.into_iter()
            .map(|x| opaque_lifetime_string(x.index()))
            .collect()
    }
    pub fn get_origin_contains_loan_at_mid(
        &self,
        location: mir::Location,
    ) -> BTreeMap<String, BTreeSet<String>> {
        let info = self.get_origin_contains_loan_at(RichLocation::Mid(location));
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
        let borrowck_in_facts = self.borrowck_in_facts();
        let subset_lifetimes: BTreeSet<Region> = borrowck_in_facts
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
    pub fn get_subset_base_at_start(&self, location: mir::Location) -> Vec<(Region, Region)> {
        let rich_location = RichLocation::Start(location);
        self.get_subset_base(rich_location)
    }
    pub fn get_subset_base_at_mid(&self, location: mir::Location) -> Vec<(Region, Region)> {
        let rich_location = RichLocation::Mid(location);
        self.get_subset_base(rich_location)
    }
    fn borrowck_in_facts(&self) -> Ref<AllInputFacts> {
        Ref::map(self.facts.input_facts.borrow(), |facts| {
            facts.as_ref().unwrap()
        })
    }
    fn borrowck_out_facts(&self) -> &AllOutputFacts {
        &self.output_facts
    }
    fn location_table(&self) -> Ref<LocationTable> {
        Ref::map(self.facts.location_table.borrow(), |table| {
            table.as_ref().unwrap()
        })
    }
    pub(super) fn debug_borrowck_in_facts(&self) {
        eprintln!("{:?}", self.borrowck_in_facts());
    }
    pub(super) fn debug_borrowck_out_facts(&self) {
        eprintln!("{:?}", self.borrowck_out_facts());
    }
    pub(super) fn get_opaque_lifetimes_with_inclusions(&self) -> Vec<LifetimeWithInclusions> {
        let borrowck_in_facts = self.borrowck_in_facts();
        let mut opaque_lifetimes = Vec::new();
        for &(placeholder, loan) in &borrowck_in_facts.placeholder {
            let mut included_in = Vec::new();
            for &(r1, r2) in &borrowck_in_facts.known_placeholder_subset {
                if r1 == placeholder {
                    included_in.push(r2);
                }
            }
            opaque_lifetimes.push(LifetimeWithInclusions {
                lifetime: placeholder,
                loan,
                included_in,
            });
        }
        opaque_lifetimes
    }
    pub(super) fn get_original_lifetimes(&self) -> Vec<Region> {
        self.borrowck_in_facts()
            .loan_issued_at
            .iter()
            .map(|(region, _, _)| *region)
            .collect()
    }
    pub(super) fn get_subset_base(&self, location: RichLocation) -> Vec<(Region, Region)> {
        let point = self.location_to_point(location);
        let borrowck_in_facts = self.borrowck_in_facts();
        borrowck_in_facts
            .subset_base
            .iter()
            .flat_map(|&(r1, r2, p)| if p == point { Some((r1, r2)) } else { None })
            .collect()
    }
    fn location_to_point(&self, location: RichLocation) -> PointIndex {
        let table = self.location_table();
        match location {
            RichLocation::Start(location) => table.start_index(location),
            RichLocation::Mid(location) => table.mid_index(location),
        }
    }
    pub(super) fn get_subset(&self, location: RichLocation) -> BTreeMap<Region, BTreeSet<Region>> {
        let point = self.location_to_point(location);
        let borrowck_out_facts = self.borrowck_out_facts();
        if let Some(map) = borrowck_out_facts.subset.get(&point) {
            map.clone()
        } else {
            BTreeMap::new()
        }
    }
    pub(super) fn get_origin_live_on_entry(&self, location: RichLocation) -> Vec<Region> {
        let point = self.location_to_point(location);
        let borrowck_out_facts = self.borrowck_out_facts();
        if let Some(origins) = borrowck_out_facts.origin_live_on_entry.get(&point) {
            origins.clone()
        } else {
            Vec::new()
        }
    }
    pub(super) fn get_loan_live_at(&self, location: RichLocation) -> Vec<Loan> {
        let point = self.location_to_point(location);
        let borrowck_out_facts = self.borrowck_out_facts();
        if let Some(loans) = borrowck_out_facts.loan_live_at.get(&point) {
            loans.clone()
        } else {
            Vec::new()
        }
    }
    pub(super) fn get_origin_contains_loan_at(
        &self,
        location: RichLocation,
    ) -> BTreeMap<Region, BTreeSet<Loan>> {
        let point = self.location_to_point(location);
        let borrowck_out_facts = self.borrowck_out_facts();
        if let Some(map) = borrowck_out_facts.origin_contains_loan_at.get(&point) {
            map.clone()
        } else {
            BTreeMap::new()
        }
    }
}
