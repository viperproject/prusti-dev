use super::{
    super::facts::{Loan, Point, Region, RichLocation},
    LifetimeWithInclusions, Lifetimes,
};
use crate::environment::debug_utils::to_text::{loan_to_text, to_sorted_text, ToText};
use std::collections::{BTreeMap, BTreeSet};

impl super::graphviz::ToText for LifetimeWithInclusions {
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

/// Functionality used only for the Graphviz output.
pub trait LifetimesGraphviz {
    fn get_cfg_incoming(&self, point: Point) -> Vec<Point>;
    fn get_cfg_outgoing(&self, point: Point) -> Vec<Point>;
    fn get_opaque_lifetimes_with_inclusions(&self) -> Vec<LifetimeWithInclusions>;
    fn get_subset_base(&self, location: RichLocation) -> Vec<(Region, Region)>;
    fn get_subset(&self, location: RichLocation) -> BTreeMap<Region, BTreeSet<Region>>;
    fn get_origin_live_on_entry(&self, location: RichLocation) -> Vec<Region>;
    fn get_original_lifetimes(&self) -> Vec<Region>;
    fn location_to_point(&self, location: RichLocation) -> Point;
    fn get_loan_live_at(&self, location: RichLocation) -> Vec<Loan>;
    fn get_loan_killed_at(&self, location: RichLocation) -> Vec<Loan>;
    fn get_loan_successfully_killed_at(&self, location: RichLocation) -> Vec<Loan>;
    fn get_origin_contains_loan_at(
        &self,
        location: RichLocation,
    ) -> BTreeMap<Region, BTreeSet<Loan>>;
}

impl LifetimesGraphviz for Lifetimes {
    fn get_cfg_incoming(&self, point: Point) -> Vec<Point> {
        self.facts
            .input_facts
            .cfg_edge
            .iter()
            .filter(|(_from, to)| *to == point)
            .map(|(from, _)| *from)
            .collect()
    }

    fn get_cfg_outgoing(&self, point: Point) -> Vec<Point> {
        self.facts
            .input_facts
            .cfg_edge
            .iter()
            .filter(|(from, _to)| *from == point)
            .map(|(_, to)| *to)
            .collect()
    }

    fn get_opaque_lifetimes_with_inclusions(&self) -> Vec<LifetimeWithInclusions> {
        let mut opaque_lifetimes = Vec::new();
        for &(placeholder, loan) in &self.facts.input_facts.placeholder {
            let mut included_in = Vec::new();
            for &(r1, r2) in &self.facts.input_facts.known_placeholder_subset {
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

    fn get_subset_base(&self, location: RichLocation) -> Vec<(Region, Region)> {
        Lifetimes::get_subset_base(self, location)
    }

    fn get_subset(&self, location: RichLocation) -> BTreeMap<Region, BTreeSet<Region>> {
        let point = self.location_to_point(location);
        if let Some(map) = self.facts.output_facts.subset.get(&point) {
            map.clone()
        } else {
            BTreeMap::new()
        }
    }

    fn get_origin_live_on_entry(&self, location: RichLocation) -> Vec<Region> {
        let point = self.location_to_point(location);
        if let Some(origins) = self.facts.output_facts.origin_live_on_entry.get(&point) {
            origins.clone()
        } else {
            Vec::new()
        }
    }

    fn get_original_lifetimes(&self) -> Vec<Region> {
        Lifetimes::get_original_lifetimes(self)
    }

    fn location_to_point(&self, location: RichLocation) -> Point {
        Lifetimes::location_to_point(self, location)
    }

    fn get_loan_live_at(&self, location: RichLocation) -> Vec<Loan> {
        Lifetimes::get_loan_live_at(self, location)
    }

    fn get_loan_killed_at(&self, location: RichLocation) -> Vec<Loan> {
        Lifetimes::get_loan_killed_at(self, location)
    }

    fn get_loan_successfully_killed_at(&self, location: RichLocation) -> Vec<Loan> {
        Lifetimes::get_loan_successfully_killed_at(self, location)
    }

    fn get_origin_contains_loan_at(
        &self,
        location: RichLocation,
    ) -> BTreeMap<Region, BTreeSet<Loan>> {
        Lifetimes::get_origin_contains_loan_at(self, location)
    }
}
