// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.



use prusti_rustc_interface::polonius_engine::FactTypes;
use prusti_rustc_interface::borrowck::consumers::{RustcFacts, LocationTable, RichLocation};
use prusti_rustc_interface::middle::mir;
use std::rc::Rc;
use std::cell::RefCell;

pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type PointIndex = <RustcFacts as FactTypes>::Point;
pub type Variable = <RustcFacts as FactTypes>::Variable;
pub type Path = <RustcFacts as FactTypes>::Path;

pub type AllInputFacts = prusti_rustc_interface::borrowck::consumers::PoloniusInput;
pub type AllOutputFacts = prusti_rustc_interface::borrowck::consumers::PoloniusOutput;

trait LocationTableExt {
    fn to_mir_location(self, point: PointIndex) -> mir::Location;
}

impl LocationTableExt for LocationTable {
    fn to_mir_location(self, point: PointIndex) -> mir::Location {
        match self.to_location(point) {
            RichLocation::Start(location) | RichLocation::Mid(location) => location,
        }
    }
}

pub struct BorrowckFacts {
    /// Polonius input facts.
    pub input_facts: RefCell<Option<AllInputFacts>>,
    /// Polonius output facts.
    pub output_facts: Rc<AllOutputFacts>,
    /// The table that maps Polonius points to locations in the table.
    pub location_table: RefCell<Option<LocationTable>>,
}

/// The type of the point. Either the start of a statement or in the
/// middle of it.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum PointType {
    Start,
    Mid,
}

impl std::cmp::PartialOrd for PointType {
    fn partial_cmp(&self, other: &PointType) -> Option<std::cmp::Ordering> {
        let res = match (self, other) {
            (PointType::Start, PointType::Start) => std::cmp::Ordering::Equal,
            (PointType::Start, PointType::Mid) => std::cmp::Ordering::Less,
            (PointType::Mid, PointType::Start) => std::cmp::Ordering::Greater,
            (PointType::Mid, PointType::Mid) => std::cmp::Ordering::Equal,
        };
        Some(res)
    }
}

impl std::cmp::Ord for PointType {
    fn cmp(&self, other: &PointType) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// A program point used in the borrow checker analysis.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct Point {
    pub location: mir::Location,
    pub typ: PointType,
}

impl std::fmt::Display for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?}:{:?}:{:?}",
            self.location.block,
            self.location.statement_index,
            self.typ
        )
    }
}

pub struct Interner {
    location_table: LocationTable,
}

impl Interner {
    pub fn new(location_table: LocationTable) -> Self {
        Self { location_table }
    }

    pub fn get_point_index(&self, point: &Point) -> PointIndex {
        // self.points.get_index(point)
        match point.typ {
            PointType::Start => self.location_table.start_index(point.location),
            PointType::Mid => self.location_table.mid_index(point.location),
        }
    }

    pub fn get_point(&self, index: PointIndex) -> Point {
        // self.points.get_element(index)
        match self.location_table.to_location(index) {
            RichLocation::Start(location) => {
                Point {
                    location, typ: PointType::Start
                }
            }
            RichLocation::Mid(location) => {
                Point {
                    location, typ: PointType::Mid
                }
            }
        }
    }
}
