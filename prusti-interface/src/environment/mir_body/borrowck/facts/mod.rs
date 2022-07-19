use prusti_rustc_interface::{
    borrowck::consumers::RustcFacts, middle::mir, polonius_engine::FactTypes,
};
use rustc_hash::FxHashMap;

pub mod patch;
pub mod validation;

pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type Point = <RustcFacts as FactTypes>::Point;
pub type Variable = <RustcFacts as FactTypes>::Variable;
pub type Path = <RustcFacts as FactTypes>::Path;

pub type AllInputFacts = prusti_rustc_interface::borrowck::consumers::PoloniusInput;
pub type AllOutputFacts = prusti_rustc_interface::borrowck::consumers::PoloniusOutput;

pub struct BorrowckFacts {
    /// Polonius input facts.
    pub input_facts: AllInputFacts,
    /// Polonius output facts.
    pub output_facts: AllOutputFacts,
    /// The table that maps Polonius points to locations in the table.
    pub location_table: LocationTable,
}

impl BorrowckFacts {
    pub fn new(
        input_facts: AllInputFacts,
        output_facts: AllOutputFacts,
        location_table: LocationTable,
    ) -> Self {
        Self {
            input_facts,
            output_facts,
            location_table,
        }
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum RichLocation {
    Start(mir::Location),
    Mid(mir::Location),
}

impl RichLocation {
    fn start(block: mir::BasicBlock, statement_index: usize) -> Self {
        Self::Start(mir::Location {
            block,
            statement_index,
        })
    }

    fn mid(block: mir::BasicBlock, statement_index: usize) -> Self {
        Self::Mid(mir::Location {
            block,
            statement_index,
        })
    }

    pub fn into_inner(self) -> mir::Location {
        match self {
            Self::Start(location) | Self::Mid(location) => location,
        }
    }
}

impl From<prusti_rustc_interface::borrowck::consumers::RichLocation> for RichLocation {
    fn from(location: prusti_rustc_interface::borrowck::consumers::RichLocation) -> Self {
        match location {
            prusti_rustc_interface::borrowck::consumers::RichLocation::Start(l) => {
                RichLocation::Start(l)
            }
            prusti_rustc_interface::borrowck::consumers::RichLocation::Mid(l) => {
                RichLocation::Mid(l)
            }
        }
    }
}

#[derive(Clone)]
pub struct LocationTable {
    /// A map from Polonius points to rich locations.
    locations: FxHashMap<Point, RichLocation>,
    /// A map from rich locations to Polonius points (inverse of locations).
    points: FxHashMap<RichLocation, Point>,
}

impl LocationTable {
    pub fn new(
        location_table: &prusti_rustc_interface::borrowck::consumers::LocationTable,
    ) -> Self {
        let mut locations = FxHashMap::default();
        let mut points = FxHashMap::default();
        for point in location_table.all_points() {
            let location = location_table.to_location(point).into();
            locations.insert(point, location);
            points.insert(location, point);
        }
        Self { locations, points }
    }

    pub fn location_to_point(&self, location: RichLocation) -> Point {
        self.points[&location]
    }
}
