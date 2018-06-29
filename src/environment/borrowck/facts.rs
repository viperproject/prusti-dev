// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

/// Code for loading an manipulating Polonius facts.
///
/// This code was adapted from the
/// [Polonius](https://github.com/rust-lang-nursery/polonius/blob/master/src/facts.rs)
/// source code.

use csv::ReaderBuilder;
use regex::Regex;
use rustc::mir;
use rustc_data_structures::indexed_vec::Idx;
use serde::de::DeserializeOwned;
use std::collections::HashMap;
use std::hash::Hash;
use std::path::Path;
use std::str::FromStr;

use polonius_engine;


/// Macro for declaring index types for referencing interned facts.
macro_rules! index_type {
    ($typ:ident) => {
        #[derive(Ord, PartialOrd, Eq, PartialEq, Clone, Copy, Debug, Hash)]
        pub struct $typ(usize);

        impl From<usize> for $typ {
            fn from(index: usize) -> $typ {
                $typ {
                    0: index,
                }
            }
        }

        impl Into<usize> for $typ {
            fn into(self) -> usize {
                self.0 as usize
            }
        }

        impl polonius_engine::Atom for $typ {
            fn index(self) -> usize {
                self.into()
            }
        }
    };
}

index_type!(RegionIndex);
index_type!(LoanIndex);
index_type!(PointIndex);


/// A unique identifier of a region.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Region {
    id: usize,
}

impl FromStr for Region {

    type Err = ();

    fn from_str(region: &str) -> Result<Self, Self::Err> {
        let re = Regex::new(r"^\\'_#(?P<id>\d+)r$").unwrap();
        let caps = re.captures(region).unwrap();
        let id: usize = caps["id"].parse().unwrap();
        Ok(Self {
            id: id,
        })
    }
}

/// A unique identifier of a loan.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Loan {
    id: usize,
}

impl FromStr for Loan {

    type Err = ();

    fn from_str(loan: &str) -> Result<Self, Self::Err> {
        let re = Regex::new(r"^bw(?P<id>\d+)$").unwrap();
        let caps = re.captures(loan).unwrap();
        let id: usize = caps["id"].parse().unwrap();
        Ok(Self {
            id: id,
        })
    }

}

/// The type of the point. Either the start of a statement or in the
/// middle of it.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum PointType {
    Start,
    Mid,
}

#[derive(Debug)]
pub struct UnknownPointTypeError(String);

impl FromStr for PointType {

    type Err = UnknownPointTypeError;

    fn from_str(point_type: &str) -> Result<Self, Self::Err> {
        match point_type {
            "Start" => Ok(PointType::Start),
            "Mid" => Ok(PointType::Mid),
            _ => Err(UnknownPointTypeError(String::from(point_type))),
        }
    }
}

/// A program point used in the borrow checker analysis.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Point {
    pub location: mir::Location,
    pub typ: PointType,
}

impl FromStr for Point {

    type Err = ();

    fn from_str(point: &str) -> Result<Self, Self::Err> {
        let re = Regex::new(r"^(?P<type>Mid|Start)\(bb(?P<bb>\d+)\[(?P<stmt>\d+)\]\)$").unwrap();
        let caps = re.captures(point).unwrap();
        let point_type: PointType = caps["type"].parse().unwrap();
        let basic_block: usize = caps["bb"].parse().unwrap();
        let statement_index: usize = caps["stmt"].parse().unwrap();
        Ok(Self {
            location: mir::Location {
                block: mir::BasicBlock::new(basic_block),
                statement_index: statement_index,
            },
            typ: point_type,
        })
    }

}

pub type AllFacts = polonius_engine::AllFacts<RegionIndex, LoanIndex, PointIndex>;


/// A table that stores a mapping between interned elements of type
/// `SourceType` and their indices.
pub struct InternerTable<SourceType: Eq, IndexType: From<usize> + Copy> {
    /// For looking up from index type to source type.
    interned_elements: Vec<SourceType>,
    /// For looking up from source type into index type.
    index_elements: HashMap<SourceType, IndexType>,
}

impl<SourceType: Eq + Hash + Clone, IndexType: From<usize> + Copy> InternerTable<SourceType, IndexType> {
    fn new() -> Self {
        Self {
            interned_elements: Vec::new(),
            index_elements: HashMap::new(),
        }
    }
    fn get_index(&mut self, element: SourceType) -> IndexType {
        if let Some(&interned) = self.index_elements.get(&element) {
            return interned;
        }

        let index = IndexType::from(self.index_elements.len());
        self.interned_elements.push(element.clone());
        *self.index_elements.entry(element).or_insert(index)
    }
}

trait InternTo<FromType, ToType> {

    fn intern(&mut self, element: FromType) -> ToType;

}

pub struct Interner {
    regions: InternerTable<Region, RegionIndex>,
    loans: InternerTable<Loan, LoanIndex>,
    points: InternerTable<Point, PointIndex>,
}

impl InternTo<String, RegionIndex> for Interner {
    fn intern(&mut self, element: String) -> RegionIndex {
        let region = element.parse().unwrap();
        self.regions.get_index(region)
    }
}

impl InternTo<String, LoanIndex> for Interner {
    fn intern(&mut self, element: String) -> LoanIndex {
        let loan = element.parse().unwrap();
        self.loans.get_index(loan)
    }
}

impl InternTo<String, PointIndex> for Interner {
    fn intern(&mut self, element: String) -> PointIndex {
        let point = element.parse().unwrap();
        self.points.get_index(point)
    }
}

impl<A, B> InternTo<(String, String), (A, B)> for Interner
    where
        Interner: InternTo<String, A>,
        Interner: InternTo<String, B>,
{
    fn intern(&mut self, (e1, e2): (String, String)) -> (A, B) {
        (self.intern(e1), self.intern(e2))
    }
}

impl<A, B, C> InternTo<(String, String, String), (A, B, C)> for Interner
    where
        Interner: InternTo<String, A>,
        Interner: InternTo<String, B>,
        Interner: InternTo<String, C>,
{
    fn intern(&mut self, (e1, e2, e3): (String, String, String)) -> (A, B, C) {
        (self.intern(e1), self.intern(e2), self.intern(e3))
    }
}

fn load_facts_from_file<T: DeserializeOwned>(facts_dir: &Path, facts_type: &str) -> Vec<T> {
    let filename = format!("{}.facts", facts_type);
    let facts_file = facts_dir.join(&filename);
    let mut reader = ReaderBuilder::new()
         .delimiter(b'\t')
         .has_headers(false)
         .from_path(facts_file)
         .unwrap();
    reader
        .deserialize()
        .map(|row| row.unwrap())
        .collect()
}

impl Interner {
    pub fn new() -> Self {
        Self {
            regions: InternerTable::new(),
            loans: InternerTable::new(),
            points: InternerTable::new(),
        }
    }
}

pub struct FactLoader {
    pub interner: Interner,
    pub facts: AllFacts,
}

impl FactLoader {
    pub fn new() -> Self {
        Self {
            interner: Interner::new(),
            facts: AllFacts::default(),
        }
    }
    pub fn load_all_facts(&mut self, facts_dir: &Path) {

        let facts = load_facts::<(String, String, String), _>(&mut self.interner, facts_dir, "borrow_region");
        self.facts.borrow_region.extend(facts);

        let facts = load_facts::<String, RegionIndex>(&mut self.interner, facts_dir, "universal_region");
        self.facts.universal_region.extend(facts);

        let facts = load_facts::<(String, String), _>(&mut self.interner, facts_dir, "cfg_edge");
        self.facts.cfg_edge.extend(facts);

        let facts = load_facts::<(String, String), _>(&mut self.interner, facts_dir, "killed");
        self.facts.killed.extend(facts);

        let facts = load_facts::<(String, String, String), _>(&mut self.interner, facts_dir, "outlives");
        self.facts.outlives.extend(facts);

        let facts = load_facts::<(String, String), _>(&mut self.interner, facts_dir, "region_live_at");
        self.facts.region_live_at.extend(facts);

        let facts = load_facts::<(String, String), _>(&mut self.interner, facts_dir, "invalidates");
        self.facts.invalidates.extend(facts);
    }
}

fn load_facts<F: DeserializeOwned, T>(interner: &mut Interner, facts_dir: &Path, facts_type: &str) -> Vec<T>
    where
        Interner: InternTo<F, T>
{
    load_facts_from_file(facts_dir, facts_type)
        .into_iter()
        .map(|fact| Interner::intern(interner, fact))
        .collect()
}
