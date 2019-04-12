// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::HashSet;
use syntax::codemap::Span;
use serde::ser::{Serialize, Serializer, SerializeStruct};
use std::hash::Hash;

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct Reason {
    /// The reason must be a valid continuation of the sentence
    /// "The following code span is not supported because it..."
    /// E.g. "uses iterators", "is a C-variadic function"
    pub reason: String,
    pub position: Span,
}

impl Reason {
    pub fn new<T: ToString>(reason: T, position: Span) -> Self {
        Reason {
            reason: reason.to_string(),
            position,
        }
    }
}

impl Serialize for Reason {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut rgb = serializer.serialize_struct("Reason", 2)?;
        rgb.serialize_field("reason", &self.reason)?;
        rgb.serialize_field("position", &format!("{:?}", self.position))?;
        rgb.end()
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Serialize)]
/// The restriction kind, with a short explanation that will be displayed to the user.
pub enum Restriction<T: Clone + Eq + PartialEq + Hash + Serialize> {
    PartiallySupported(T),
    Unsupported(T),
}

impl<T: Clone + Eq + PartialEq + Hash + Serialize> Restriction<T> {
    pub fn partially(reason: T) -> Self {
        Restriction::PartiallySupported(reason)
    }

    pub fn unsupported(reason: T) -> Self {
        Restriction::Unsupported(reason)
    }

    pub fn is_partially_supported(&self) -> bool {
        match self {
            Restriction::PartiallySupported(_) => true,
            _ => false
        }
    }

    pub fn is_unsupported(&self) -> bool {
        match self {
            Restriction::Unsupported(_) => true,
            _ => false
        }
    }

    pub fn reason(&self) -> &T {
        match self {
            Restriction::Unsupported(ref reason) |
            Restriction::PartiallySupported(ref reason) => reason,
        }
    }
}

#[derive(Serialize)]
pub struct SupportStatus {
    /// Reasons why the implementation item is unsupported or partially supported
    restrictions: HashSet<Restriction<String>>,
    /// Like restrictions, with with the offending code span
    precise_restrictions: HashSet<Restriction<Reason>>,
    /// Interesting features (e.g. "returns a reference")
    interestings: HashSet<String>,
}

impl SupportStatus {
    pub fn new() -> Self {
        SupportStatus {
            restrictions: HashSet::new(),
            interestings: HashSet::new(),
            precise_restrictions: HashSet::new(),
        }
    }

    pub fn partially(&mut self, reason: Reason) {
        self.restrictions.insert(
            Restriction::PartiallySupported(reason.reason.clone())
        );
        self.precise_restrictions.insert(
            Restriction::PartiallySupported(reason)
        );
    }

    #[allow(dead_code)]
    pub fn unsupported(&mut self, reason: Reason) {
        self.restrictions.insert(
            Restriction::Unsupported(reason.reason.clone())
        );
        self.precise_restrictions.insert(
            Restriction::Unsupported(reason)
        );
    }

    #[allow(dead_code)]
    pub fn interesting<T: ToString>(&mut self, reason: T) {
        self.interestings.insert(reason.to_string());
    }

    pub fn is_supported(&self) -> bool {
        self.precise_restrictions.is_empty()
    }

    pub fn is_partially_supported(&self) -> bool {
        !self.precise_restrictions.is_empty() &&
        self.precise_restrictions.iter()
            .all(|s| s.is_partially_supported())
    }

    #[allow(dead_code)]
    pub fn is_unsupported(&self) -> bool {
        self.precise_restrictions.iter()
            .any(|s| s.is_unsupported())
    }

    pub fn get_partially_supported_reasons(&self) -> Vec<Reason> {
        self.precise_restrictions.iter()
            .filter(|s| s.is_partially_supported())
            .map(|s| s.reason().clone())
            .collect()
    }

    #[allow(dead_code)]
    pub fn get_unsupported_reasons(&self) -> Vec<Reason> {
        self.precise_restrictions.iter()
            .filter(|s| s.is_unsupported())
            .map(|s| s.reason().clone())
            .collect()
    }
}
