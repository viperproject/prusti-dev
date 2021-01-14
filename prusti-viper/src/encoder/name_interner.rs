// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{HashMap, HashSet};
use log::debug;

/// Name interner.
/// This structure can be used to shorten long unique names without losing the uniqueness property.
#[derive(Debug)]
pub struct NameInterner {
    name_to_symbol: HashMap<String, String>,
    used_symbols: HashSet<String>,
}

impl NameInterner {
    pub fn new() -> Self {
        NameInterner {
            name_to_symbol: HashMap::new(),
            used_symbols: HashSet::new(),
        }
    }

    /// Intern a full unique name, returning a possibly readable string that uniquely identifies it.
    /// The `readable_names` must not collide with past or future `full_unique_name`s.
    pub fn intern<S: ToString>(&mut self, full_unique_name: S, readable_names: &[S]) -> String {
        let full_unique_name = full_unique_name.to_string();
        let readable_names: Vec<_> = readable_names.iter().map(|s| s.to_string()).collect();
        debug_assert!(!readable_names.contains(&"".to_string()));

        // Return the symbol, if we already interned the full name
        if let Some(symbol) = self.name_to_symbol.get(&full_unique_name) {
            debug!("Interning of {:?} is {:?}", &full_unique_name, symbol);
            return symbol.clone();
        }

        // Check that the readable name is not equal to full names passed in the past.
        debug_assert!(!readable_names.iter().any(|r| self.name_to_symbol.contains_key(r)));

        // Check that readable names passed in the past are not equal to the current full name.
        debug_assert!(!self.used_symbols.contains(&full_unique_name));

        let symbol = readable_names.into_iter()
            .find(|r| !self.used_symbols.contains(r))
            .unwrap_or(full_unique_name.clone());
        debug!("Interning of {:?} is {:?}", &full_unique_name, symbol);
        self.used_symbols.insert(symbol.clone());
        self.name_to_symbol.insert(full_unique_name, symbol.clone());

        symbol
    }
}

impl Default for NameInterner {
    fn default() -> Self {
        NameInterner::new()
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_name_interner() {
        let mut interner = NameInterner::new();
        assert_eq!(interner.intern("unreadable$name", &["name"]), "name");
        assert_eq!(interner.intern("unreadable$name", &["name"]), "name");
        assert_eq!(interner.intern("another$name", &["name"]), "another$name");
        assert_eq!(interner.intern("another$name", &["name"]), "another$name");
        assert_eq!(interner.intern("unreadable$name", &["name"]), "name");
        assert_eq!(interner.intern("another$name", &["name"]), "another$name");
        assert_eq!(interner.intern("third$name", &["third"]), "third");
        assert_eq!(interner.intern("unreadable$name", &["name"]), "name");
        assert_eq!(interner.intern("another$name", &["name"]), "another$name");
        assert_eq!(interner.intern("third$name", &["third"]), "third");
    }

    #[test]
    fn test_multiple_readable_names() {
        let mut interner = NameInterner::new();
        assert_eq!(interner.intern("my$first$name", &["name", "first$name"]), "name");
        assert_eq!(interner.intern("my$first$name", &["name", "first$name"]), "name");
        assert_eq!(interner.intern("my$second$name", &["name", "second$name"]), "second$name");
        assert_eq!(interner.intern("my$second$name", &[]), "second$name");
        assert_eq!(interner.intern("my$first$name", &["name", "first$name"]), "name");
        assert_eq!(interner.intern("my$third$name", &["name", "third$name"]), "third$name");
        assert_eq!(interner.intern("another$second$name", &["name", "second$name"]), "another$second$name");
        assert_eq!(interner.intern("my$second$name", &[]), "second$name");
    }

    #[test]
    #[should_panic]
    fn test_readable_name_eq_past_full_name_1() {
        let mut interner = NameInterner::new();
        assert_eq!(interner.intern("first", &["name"]), "name");
        // The readable name is one of the past full names
        let _ = interner.intern("second", &["first"]);
    }

    #[test]
    #[should_panic]
    fn test_readable_name_eq_past_full_name_2() {
        let mut interner = NameInterner::new();
        assert_eq!(interner.intern("first", &["first"]), "first");
        // The readable name is one of the past full names
        let _ = interner.intern("second", &["first"]);
    }

    #[test]
    #[should_panic]
    fn test_readable_name_eq_future_full_name() {
        let mut interner = NameInterner::new();
        // The readable name is one of the future full names
        assert_eq!(interner.intern("first", &["second"]), "second");
        let _ = interner.intern("second", &["name"]);
    }

    #[test]
    #[should_panic]
    fn test_empty_readable_name() {
        let mut interner = NameInterner::new();
        // The readable name is empty
        let _ = interner.intern("second", &[""]);
    }
}
