// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt::Debug;

use rustc_hash::{FxHashMap, FxHashSet};

/// Name interner.
/// This structure can be used to shorten long unique names without losing the uniqueness property.
#[derive(Debug)]
pub struct NameInterner {
    name_to_symbol: FxHashMap<String, String>,
    used_symbols: FxHashSet<String>,
}

impl NameInterner {
    pub fn new() -> Self {
        NameInterner {
            name_to_symbol: FxHashMap::default(),
            used_symbols: FxHashSet::default(),
        }
    }

    /// Intern a full unique name, returning a possibly readable string that uniquely identifies it.
    /// The `readable_names` must not collide with past or future `full_unique_name`s, except for
    /// the `full_unique_name` passed in the same call.
    #[tracing::instrument(level = "debug", skip(self), ret)]
    pub fn intern<S: AsRef<str> + Debug>(
        &mut self,
        full_unique_name: S,
        readable_names: &[S],
    ) -> String {
        let full_unique_name = full_unique_name.as_ref();

        debug_assert!(!readable_names.iter().any(|r| r.as_ref() == ""));

        // Check that the readable name is not equal to full names passed in the past.
        debug_assert!(!readable_names.iter().any(
            |r| r.as_ref() != full_unique_name && self.name_to_symbol.contains_key(r.as_ref())
        ));

        // Check that readable names passed in the past are not equal to the current full name.
        debug_assert!(
            self.name_to_symbol.contains_key(full_unique_name)
                || !self.used_symbols.contains(full_unique_name)
        );

        // Return the symbol, if we already interned the full name
        if let Some(symbol) = self.name_to_symbol.get(full_unique_name) {
            return symbol.clone();
        }

        let symbol = readable_names
            .iter()
            .find(|r| !self.used_symbols.contains(r.as_ref()))
            .map(|r| r.as_ref())
            .unwrap_or(full_unique_name);
        self.used_symbols.insert(symbol.to_string());
        self.name_to_symbol
            .insert(full_unique_name.to_string(), symbol.to_string());

        symbol.to_string()
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
    fn test_full_name_eq_readable_names() {
        let mut interner = NameInterner::new();
        assert_eq!(
            interner.intern("my$first$name", &["my$first$name"]),
            "my$first$name"
        );
    }

    #[test]
    fn test_no_readable_names() {
        let mut interner = NameInterner::new();
        assert_eq!(interner.intern("first", &[]), "first");
        assert_eq!(interner.intern("second", &[]), "second");
        assert_eq!(interner.intern("second", &[]), "second");
    }

    #[test]
    fn test_multiple_readable_names() {
        let mut interner = NameInterner::new();
        assert_eq!(
            interner.intern("my$first$name", &["name", "first$name"]),
            "name"
        );
        assert_eq!(
            interner.intern("my$first$name", &["name", "first$name"]),
            "name"
        );
        assert_eq!(
            interner.intern("my$second$name", &["name", "second$name"]),
            "second$name"
        );
        assert_eq!(interner.intern("my$second$name", &[]), "second$name");
        assert_eq!(
            interner.intern("my$first$name", &["name", "first$name"]),
            "name"
        );
        assert_eq!(
            interner.intern("my$third$name", &["name", "third$name"]),
            "third$name"
        );
        assert_eq!(
            interner.intern("another$second$name", &["name", "second$name"]),
            "another$second$name"
        );
        assert_eq!(interner.intern("my$second$name", &[]), "second$name");
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn test_readable_name_eq_past_full_name_1() {
        let mut interner = NameInterner::new();
        assert_eq!(interner.intern("first", &["name"]), "name");
        // The readable name is one of the past full names
        let _ = interner.intern("second", &["first"]);
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn test_readable_name_eq_past_full_name_2() {
        let mut interner = NameInterner::new();
        assert_eq!(interner.intern("first", &["first"]), "first");
        // The readable name is one of the past full names
        let _ = interner.intern("second", &["first"]);
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn test_readable_name_eq_future_full_name() {
        let mut interner = NameInterner::new();
        // The readable name is one of the future full names
        assert_eq!(interner.intern("first", &["second"]), "second");
        let _ = interner.intern("second", &["name"]);
    }

    #[test]
    #[should_panic]
    #[cfg(debug_assertions)]
    fn test_empty_readable_name() {
        let mut interner = NameInterner::new();
        // The readable name is empty
        let _ = interner.intern("second", &[""]);
    }
}
