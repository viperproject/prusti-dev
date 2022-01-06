// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use vir_crate::polymorphic::NameHash;
use prusti_common::config;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use rustc_hir::definitions::DefPath;
use rustc_hir::def_id::DefPathHash;
use std::fmt;
use log::debug;

// Tracks if crate-unqiue and module-unique names are needed to ensure uniqueness
#[derive(Debug)]
struct ShortName {
    prefix: String,
    project_unique: (bool, String),
    crate_unique: (bool, String),
    mod_unique: (bool, String),
    short_name: String,
}
impl fmt::Display for ShortName {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.prefix);
        if !self.project_unique.0 {
            write!(f, "{}::", self.project_unique.1);
        }
        if !self.crate_unique.0 {
            write!(f, "{}::", self.crate_unique.1);
        }
        if !self.mod_unique.0 {
            write!(f, "{}::", self.mod_unique.1);
        }
        write!(f, "{}", self.short_name)
    }
}
impl ShortName {
    fn update(&mut self, other: &mut Self) {
        if self.short_name == other.short_name && self.prefix == other.prefix {
            if self.project_unique.1 != other.project_unique.1 {
                self.project_unique.0 = false;
                other.project_unique.0 = false;
            } else if self.crate_unique.1 != other.crate_unique.1 {
                self.crate_unique.0 = false;
                other.crate_unique.0 = false;
            } else if self.mod_unique.1 != other.mod_unique.1 {
                self.mod_unique.0 = false;
                other.mod_unique.0 = false;
            } else {
                panic!("Have been given two identical names: {:?}", self);
            }
        }
    }
}

/// Name interner.
/// This structure can be used to shorten long unique names without losing the uniqueness property.
pub struct NameInterner {
    name_to_short: HashMap<NameHash, ShortName>,
    locked: bool,
}

impl NameInterner {
    pub fn new() -> Self {
        NameInterner {
            name_to_short: HashMap::default(),
            locked: false,
        }
    }

    /// Intern a full unique name, returning a possibly readable string that uniquely identifies it.
    pub fn intern(&mut self, prefix: &str, def_id: DefId, tcx: TyCtxt) -> NameHash {
        let def_path = tcx.def_path(def_id);
        // The `to_string` gives each `DisambiguatedDefPathData` separated by "::"
        let crate_name = tcx.crate_name(def_path.krate).to_string();
        // Assume that the friendly `tcx.opt_item_name` is the last one, use second-to-last as the mod unique, and others as crate unique.
        let item_name = def_path.to_string_no_crate_verbose().rsplitn(3, "::");
        let short_name = item_name.next().unwrap_or_default();
        let mod_unique = item_name.next().unwrap_or_default();
        // TODO: How does this work when we have a crate with multiple files
        let crate_unique = item_name.next().unwrap_or_default();

        let path_hash = tcx.def_path_hash(def_id);
        let key = NameHash::new(path_hash.stable_crate_id().to_u64(), path_hash.local_hash());
        let name = self.intern_name(prefix.to_string(), crate_name, crate_unique, mod_unique, short_name);
        // Uniqueness is ensured by `ShortName::update`; `Some` indicates a clash of the Hash
        let old = self.name_to_short.insert(key, name);
        assert!(old.is_none(), "Two name hashes have clashed! This is exceedingly rare");
    }

    fn intern_name(&mut self, prefix: String, project_unique: String, crate_unique: String, mod_unique: String, short_name: String) -> ShortName {
        if self.locked {
            let full_name = format!("{}{}::{}::{}::{}", prefix, project_unique, crate_unique, mod_unique, short_name);
            let short_name = format!("{}{}", prefix, short_name);
            panic!(
                "Attempting to add {} to the `NameInterner` after names have been read out, \
                this could invalidate these names if they clash with {}!",
                full_name,
                short_name
            );
        }
        let can_be_unqiue = config::disable_name_mangling() || config::intern_names();
        let mut name = ShortName {
            prefix,
            // If name_mangling is enabled but `!intern_names`, assume nothing is unique:
            // `!crate_unique.0` and `!mod_unique.0`
            project_unique: (can_be_unqiue, crate_name),
            crate_unique: (can_be_unqiue, crate_unique),
            mod_unique: (can_be_unqiue, mod_unique),
            short_name,
        };
        // Intern mangled names only if `enable_name_mangling && intern_names`
        if !config::disable_name_mangling() && config::intern_names() {
            for (_, mut value) in self.name_to_short {
                value.update(&mut name);
            }
        }
        name
    }

    pub fn get_interned(&mut self, full_name: &NameHash) -> String {
        self.locked = true;
        self.name_to_short.get(full_name).unwrap().to_string()
    }
}

impl Default for NameInterner {
    fn default() -> Self {
        NameInterner::new()
    }
}

/*
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
        assert_eq!(interner.intern("my$first$name", &["my$first$name"]), "my$first$name");
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
*/
