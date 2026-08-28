use prusti_rustc_interface::{hir::definitions::DefPathData, span::def_id::DefId};
use serde::{Deserialize, Serialize};

use crate::{IdentStyle, VirCtxt};
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Serialize, Deserialize, Hash)]
#[serde(transparent)]
pub struct ViperIdent<'vir>(#[serde(with = "crate::serde::serde_str")] &'vir str);

impl Display for ViperIdent<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<'vir> ViperIdent<'vir> {
    pub fn new(ident: &'vir str) -> ViperIdent<'vir> {
        assert!(is_valid_identifier(ident));
        ViperIdent(ident)
    }

    pub fn sanitize(vcx: &'vir VirCtxt<'_>, ident: &str) -> ViperIdent<'vir> {
        let ident = sanitize_str(ident);
        // Just a sanity check, if this fails there is a problem in `sanitize`
        assert!(is_valid_identifier(ident.as_str()));
        ViperIdent(vcx.alloc_str(&ident))
    }

    /// The identifier fragment naming the Rust item `def_id`. Callers combine
    /// this with a role-specific prefix, e.g.
    /// `vir_format_identifier!(vcx, "m_{}", ViperIdent::from_def_id(vcx, def_id))`.
    pub fn from_def_id(vcx: &'vir VirCtxt<'_>, def_id: DefId) -> ViperIdent<'vir> {
        let name = match vcx.ident_style {
            IdentStyle::DefPath => vcx.tcx().def_path_str(def_id),
            IdentStyle::ItemName => short_name(vcx, def_id),
        };
        Self::sanitize(vcx, &name)
    }

    pub fn to_str(&self) -> &'vir str {
        self.0
    }
}

/// Asking for the `item_name` of a closure triggers an ICE in the compiler, so
/// a closure is named after its nearest non-closure ancestor (closures can
/// nest, e.g. a quantifier's closure inside an assertion's closure).
fn short_name(vcx: &VirCtxt<'_>, mut def_id: DefId) -> String {
    let mut key = vcx.tcx().def_key(def_id);
    let mut suffix = String::new();
    while let DefPathData::Closure = key.disambiguated_data.data {
        suffix = format!("_Closure_{}{suffix}", key.disambiguated_data.disambiguator);
        def_id.index = key.parent.unwrap();
        key = vcx.tcx().def_key(def_id);
    }
    format!("{}{suffix}", vcx.tcx().item_name(def_id).to_ident_string())
}

fn sanitize_char(c: char) -> Option<String> {
    match c {
        '<' => Some("$lt$".to_string()),
        '>' => Some("$gt$".to_string()),
        ' ' => Some("$sp$".to_string()),
        ',' => Some("$com$".to_string()),
        ':' => Some("$col$".to_string()),
        '\'' => Some("$sq$".to_string()),
        '&' => Some("$amp$".to_string()),
        '-' => Some("$hyp$".to_string()),
        '(' => Some("$lp$".to_string()),
        ')' => Some("$rp$".to_string()),
        '[' => Some("$lb$".to_string()),
        ']' => Some("$rb$".to_string()),
        '{' => Some("$lc$".to_string()),
        '}' => Some("$rc$".to_string()),
        '?' => Some("$qm$".to_string()),
        ';' => Some("$sc$".to_string()),
        '#' => Some("$oc$".to_string()),
        '/' => Some("$fs$".to_string()),
        '*' => Some("$as$".to_string()),
        '=' => Some("$eq$".to_string()),
        '+' => Some("$pl$".to_string()),
        '!' => Some("$ex$".to_string()),
        _ => None,
    }
}

fn sanitize_str(s: &str) -> String {
    s.chars()
        .map(|c| sanitize_char(c).unwrap_or_else(|| c.to_string()))
        .collect()
}

fn is_valid_identifier(s: &str) -> bool {
    s.chars().all(|c| sanitize_char(c).is_none())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Call sites compose sanitized fragments into larger identifiers with
    /// `vir_format_identifier!`, which sanitizes again; that must be a no-op.
    #[test]
    fn sanitize_is_idempotent() {
        let path = "<core::ops::Range<T> as Foo>::bar::{closure#0}";
        let once = sanitize_str(path);
        assert!(is_valid_identifier(&once));
        assert_eq!(sanitize_str(&once), once);
    }
}
