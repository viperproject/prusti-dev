use serde::{Serialize, Deserialize};

use crate::VirCtxt;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Serialize, Deserialize, Hash)]
#[serde(transparent)]
pub struct ViperIdent<'vir>(#[serde(with = "crate::serde::serde_str")] &'vir str);

impl Display for ViperIdent<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl <'vir> ViperIdent<'vir> {

    pub fn new(ident: &'vir str) -> ViperIdent<'vir> {
        assert!(is_valid_identifier(ident));
        ViperIdent(ident)
    }

    pub fn sanitize(vcx: &'vir VirCtxt<'_>,  ident: String) -> ViperIdent<'vir> {
        let ident = sanitize_str(&ident);
        // Just a sanity check, if this fails there is a problem in `sanitize`
        assert!(is_valid_identifier(ident.as_str()));
        ViperIdent(vcx.alloc_str(&ident))
    }

    pub fn to_str(&self) -> &'vir str {
        self.0
    }
}
fn sanitize_char(c: char) -> Option<String> {
    match c {
        '<' => Some("$lt$".to_string()),
        '>' => Some("$gt$".to_string()),
        ' ' => Some("$space$".to_string()),
        ',' => Some("$comma$".to_string()),
        ':' => Some("$colon$".to_string()),
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
