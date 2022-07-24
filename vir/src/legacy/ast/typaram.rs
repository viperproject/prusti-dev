// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use log::trace;
use regex::Regex;
use std::collections::HashMap;

pub struct Substs {
    regex: Regex,
    repls: HashMap<String, String>,
}

impl std::fmt::Debug for Substs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Substs")
            .field("repls", &self.repls)
            .finish()
    }
}

fn escape_dollars(s: &str) -> String {
    s.replace('$', "\\$")
}

impl Substs {
    /// Takes the string representation of two types: `from` is the generic one; `to` is the more
    /// concrete one.
    /// This function will compute what is the type substitution needed to go from `from` to `to`.
    pub fn learn(from: &str, to: &str) -> Self {
        lazy_static::lazy_static! {
            static ref TYPARAM_RE: Regex = Regex::new("(__TYPARAM__\\$(.*?)\\$__)").unwrap();
        }

        // Start with an empty `repls_regex`
        let mut repls_regex_str = String::new();
        repls_regex_str.push('^');

        // Extract the name of type parameters from the `from` string
        let mut found_typarams = Vec::new();
        let mut last = 0;
        for matched_item in TYPARAM_RE.find_iter(from) {
            repls_regex_str.push_str(&escape_dollars(&from[last..matched_item.start()]));
            repls_regex_str.push_str("(.*?)");
            found_typarams.push(matched_item.as_str().to_string());
            last = matched_item.end();
        }

        repls_regex_str.push_str(&escape_dollars(&from[last..]));
        repls_regex_str.push('$');
        let repls_regex = Regex::new(&repls_regex_str).unwrap();

        // Early return for simple case
        if from == to {
            return Substs {
                regex: TYPARAM_RE.clone(),
                repls: found_typarams.into_iter().map(|x| (x.clone(), x)).collect(),
            };
        }

        // Use `repls_regex` to find typaram replacements
        let mut repls = HashMap::new();
        trace!("regex {:?} from {:?} to {:?}", repls_regex, from, to);
        let captures = repls_regex.captures(to).unwrap();
        for i in 1..captures.len() {
            let from_typaram = found_typarams[i - 1].to_string();
            let to_typaram = captures.get(i).unwrap().as_str();
            let old_entry = repls.insert(from_typaram.clone(), to_typaram.to_string());
            // What if there was something in `repls`? Check that we didn't change it.
            if let Some(x) = old_entry {
                assert!(
                    to == x,
                    "Error in learn({:?}, {:?}). from_typaram: {:?}, to_typaram: {:?}, old_entry: {:?}, repls_regex_str: {:?}",
                    from,
                    to,
                    from_typaram,
                    to_typaram,
                    Some(x),
                    repls_regex_str
                );
            }
        }
        Substs {
            regex: TYPARAM_RE.clone(),
            repls,
        }
    }

    pub fn apply(&self, inner1: &str) -> String {
        let mut newstr = String::new();
        let mut last = 0;
        for matsh in self.regex.find_iter(inner1) {
            newstr.push_str(&inner1[last..matsh.start()]);
            if let Some(rep) = self.repls.get(matsh.as_str()) {
                newstr.push_str(rep);
            } else {
                newstr.push_str(matsh.as_str());
            }
            last = matsh.end();
        }
        newstr.push_str(&inner1[last..]);
        newstr
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test(outer1: &str, outer2: &str, inner1: &str, inner2: &str) {
        let substs = Substs::learn(outer1, outer2);
        let inner2_gen = substs.apply(inner1);
        assert_eq!(inner2_gen, inner2);
    }

    #[test]
    pub fn test1() {
        let outer1 =
            "ref$m_generics_basic_3$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$Y$__$_end_";
        let outer2 =
            "ref$m_generics_basic_3$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$Z$__$_end_";
        let inner1 = "m_generics_basic_3$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$Y$__$_end_";
        let inner2 = "m_generics_basic_3$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$Z$__$_end_";
        test(outer1, outer2, inner1, inner2);
    }

    #[test]
    fn test2() {
        let outer1 = "ref$m_generics_basic_7$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$A$__$_sep_$__TYPARAM__$B$__$_end_";
        let outer2 = "ref$m_generics_basic_7$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$B$__$_sep_$__TYPARAM__$A$__$_end_";
        let inner1 = "m_generics_basic_7$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$A$__$_sep_$__TYPARAM__$B$__$_end_";
        let inner2 = "m_generics_basic_7$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$B$__$_sep_$__TYPARAM__$A$__$_end_";
        test(outer1, outer2, inner1, inner2);
    }

    #[test]
    fn test3() {
        let outer1 = "m_generics_basic_6$$Foo$opensqu$0$closesqu$$_beg_$__TYPARAM__$C$__$_end_";
        let outer2 = "m_generics_basic_6$$Foo$opensqu$0$closesqu$$_beg_$u128$_end_";
        let inner1 = "m_generics_basic_6$$BarBaz$opensqu$0$closesqu$$_beg_$__TYPARAM__$C$__$_end_";
        let inner2 = "m_generics_basic_6$$BarBaz$opensqu$0$closesqu$$_beg_$u128$_end_";
        test(outer1, outer2, inner1, inner2);
    }

    #[test]
    fn test4() {
        let outer1 = "ref$m_generics_basic_4$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$A$__$_sep_$__TYPARAM__$B$__$_end_";
        let outer2 = "ref$m_generics_basic_4$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$C$__$_sep_$i16$_end_";
        let inner1 = "m_generics_basic_4$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$A$__$_sep_$__TYPARAM__$B$__$_end_";
        let inner2 =
            "m_generics_basic_4$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$C$__$_sep_$i16$_end_";
        test(outer1, outer2, inner1, inner2);
    }

    #[test]
    fn test5() {
        let outer1 = "ref$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$A$__$_sep_$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$B$__$_sep_$i32$_sep_$__TYPARAM__$C$__$_end_$_sep_$__TYPARAM__$D$__$_end_";
        let outer2 = "ref$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$i8$_sep_$i32$_sep_$u8$_end_$_sep_$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$i16$_sep_$i32$_sep_$i64$_end_$_sep_$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$isize$_sep_$i32$_sep_$usize$_end_$_end_";
        let inner1 = "m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$B$__$_sep_$i32$_sep_$__TYPARAM__$C$__$_end_";
        let inner2 =
            "m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$i16$_sep_$i32$_sep_$i64$_end_";
        test(outer1, outer2, inner1, inner2);
    }

    #[test]
    fn test6() {
        let outer1 = "ref$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$A$__$_sep_$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$B$__$_sep_$i32$_sep_$__TYPARAM__$C$__$_end_$_sep_$__TYPARAM__$D$__$_end_";
        let outer2 = "ref$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$i8$_sep_$i32$_sep_$u8$_end_$_sep_$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$i16$_sep_$i32$_sep_$i64$_end_$_sep_$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$isize$_sep_$i32$_sep_$usize$_end_$_end_";
        let inner1 = "m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$A$__$_sep_$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$__TYPARAM__$B$__$_sep_$i32$_sep_$__TYPARAM__$C$__$_end_$_sep_$__TYPARAM__$D$__$_end_";
        let inner2 = "m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$i8$_sep_$i32$_sep_$u8$_end_$_sep_$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$i16$_sep_$i32$_sep_$i64$_end_$_sep_$m_generics_basic_5$$Number$opensqu$0$closesqu$$_beg_$isize$_sep_$i32$_sep_$usize$_end_$_end_";
        test(outer1, outer2, inner1, inner2);
    }

    #[test]
    pub fn test7() {
        let outer1 = "tuple2$__TYPARAM__$T$__$__TYPARAM__$T$__";
        let outer2 = "tuple2$__TYPARAM__$T$__$__TYPARAM__$T$__";
        let inner1 = "tuple2$__TYPARAM__$T$__$__TYPARAM__$T$__";
        let inner2 = "tuple2$__TYPARAM__$T$__$__TYPARAM__$T$__";
        test(outer1, outer2, inner1, inner2);
    }
}
