// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir;
use std::fmt;
use std::iter::FlatMap;
use std::collections::HashMap;

/// A permission in the current state or in the (old) state of a label
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LabelledPerm {
    Old(String, Perm),
    Curr(Perm)
}

impl LabelledPerm {
    pub fn old(label: &str, perm: Perm) -> Self {
        LabelledPerm::Old(
            label.to_string(),
            perm
        )
    }

    pub fn curr(perm: Perm) -> Self {
        LabelledPerm::Curr(perm)
    }

    pub fn inner(&self) -> &Perm {
        match self {
            LabelledPerm::Old(_, ref perm) |
            LabelledPerm::Curr( ref perm) => perm
        }
    }
}

/// An access or predicate permission to a place
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Perm {
    Acc(vir::Place),
    Pred(vir::Place)
}

impl Perm {
    pub fn is_acc(&self) -> bool {
        match self {
            Perm::Acc(_) => true,
            _ => false,
        }
    }

    pub fn is_pred(&self) -> bool {
        match self {
            Perm::Pred(_) => true,
            _ => false,
        }
    }

    pub fn get_pred(&self) -> Option<&vir::Place> {
        match self {
            Perm::Pred(ref place) => Some(place),
            _ => None,
        }
    }

    pub fn get_place(&self) -> vir::Place {
        match self {
            &Perm::Acc(ref place) |
            &Perm::Pred(ref place) => place.clone(),
        }
    }

    pub fn as_ref(&self) -> &vir::Place {
        match self {
            &Perm::Acc(ref place) |
            &Perm::Pred(ref place) => place,
        }
    }

    pub fn as_mut_ref(&mut self) -> &mut vir::Place {
        match self {
            &mut Perm::Acc(ref mut place) |
            &mut Perm::Pred(ref mut place) => place,
        }
    }

    pub fn unwrap(self) -> vir::Place {
        match self {
            Perm::Acc(place) |
            Perm::Pred(place) => place,
        }
    }

    pub fn map<F>(self, f: F) -> Self
        where F: Fn(vir::Place) -> vir::Place
    {
        match self {
            Perm::Acc(place) => Perm::Acc(f(place)),
            Perm::Pred(place) => Perm::Pred(f(place)),
        }
    }
}

impl fmt::Display for Perm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Perm::Acc(ref place) => write!(f, "Acc({})", place),
            &Perm::Pred(ref place) => write!(f, "Pred({})", place),
        }
    }
}


pub trait LabelledPermIterator {
    fn collect_curr(&mut self) -> Vec<Perm>;
    fn group_by_label(&mut self) -> (Vec<Perm>, HashMap<String, Vec<Perm>>);
}

impl<T> LabelledPermIterator for T where T: Iterator<Item = LabelledPerm> {
    fn collect_curr(&mut self) -> Vec<Perm> {
        self.flat_map(|mop| match mop {
            LabelledPerm::Curr(p) => Some(p),
            _ => None
        }).collect()
    }

    fn group_by_label(&mut self) -> (Vec<Perm>, HashMap<String, Vec<Perm>>) {
        let mut curr_perm = vec![];
        let mut old_perm = HashMap::new();
        for x in self {
            match x {
                LabelledPerm::Old(label, perm) => {
                    old_perm.entry(label).or_insert(vec![]).push(perm);
                }
                LabelledPerm::Curr(perm) => {
                    curr_perm.push(perm);
                }
            }
        }
        (curr_perm, old_perm)
    }
}
