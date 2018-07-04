// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::vir;
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Perm {
    Acc(vir::Place),
    Pred(vir::Place)
}

impl Perm {
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

pub fn display(this: &Vec<Perm>) -> String {
    this.iter().map(|x| x.to_string()).collect::<Vec<String>>().join(", ")
}
