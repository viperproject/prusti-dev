use std::collections::{BTreeMap, BTreeSet};

use crate::environment::mir_body::borrowck::facts::Point;

pub trait ToText {
    fn to_text(&self) -> String;
}

pub fn to_sorted_text<S: ToText>(texts: &[S]) -> Vec<String> {
    let mut strings: Vec<_> = texts.iter().map(ToText::to_text).collect();
    strings.sort();
    strings
}

pub fn opaque_lifetime_string(index: usize) -> String {
    format!("bw{}", index)
}

fn escape_html<S: ToString>(s: S) -> String {
    s.to_string()
        .replace('&', "&amp;")
        .replace('>', "&gt;")
        .replace('<', "&lt;")
        .replace('{', "\\{")
        .replace('}', "\\}")
        .replace('\n', "<br/>")
}

impl ToText for str {
    fn to_text(&self) -> String {
        self.to_string()
    }
}

impl ToText for String {
    fn to_text(&self) -> String {
        self.clone()
    }
}

impl ToText for rustc_middle::mir::Local {
    fn to_text(&self) -> String {
        format!("{:?}", self)
    }
}

impl ToText for rustc_middle::ty::RegionVid {
    fn to_text(&self) -> String {
        format!("lft_{}", self.index())
    }
}

impl ToText for Vec<rustc_middle::ty::RegionVid> {
    fn to_text(&self) -> String {
        let mut strings: Vec<_> = self.iter().map(ToText::to_text).collect();
        strings.sort();
        strings.join(", ")
    }
}

impl ToText for Vec<(rustc_middle::ty::RegionVid, rustc_middle::ty::RegionVid)> {
    fn to_text(&self) -> String {
        let mut strings: Vec<_> = self
            .iter()
            .map(|(r1, r2)| format!("{} ⊆ {}", r1.to_text(), r2.to_text()))
            .collect();
        strings.sort();
        strings.join(", ")
    }
}

impl ToText for BTreeSet<rustc_middle::ty::RegionVid> {
    fn to_text(&self) -> String {
        let strings: Vec<_> = self.iter().map(|r| r.to_text()).collect();
        strings.join(" ∪ ")
    }
}

impl ToText for BTreeMap<rustc_middle::ty::RegionVid, BTreeSet<rustc_middle::ty::RegionVid>> {
    fn to_text(&self) -> String {
        let strings: Vec<_> = self
            .iter()
            .map(|(r, set)| format!("{} ⊆ {}", r.to_text(), set.to_text()))
            .collect();
        strings.join(", ")
    }
}

pub fn point_to_text(point: &Point) -> String {
    format!("P{}", point.index())
}

pub fn points_to_text(points: &[Point]) -> String {
    let mut strings: Vec<_> = points.iter().map(point_to_text).collect();
    strings.sort();
    strings.join(", ")
}

pub fn loan_to_text(loan: &crate::environment::borrowck::facts::Loan) -> String {
    format!("{:?}", loan)
}

pub fn loans_to_text(loans: &[crate::environment::borrowck::facts::Loan]) -> String {
    let mut strings: Vec<_> = loans.iter().map(loan_to_text).collect();
    strings.sort();
    strings.join(", ")
}

pub(in super::super) fn loan_set_to_text(
    loans: &BTreeSet<crate::environment::borrowck::facts::Loan>,
) -> String {
    let strings: Vec<_> = loans.iter().map(loan_to_text).collect();
    strings.join(" ∪ ")
}

pub fn loan_containment_to_text(
    loans: &BTreeMap<
        rustc_middle::ty::RegionVid,
        BTreeSet<crate::environment::borrowck::facts::Loan>,
    >,
) -> String {
    let strings: Vec<_> = loans
        .iter()
        .map(|(r, set)| format!("{} ⊆ {}", r.to_text(), loan_set_to_text(set)))
        .collect();
    strings.join(", ")
}

impl ToText for rustc_middle::mir::BasicBlock {
    fn to_text(&self) -> String {
        format!("{:?}", self)
    }
}

impl ToText for rustc_middle::mir::Location {
    fn to_text(&self) -> String {
        format!("{:?}", self)
    }
}

impl<'tcx> ToText for rustc_middle::mir::Statement<'tcx> {
    fn to_text(&self) -> String {
        escape_html(format!("{:?}", self))
    }
}

impl<'tcx> ToText for rustc_middle::mir::Terminator<'tcx> {
    fn to_text(&self) -> String {
        escape_html(format!("{:?}", self.kind))
    }
}

impl<'tcx> ToText for rustc_middle::ty::Ty<'tcx> {
    fn to_text(&self) -> String {
        escape_html(format!("{:?}", self))
    }
}

impl<'tcx> ToText for rustc_middle::ty::Region<'tcx> {
    fn to_text(&self) -> String {
        match self.kind() {
            rustc_middle::ty::ReEarlyBound(reg) => {
                format!("lft_early_bound_{}", reg.index)
            }
            rustc_middle::ty::ReLateBound(debruijn, bound_reg) => {
                format!("lft_late_{}_{}", debruijn.index(), bound_reg.var.index())
            }
            rustc_middle::ty::ReFree(_) => {
                unimplemented!("ReFree: {}", format!("{}", self));
            }
            rustc_middle::ty::ReStatic => String::from("lft_static"),
            rustc_middle::ty::ReVar(region_vid) => format!("lft_{}", region_vid.index()),
            rustc_middle::ty::RePlaceholder(_) => {
                unimplemented!("RePlaceholder: {}", format!("{}", self));
            }
            rustc_middle::ty::ReEmpty(_) => {
                unimplemented!("ReEmpty: {}", format!("{}", self));
            }
            rustc_middle::ty::ReErased => String::from("lft_erased"),
        }
    }
}
