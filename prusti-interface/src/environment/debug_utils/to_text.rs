use crate::environment::mir_body::borrowck::facts::Point;
use std::collections::{BTreeMap, BTreeSet};
use vir::common::{builtin_constants::ERASED_LIFETIME_NAME, graphviz::escape_html};

pub trait ToText {
    fn to_text(&self) -> String;
}

pub fn to_sorted_text<S: ToText>(texts: &[S]) -> Vec<String> {
    let mut strings: Vec<_> = texts.iter().map(ToText::to_text).collect();
    strings.sort();
    strings
}

pub fn opaque_lifetime_string(index: usize) -> String {
    format!("bw{index}")
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

impl ToText for prusti_rustc_interface::middle::mir::Local {
    fn to_text(&self) -> String {
        format!("{self:?}")
    }
}

impl ToText for prusti_rustc_interface::middle::ty::RegionVid {
    fn to_text(&self) -> String {
        format!("lft_{}", self.index())
    }
}

impl ToText for Vec<prusti_rustc_interface::middle::ty::RegionVid> {
    fn to_text(&self) -> String {
        let mut strings: Vec<_> = self.iter().map(ToText::to_text).collect();
        strings.sort();
        strings.join(", ")
    }
}

impl ToText
    for Vec<(
        prusti_rustc_interface::middle::ty::RegionVid,
        prusti_rustc_interface::middle::ty::RegionVid,
    )>
{
    fn to_text(&self) -> String {
        let mut strings: Vec<_> = self
            .iter()
            .map(|(r1, r2)| format!("{} ⊆ {}", r1.to_text(), r2.to_text()))
            .collect();
        strings.sort();
        strings.join(", ")
    }
}

impl ToText for prusti_rustc_interface::middle::ty::BoundRegionKind {
    fn to_text(&self) -> String {
        match self {
            prusti_rustc_interface::middle::ty::BoundRegionKind::BrAnon(id, _) => {
                format!("lft_br_anon_{id}")
            }
            prusti_rustc_interface::middle::ty::BoundRegionKind::BrNamed(_, name) => {
                format!("lft_br_named_{name}")
            }
            prusti_rustc_interface::middle::ty::BoundRegionKind::BrEnv => "lft_br_env".to_string(),
        }
    }
}

impl ToText for BTreeSet<prusti_rustc_interface::middle::ty::RegionVid> {
    fn to_text(&self) -> String {
        let strings: Vec<_> = self.iter().map(|r| r.to_text()).collect();
        strings.join(" ∪ ")
    }
}

impl ToText
    for BTreeMap<
        prusti_rustc_interface::middle::ty::RegionVid,
        BTreeSet<prusti_rustc_interface::middle::ty::RegionVid>,
    >
{
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
    format!("{loan:?}")
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
        prusti_rustc_interface::middle::ty::RegionVid,
        BTreeSet<crate::environment::borrowck::facts::Loan>,
    >,
) -> String {
    let strings: Vec<_> = loans
        .iter()
        .map(|(r, set)| format!("{} ⊆ {}", r.to_text(), loan_set_to_text(set)))
        .collect();
    strings.join(", ")
}

impl ToText for prusti_rustc_interface::middle::mir::BasicBlock {
    fn to_text(&self) -> String {
        format!("{self:?}")
    }
}

impl ToText for prusti_rustc_interface::middle::mir::Location {
    fn to_text(&self) -> String {
        format!("{self:?}")
    }
}

impl<'tcx> ToText for prusti_rustc_interface::middle::mir::Statement<'tcx> {
    fn to_text(&self) -> String {
        escape_html(format!("{self:?}"))
    }
}

impl<'tcx> ToText for prusti_rustc_interface::middle::mir::Terminator<'tcx> {
    fn to_text(&self) -> String {
        escape_html(format!("{:?}", self.kind))
    }
}

impl<'tcx> ToText for prusti_rustc_interface::middle::ty::Ty<'tcx> {
    fn to_text(&self) -> String {
        escape_html(format!("{self:?}"))
    }
}

impl<'tcx> ToText for prusti_rustc_interface::middle::ty::Region<'tcx> {
    fn to_text(&self) -> String {
        match self.kind() {
            prusti_rustc_interface::middle::ty::ReEarlyBound(reg) => {
                format!("lft_early_bound_{}", reg.index)
            }
            prusti_rustc_interface::middle::ty::ReLateBound(debruijn, bound_reg) => {
                format!("lft_late_{}_{}", debruijn.index(), bound_reg.var.index())
            }
            prusti_rustc_interface::middle::ty::ReFree(_) => {
                unimplemented!("ReFree: {self}");
            }
            prusti_rustc_interface::middle::ty::ReStatic => String::from("lft_static"),
            prusti_rustc_interface::middle::ty::ReVar(region_vid) => {
                format!("lft_{}", region_vid.index())
            }
            prusti_rustc_interface::middle::ty::RePlaceholder(_) => {
                unimplemented!("RePlaceholder: {self}");
            }
            prusti_rustc_interface::middle::ty::ReErased => String::from(ERASED_LIFETIME_NAME),
            prusti_rustc_interface::middle::ty::ReError(_) => {
                unimplemented!("ReError: {}", format!("{self}"));
            }
        }
    }
}
