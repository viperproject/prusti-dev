// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    hyperdigraph::{Bijection, DHEdge, Hyperdigraph},
    pcs::LoanSCC,
};
use prusti_interface::environment::borrowck::facts::{Loan, PointIndex};
use rustc_middle::mir;

#[allow(unused)]
/// A Coupling DAG is a HyperDAG of places, with edges annotated by
/// families of loans of which there exists (dynamically, at runtime)
/// a sequence of Viper statements to consume the LHS and produce the RHS.

#[derive(Default, Clone)]
pub struct CouplingDigraph<'tcx> {
    graph: Hyperdigraph<mir::Place<'tcx>>,
    annotations: Bijection<DHEdge<mir::Place<'tcx>>, ()>,
}

impl<'tcx> CouplingDigraph<'tcx> {
    pub fn new_loan(&mut self, loan: Loan) {
        todo!();
    }

    /// This is going to be implemented slightly ad-hoc.
    /// After computing some examples I'll have a better idea of
    /// a general algorithm here.
    ///
    /// REQUIRES: the nodes of the LoanSCC to be sets of nodes in the
    /// hypergraph (kills and new loans are applied)
    /// NOTE: Possibly less live loans than edges in CDG
    pub fn constrain_by_scc(&mut self, scc: LoanSCC) {
        // If all origins either contain or do not contain a K-path,
        // quotient the graph by that K-path ("collapse" them).

        // "before" relation: ensure that
        println!("\tenter constraint algorithm");
        println!("\t{:#?}", scc.distinguishing_loans());
        println!("\texit constraint algorithm");
    }

    pub fn pprint(&self) {
        self.graph.pprint();
    }
}
