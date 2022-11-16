// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use serde::Serialize;

/// Trait to be used to define an abstract domain by defining the type of its elements.
/// These elements can be used in the ``Analyzer`` to represent an abstraction of the concrete
/// state at program points.
///
/// To ensure that the analysis is converging to a correct fixed point implementations `S` of this
/// trait should fulfill the following properties:
/// * `join()` implicitly defines a partial order of abstraction `<=`, such that
///   forall x,y: S :: `x <= x.join(y)` && `y <= x.join(y)`;
///   i.e. `join()` computes an upper bound in that order, which means it abstracts more (or
///   equally many) concrete states, in particular it represents all concrete states that were
///   abstracted by either `x` or `y`.
/// * `new_bottom()` should return the least element in that order.
/// * If the 'height' of the order, i.e. how many elements can be traversed until a maximum is
///   reached, is not known to be finite, the following properties should additionally hold for
///   proper widening:
///     - exists i: u32 :: `need_to_widen(i) == true`
///     - forall x,y: S :: `x <= x.widen(y)` && `y <= x.widen(y)`
///     - for every ascending chain of domain elements x_i the ascending chain y_i defined as
///       y_0 := x_0, y_(i+1) := x_i.widen(y_i)
///       reaches a fixed-point after a finite number of steps
/// * The 'abstract transformers' `apply_statement_effect` and `apply_terminator_effect`
///   should correctly abstract the concrete semantics of the given operation,
///   i.e. the resulting abstraction should represent a superset of the possible concrete states
///   after applying the statement or terminator to any of the concrete states represented by the
///   abstraction before.
///   (If an operation is not supported an `AnalysisError::UnsupportedStatement` can be returned.)
/// * `apply_terminator_effect` should assign an abstract state to every successor basic block,
///   otherwise `NoStateAfterSuccessor` error will be returned by the analysis.
///
/// To get a result that is as precise as possible implementers probably also want to fulfill the
/// following properties:
/// * `join()` should return the **least** least upper bound. In particular it should hold:
///    forall x: S :: `x.join(S::new_bottom(_)) == x` && `S::new_bottom(_).join(x) == x`.
/// * The 'abstract transformers' `apply_statement_effect` and `apply_terminator_effect`
///   should abstract the concrete semantics as precise as possible.
// Sized needed for apply_terminator_effect's return type
pub trait AbstractState: Clone + Eq + Sized + Serialize {
    //fn make_top(&mut self) -> Self;
    //fn make_bottom(&mut self) -> Self;

    /// Checks if the current state corresponds to the bottom element in the lattice
    fn is_bottom(&self) -> bool;

    //fn new_top(&self) -> Self;
    //fn is_top(&self) -> bool;

    //fn less_equal(&self, other: &Self) -> bool;

    /// Lattice operation to join `other` into this state, producing the (least) upper bound
    fn join(&mut self, other: &Self);

    /// Lattice operation to join all `others` into this state, producing the (least) upper bound
    fn join_all(&mut self, others: &[&Self]) {
        for other in others.iter() {
            self.join(other)
        }
    }

    //fn meet(&mut self, other: &Self) -> Self;

    /// Make the state less precise to make the iteration stop by using the difference to the state
    /// from the previous iteration given in `previous`.
    fn widen(&mut self, previous: &Self);
}
