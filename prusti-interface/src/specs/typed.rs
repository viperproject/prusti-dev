use crate::{environment::Environment, utils::has_trait_bounds_type_cond_spec, PrustiError};
pub use common::{SpecIdRef, SpecType, SpecificationId};
use prusti_rustc_interface::{
    hir::def_id::{DefId, LocalDefId},
    macros::{TyDecodable, TyEncodable},
};
use prusti_specs::specifications::common;
use regex::Regex;
use rustc_hash::FxHashMap;
use std::fmt::{Debug, Display, Formatter};

/// A map of specifications keyed by crate-local DefIds.
#[derive(Default, Debug, Clone)]
pub struct DefSpecificationMap {
    pub proc_specs: FxHashMap<DefId, SpecGraph<ProcedureSpecification>>,
    pub loop_specs: FxHashMap<DefId, LoopSpecification>,
    pub type_specs: FxHashMap<DefId, TypeSpecification>,
    pub prusti_assertions: FxHashMap<DefId, PrustiAssertion>,
    pub prusti_assumptions: FxHashMap<DefId, PrustiAssumption>,
    pub prusti_refutations: FxHashMap<DefId, PrustiRefutation>,
    pub ghost_begin: FxHashMap<DefId, GhostBegin>,
    pub ghost_end: FxHashMap<DefId, GhostEnd>,
    pub specification_region_begin: FxHashMap<DefId, SpecificationRegionBegin>,
    pub specification_region_end: FxHashMap<DefId, SpecificationRegionEnd>,
    pub specification_expression: FxHashMap<DefId, SpecificationExpression>,
}

impl DefSpecificationMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_loop_spec(&self, def_id: &DefId) -> Option<&LoopSpecification> {
        self.loop_specs.get(def_id)
    }

    pub fn get_proc_spec(&self, def_id: &DefId) -> Option<&SpecGraph<ProcedureSpecification>> {
        self.proc_specs.get(def_id)
    }

    pub fn get_type_spec(&self, def_id: &DefId) -> Option<&TypeSpecification> {
        self.type_specs.get(def_id)
    }

    pub fn get_assertion(&self, def_id: &DefId) -> Option<&PrustiAssertion> {
        self.prusti_assertions.get(def_id)
    }

    pub fn get_assumption(&self, def_id: &DefId) -> Option<&PrustiAssumption> {
        self.prusti_assumptions.get(def_id)
    }

    pub fn get_refutation(&self, def_id: &DefId) -> Option<&PrustiRefutation> {
        self.prusti_refutations.get(def_id)
    }

    pub fn get_ghost_begin(&self, def_id: &DefId) -> Option<&GhostBegin> {
        self.ghost_begin.get(def_id)
    }

    pub fn get_ghost_end(&self, def_id: &DefId) -> Option<&GhostEnd> {
        self.ghost_end.get(def_id)
    }

    pub fn get_specification_region_begin(
        &self,
        def_id: &DefId,
    ) -> Option<&SpecificationRegionBegin> {
        self.specification_region_begin.get(def_id)
    }

    pub fn get_specification_region_end(&self, def_id: &DefId) -> Option<&SpecificationRegionEnd> {
        self.specification_region_end.get(def_id)
    }

    pub fn get_specification_expression(&self, def_id: &DefId) -> Option<&SpecificationExpression> {
        self.specification_expression.get(def_id)
    }

    pub(crate) fn defid_for_export(
        &self,
    ) -> (
        // Specs
        Vec<DefId>,
        // Pure fns
        Vec<DefId>,
        // Predicates
        Vec<DefId>,
    ) {
        let mut specs = Vec::new();
        let mut pure_fns = Vec::new();
        let mut predicates = Vec::new();
        for (def_id, spec_graph) in &self.proc_specs {
            let all_specs = std::iter::once(&spec_graph.base_spec)
                .chain(spec_graph.specs_with_constraints.values());
            for spec in all_specs {
                if let Some(pres) = spec.pres.extract_with_selective_replacement() {
                    specs.extend(pres);
                }
                if let Some(posts) = spec.posts.extract_with_selective_replacement() {
                    specs.extend(posts);
                }
                if let Some(broken_pres) = spec.broken_pres.extract_with_selective_replacement() {
                    specs.extend(broken_pres);
                }
                if let Some(broken_posts) = spec.broken_posts.extract_with_selective_replacement() {
                    specs.extend(broken_posts);
                }
                if let Some(Some(term)) = spec.terminates.extract_with_selective_replacement() {
                    specs.push(*term);
                }
                if let Some(pledges) = spec.pledges.extract_with_selective_replacement() {
                    specs.extend(pledges.iter().filter_map(|pledge| pledge.lhs));
                    specs.extend(pledges.iter().map(|pledge| pledge.rhs));
                }
                let is_trusted = spec.trusted.extract_inherit().expect("Expected trusted")
                // It has to be non-extern_spec which is trusted (since extern_specs are always trusted)
                    && (*def_id == spec.source || !def_id.is_local());
                if spec.kind.is_pure().expect("Expected pure") && !is_trusted {
                    pure_fns.push(*def_id)
                }
                if let Some(ProcedureSpecificationKind::Predicate(Some(def_id))) =
                    spec.kind.extract_with_selective_replacement()
                {
                    predicates.push(*def_id);
                }
            }
        }
        for spec in self.type_specs.values() {
            if let Some(invariants) = spec.invariant.extract_with_selective_replacement() {
                specs.extend(invariants);
            }
            if let Some(invariants) = spec
                .structural_invariant
                .extract_with_selective_replacement()
            {
                specs.extend(invariants);
            }
        }
        (specs, pure_fns, predicates)
    }

    pub(crate) fn import_external(
        &mut self,
        proc_specs: FxHashMap<DefId, SpecGraph<ProcedureSpecification>>,
        type_specs: FxHashMap<DefId, TypeSpecification>,
        env: &Environment,
    ) {
        let duplicate_error = |item_id, spec_id_a: DefId, spec_id_b: DefId| {
            PrustiError::incorrect(
                format!(
                    "duplicate specification for `{}` from crate `{}` and `{}`",
                    env.name.get_item_name(item_id),
                    env.name.crate_name(spec_id_a.krate),
                    env.name.crate_name(spec_id_b.krate),
                ),
                crate::specs::MultiSpan::from_spans(vec![
                    env.query.get_def_span(spec_id_a),
                    env.query.get_def_span(spec_id_b),
                ]),
            )
            .emit(&env.diagnostic)
        };
        for (k, v) in proc_specs {
            if let Some(other) = self.proc_specs.insert(k, v) {
                let v = self.proc_specs.get(&k).unwrap();
                duplicate_error(k, other.base_spec.source, v.base_spec.source);
            }
        }
        for (k, v) in type_specs {
            if let Some(other) = self.type_specs.insert(k, v) {
                let v = self.type_specs.get(&k).unwrap();
                duplicate_error(k, other.source, v.source);
            }
        }
    }

    pub fn all_values_debug(&self, hide_uuids: bool) -> Vec<String> {
        let loop_specs: Vec<_> = self
            .loop_specs
            .values()
            .map(|spec| format!("{spec:?}"))
            .collect();
        let proc_specs: Vec<_> = self
            .proc_specs
            .values()
            .map(|spec| format!("{:?}", spec.base_spec))
            .collect();
        let type_specs: Vec<_> = self
            .type_specs
            .values()
            .map(|spec| format!("{spec:?}"))
            .collect();
        let asserts: Vec<_> = self
            .prusti_assertions
            .values()
            .map(|spec| format!("{spec:?}"))
            .collect();
        let assumptions: Vec<_> = self
            .prusti_assumptions
            .values()
            .map(|spec| format!("{spec:?}"))
            .collect();
        let refutations: Vec<_> = self
            .prusti_refutations
            .values()
            .map(|spec| format!("{spec:?}"))
            .collect();
        let mut values = Vec::new();
        values.extend(loop_specs);
        values.extend(proc_specs);
        values.extend(type_specs);
        values.extend(asserts);
        values.extend(assumptions);
        values.extend(refutations);
        if hide_uuids {
            let uuid =
                Regex::new("[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}").unwrap();
            let num_uuid = Regex::new("[a-z0-9]{32}").unwrap();
            let mut replaced_values: Vec<String> = vec![];
            for item in values {
                let item = num_uuid.replace_all(&item, "$(NUM_UUID)");
                let item = uuid.replace_all(&item, "$(UUID)");
                replaced_values.push(String::from(item));
            }
            values = replaced_values;
        }
        // We sort in this strange way so that the output is
        // determinstic enough to be used in tests.
        values.sort_by_key(|v| (v.len(), v.to_string()));
        values
    }
}

#[derive(Debug, Clone, TyEncodable, TyDecodable)]
pub struct ProcedureSpecification {
    // DefId of fn signature to which the spec was attached.
    // For `extern_spec` it differs to the key in `proc_specs`
    pub source: DefId,
    pub kind: SpecificationItem<ProcedureSpecificationKind>,
    pub pres: SpecificationItem<Vec<DefId>>,
    pub posts: SpecificationItem<Vec<DefId>>,
    pub pledges: SpecificationItem<Vec<Pledge>>,
    pub trusted: SpecificationItem<bool>,
    pub no_panic: SpecificationItem<bool>,
    pub no_panic_ensures_postcondition: SpecificationItem<bool>,
    pub broken_pres: SpecificationItem<Vec<DefId>>,
    pub broken_posts: SpecificationItem<Vec<DefId>>,
    pub terminates: SpecificationItem<Option<DefId>>,
    pub purity: SpecificationItem<Option<DefId>>, // for type-conditional spec refinements
}

impl ProcedureSpecification {
    pub fn empty(source: DefId) -> Self {
        ProcedureSpecification {
            source,
            // We never create an empty "kind". Having no concrete user-annotation
            // defaults to an impure function
            kind: SpecificationItem::Inherent(ProcedureSpecificationKind::Impure),
            pres: SpecificationItem::Empty,
            posts: SpecificationItem::Empty,
            broken_pres: SpecificationItem::Empty,
            broken_posts: SpecificationItem::Empty,
            pledges: SpecificationItem::Empty,
            trusted: SpecificationItem::Inherent(false),
            no_panic: SpecificationItem::Inherent(false),
            no_panic_ensures_postcondition: SpecificationItem::Inherent(false),
            terminates: SpecificationItem::Inherent(None),
            purity: SpecificationItem::Inherent(None),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, TyEncodable, TyDecodable)]
pub enum ProcedureSpecificationKind {
    Impure,
    Pure,
    /// The specification is a predicate with the enclosed body.
    /// The body can be None to account for abstract predicates.
    Predicate(Option<DefId>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, TyEncodable, TyDecodable)]
pub enum SpecConstraintKind {
    ResolveGenericParamTraitBounds,
}

impl Display for ProcedureSpecificationKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ProcedureSpecificationKind::Impure => write!(f, "Impure"),
            ProcedureSpecificationKind::Pure => write!(f, "Pure"),
            ProcedureSpecificationKind::Predicate(_) => write!(f, "Predicate"),
        }
    }
}
impl ProcedureSpecificationKind {
    pub fn is_impure(&self) -> bool {
        matches!(self, ProcedureSpecificationKind::Impure)
    }
}

#[derive(Debug, Clone)]
pub enum LoopSpecification {
    Invariant(LocalDefId),
    Variant(LocalDefId),
}

/// Specification of a type.
#[derive(Debug, Clone, TyEncodable, TyDecodable)]
pub struct TypeSpecification {
    // DefId of type defn to which the spec was attached.
    // Currently identical to the key in `type_specs`, but once
    // `extern_spec` for type invs is supported it could differ.
    pub source: DefId,
    pub invariant: SpecificationItem<Vec<DefId>>,
    pub structural_invariant: SpecificationItem<Vec<DefId>>,
    pub trusted: SpecificationItem<bool>,
    pub model: Option<(String, LocalDefId)>,
    pub counterexample_print: Vec<(Option<String>, LocalDefId)>,
}

impl TypeSpecification {
    pub fn empty(source: DefId) -> Self {
        TypeSpecification {
            source,
            invariant: SpecificationItem::Empty,
            structural_invariant: SpecificationItem::Empty,
            trusted: SpecificationItem::Inherent(false),
            model: None,
            counterexample_print: vec![],
        }
    }
}

#[derive(Debug, Clone)]
pub struct PrustiAssertion {
    pub assertion: LocalDefId,
    pub is_structural: bool,
}

#[derive(Debug, Clone)]
pub struct PrustiAssumption {
    pub assumption: LocalDefId,
    pub is_structural: bool,
}

#[derive(Debug, Clone)]
pub struct PrustiRefutation {
    pub refutation: LocalDefId,
}

#[derive(Debug, Clone)]
pub struct GhostBegin {
    pub marker: LocalDefId,
}

#[derive(Debug, Clone)]
pub struct GhostEnd {
    pub marker: LocalDefId,
}

#[derive(Debug, Clone)]
pub struct SpecificationRegionBegin {
    pub marker: LocalDefId,
}

#[derive(Debug, Clone)]
pub struct SpecificationRegionEnd {
    pub marker: LocalDefId,
}

#[derive(Debug, Clone)]
pub struct SpecificationExpression {
    pub expression: LocalDefId,
}

/// The base container to store a contract of a procedure.
/// A contract can be divided into multiple specifications:
/// - **Base spec**: A spec without constraints.
/// - **Constrained specs**: Multiple specs which have [SpecConstraintKind] constraints.
#[derive(Default, Debug, Clone, TyEncodable, TyDecodable)]
pub struct SpecGraph<T> {
    /// The base specification which has no constraints
    pub base_spec: T,

    /// Specs which are active when the corresponding [SpecConstraintKind] holds on callsite
    pub specs_with_constraints: FxHashMap<SpecConstraintKind, T>,
}

impl<T> SpecGraph<T> {
    pub fn new(spec: T) -> Self {
        Self {
            base_spec: spec,
            specs_with_constraints: FxHashMap::default(),
        }
    }
}

/// Provides various methods to construct a [SpecGraph] for a [ProcedureSpecification].
/// In particular, these methods ensure that the resulting [SpecGraph]'s specs are *consistent*,
/// which means:
/// - The postconditions of any constrained spec always contain the postconditions of the base spec
/// - The [ProcedureSpecificationKind] for the base spec and constrained specs is always the same
/// - The `trusted` flag for the base spec and constrained specs is always the same
/// - The [Pledge]s for the base spec and constrained specs are always the same
///
/// Note: Unlike postconditions, the preconditions are not copied amongst the base spec
/// and constrained specs.
///
/// # A note about behavioral subtyping
/// For a [SpecGraph] to be sound, we require that the constrained specs are valid to the base spec
/// w.r.t. behavioral subtyping rules.
/// We at least require that for some base spec B and any constrained spec C:
/// - (a) The postconditions of C are at least as strong as the postconditions of B
/// - (b) The preconditions of C are at least as weak as the preconditions of B
/// - *...more..*
///
/// The consistency guarantees mentioned above satisfy (a) by construction but do not guarantee (b).
///
/// **Important**: There is no automatic check that guarantees the validity of a [SpecGraph].
///
/// # Example: Pre- and postconditions
/// ```ignore
/// trait MarkerTrait {}
///
/// trait SomeTrait {
///     #[requires(x > 0)]
///     #[ensures(x > 0)]
///     #[refine_spec(where T: MarkerTrait, [
///         requires(x > 10),
///         ensures(x > 10),
///     ])]
///     fn foo<T>(&self, x: i32) -> i32;
/// }
///
/// struct SomeStruct;
/// #[refine_trait_spec]
/// impl SomeTrait for SomeStruct {
///     #[requires(x >= 0)]
///     #[ensures(x > 10)]
///     #[refine_spec(where T: MarkerTrait, [
///         requires(x >= -5),
///         ensures(x > 20),
///     ])]
///     fn foo<T>(&self, x: i32) -> i32 {
///         42
///     }
/// }
/// ```
/// Let `B_T` be the base spec of `SomeTrait`, `B_S` be the base spec of `SomeStruct`,
/// `C_T` be the constrained spec of `SomeTrait` and `C_S` be the constrained spec of `SomeStruct`.
/// - The computed [SpecGraph] of `SomeTrait` will be:
///     - `pres(B_T) ≡ x > 0`
///     - `posts(B_T) ≡ x > 0`
///     - `pres(C_T) ≡ x > 10`
///     - `posts(C_T) ≡ posts(B_T) && x > 10 ≡ x > 0 && x > 10`
/// - The computed [SpecGraph] of `SomeStruct` will be:
///     - `pres(B_S) ≡ x >= 0`
///     - `posts(B_S) ≡ x > 10`
///     - `pres(C_S) ≡ x >= -5`
///     - `posts(C_S) ≡ posts(B_S) && x > 20 ≡ x > 10 && x > 20`
///
/// When using `SomeStruct::foo`, we resolve to either `B_S` or `C_S`.
/// ```ignore
/// impl MarkerTrait for i32 {}
/// fn main() {
///     let s = SomeStruct;
///     let r = s.foo::<i32>(100); // i32 implements MarkerTrait -> C_S is active
///     let r = s.foo::<u32>(100); // i32 does not implement MarkerTrait -> B_S is active
/// }
/// ```
impl SpecGraph<ProcedureSpecification> {
    /// Attaches the precondition `pre` to this [SpecGraph].
    ///
    /// If this precondition has a constraint it will be attached to the corresponding
    /// constrained spec, otherwise just to the base spec.
    pub fn add_precondition<'tcx>(&mut self, pre: LocalDefId, env: &Environment<'tcx>) {
        match self.get_constraint(pre, env) {
            None => {
                self.base_spec.pres.push(pre.to_def_id());
                // Preconditions are explicitly not copied (as opposed to postconditions)
                // This would always violate behavioral subtyping rules
            }
            Some(constraint) => {
                self.get_constrained_spec_mut(constraint)
                    .pres
                    .push(pre.to_def_id());
            }
        }
    }

    /// Attaches the postcondition `post` to this [SpecGraph].
    ///
    /// If this postcondition has a constraint it will be attached to the corresponding
    /// constrained spec **and** the base spec, otherwise just to the base spec.
    pub fn add_postcondition<'tcx>(&mut self, post: LocalDefId, env: &Environment<'tcx>) {
        match self.get_constraint(post, env) {
            None => {
                self.base_spec.posts.push(post.to_def_id());
                self.specs_with_constraints
                    .values_mut()
                    .for_each(|s| s.posts.push(post.to_def_id()));
            }
            Some(obligation) => {
                self.get_constrained_spec_mut(obligation)
                    .posts
                    .push(post.to_def_id());
            }
        }
    }

    /// Sets the broken precondition for the base spec and all constrained specs.
    pub fn add_broken_precondition(&mut self, broken_precondition: DefId) {
        self.base_spec.broken_pres.push(broken_precondition);
    }

    /// Sets the broken precondition for the base spec and all constrained specs.
    pub fn add_broken_postcondition(&mut self, broken_postcondition: DefId) {
        self.base_spec.broken_posts.push(broken_postcondition);
    }

    pub fn add_purity<'tcx>(&mut self, purity: LocalDefId, env: &Environment<'tcx>) {
        match self.get_constraint(purity, env) {
            None => {
                unreachable!(
                    "separate purity defs are only used for type-conditional spec refinements"
                )
            }
            Some(constraint) => {
                let constrained_spec = self.get_constrained_spec_mut(constraint);
                constrained_spec.kind =
                    SpecificationItem::Inherent(ProcedureSpecificationKind::Pure);
                // need to store this as well, since without pres or posts we couldn't find any def id with the trait bounds
                constrained_spec.purity.set(Some(purity.to_def_id()));
            }
        }
    }

    /// Attaches the `pledge` to the base spec and all constrained specs.
    pub fn add_pledge(&mut self, pledge: Pledge) {
        self.base_spec.pledges.push(pledge.clone());
        self.specs_with_constraints
            .values_mut()
            .for_each(|s| s.pledges.push(pledge.clone()));
    }

    /// Sets the trusted flag for the base spec and all constrained specs.
    pub fn set_trusted(&mut self, trusted: bool) {
        self.base_spec.trusted.set(trusted);
        self.specs_with_constraints
            .values_mut()
            .for_each(|s| s.trusted.set(trusted));
    }

    /// Sets the no_panic flag for the base spec and all constrained specs.
    pub fn set_no_panic(&mut self, no_panic: bool) {
        self.base_spec.no_panic.set(no_panic);
        self.specs_with_constraints
            .values_mut()
            .for_each(|s| s.no_panic.set(no_panic));
    }

    /// Sets the no_panic_ensures_postcondition flag for the base spec and all constrained specs.
    pub fn set_no_panic_ensures_postcondition(&mut self, no_panic_ensures_postcondition: bool) {
        self.base_spec
            .no_panic_ensures_postcondition
            .set(no_panic_ensures_postcondition);
        self.specs_with_constraints.values_mut().for_each(|s| {
            s.no_panic_ensures_postcondition
                .set(no_panic_ensures_postcondition)
        });
    }

    /// Sets the termination flag for the base spec and all constrained specs.
    pub fn set_terminates(&mut self, terminates: DefId) {
        self.base_spec.terminates.set(Some(terminates));
        self.specs_with_constraints
            .values_mut()
            .for_each(|s| s.terminates.set(Some(terminates)));
    }

    /// Sets the [ProcedureSpecificationKind] for the base spec and all constrained specs.
    pub fn set_kind(&mut self, kind: ProcedureSpecificationKind) {
        self.base_spec.kind.set(kind);
        self.specs_with_constraints
            .values_mut()
            .for_each(|s| s.kind.set(kind));
    }

    /// Lazily gets/creates a constrained spec.
    /// If the constrained spec does not yet exist, the base spec serves as a template for
    /// the newly created constrained spec.
    fn get_constrained_spec_mut(
        &mut self,
        constraint: SpecConstraintKind,
    ) -> &mut ProcedureSpecification {
        self.specs_with_constraints
            .entry(constraint)
            .or_insert_with(|| self.base_spec.clone())
    }

    /// Gets the constraint of a spec function `spec`.
    ///
    /// Multiple constraints are currently not supported.
    fn get_constraint<'tcx>(
        &self,
        spec: LocalDefId,
        env: &Environment<'tcx>,
    ) -> Option<SpecConstraintKind> {
        let attrs = env.query.get_local_attributes(spec);
        if has_trait_bounds_type_cond_spec(attrs) {
            return Some(SpecConstraintKind::ResolveGenericParamTraitBounds);
        }
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq, TyEncodable, TyDecodable)]
pub struct Pledge {
    pub reference: Option<()>, // TODO: pledge references
    pub lhs: Option<DefId>,
    pub rhs: DefId,
}

/// A specification, such as preconditions or a `#[pure]` annotation.
/// Contains information about the refinement of these specifications.
#[derive(Debug, Clone, Copy, PartialEq, Eq, TyEncodable, TyDecodable)]
pub enum SpecificationItem<T> {
    /// Represents an empty specification, i.e. when the user has not defined the property
    Empty,

    /// Represents a specification typed by the user
    Inherent(T),

    /// Represents a specification which was inherited from somewhere (e.g. from a trait method)
    Inherited(T),

    /// Represents an item which was refined
    /// This happens for example if the user annotates a trait method and its implementation method
    /// with a precondition. This variant then holds the trait's precondition and the impl's precondition.
    Refined(T, T),
}

impl<T> SpecificationItem<T> {
    pub fn is_empty(&self) -> bool {
        matches!(self, SpecificationItem::Empty)
    }

    /// Returns the contained value of this item
    fn get(&self) -> Option<(Option<&T>, &T)> {
        // TODO(tymap): this API is not good: it must be possible to tell that
        //   the result was inherited, as we will e.g. need to rebase our substs
        //   to the trait
        match self {
            SpecificationItem::Empty => None,
            SpecificationItem::Inherited(val) => Some((None, val)),
            SpecificationItem::Inherent(val) => Some((None, val)),
            SpecificationItem::Refined(from, to) => Some((Some(from), to)),
        }
    }

    /// Extracts the refined value out of this item by applying the provided strategy
    pub fn extract_with_strategy<'a, R, S: FnOnce((Option<&'a T>, &'a T)) -> R>(
        &'a self,
        strategy: S,
    ) -> Option<R> {
        self.get().map(strategy)
    }

    /// Uses alternative C as discussed in
    /// https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Matthias_Erdin_MA_report.pdf
    /// pp 19-23
    pub fn extract_with_selective_replacement(&self) -> Option<&T> {
        self.extract_with_strategy(|(_, refined)| refined)
    }

    #[track_caller]
    pub fn expect_empty_or_inherent(&self) -> Option<&T> {
        match self {
            SpecificationItem::Empty => None,
            SpecificationItem::Inherent(item) => Some(item),
            _ => unreachable!(),
        }
    }

    #[track_caller]
    pub fn expect_inherent(&self) -> &T {
        match self {
            SpecificationItem::Inherent(item) => item,
            _ => unreachable!(),
        }
    }

    #[track_caller]
    pub fn expect_inherited(&self) -> &T {
        match self {
            SpecificationItem::Inherited(item) => item,
            _ => unreachable!(),
        }
    }

    #[track_caller]
    pub fn expect_refined(&self) -> (&T, &T) {
        match self {
            SpecificationItem::Refined(a, b) => (a, b),
            _ => unreachable!(),
        }
    }
}

impl<T: Clone> SpecificationItem<T> {
    pub fn set(&mut self, new_value: T) {
        match self {
            SpecificationItem::Empty => *self = SpecificationItem::Inherent(new_value),
            SpecificationItem::Inherent(val) => *val = new_value,
            SpecificationItem::Refined(_, values) => *values = new_value,
            SpecificationItem::Inherited(inherited) => {
                *self = SpecificationItem::Refined(inherited.clone(), new_value)
            }
        }
    }
}

impl SpecificationItem<bool> {
    pub fn extract_inherit(&self) -> Option<bool> {
        self.extract_with_strategy(|(refined_from, refined)| {
            *(refined_from.unwrap_or(&false)) || *refined
        })
    }
}

#[derive(Debug)]
pub enum ProcedureSpecificationKindError {
    /// Occurs whenever the relation between [ProcedureSpecificationKind]s is violated.
    /// The relation is: predicates ⊂ pure functions ⊂ impure functions
    /// However, we can not refine a non-predicate to a predicate, since predicates are not callable.
    /// This validation is not automatically performed during refinement. It needs to be invoked
    /// manually with [SpecificationItem<ProcedureSpecificationKind>::validate]
    InvalidSpecKindRefinement(ProcedureSpecificationKind, ProcedureSpecificationKind),
}

impl SpecificationItem<ProcedureSpecificationKind> {
    pub fn is_pure(&self) -> Result<bool, ProcedureSpecificationKindError> {
        self.validate()?;

        Ok(matches!(
            self.extract_with_selective_replacement(),
            Some(ProcedureSpecificationKind::Pure) | Some(ProcedureSpecificationKind::Predicate(_))
        ))
    }

    pub fn is_impure(&self) -> Result<bool, ProcedureSpecificationKindError> {
        self.validate()?;

        Ok(match self.extract_with_selective_replacement() {
            Some(refined) => matches!(refined, ProcedureSpecificationKind::Impure),
            _ => true,
        })
    }

    pub fn get_predicate_body(&self) -> Result<Option<&DefId>, ProcedureSpecificationKindError> {
        self.validate()?;

        Ok(match self.extract_with_selective_replacement() {
            Some(ProcedureSpecificationKind::Predicate(pred_id)) => pred_id.as_ref(),
            _ => None,
        })
    }

    /// Ensures that refined [ProcedureSpecificationKind]s are valid.
    /// See [ProcedureSpecificationKindError] for detailed error descriptions.
    pub fn validate(&self) -> Result<(), ProcedureSpecificationKindError> {
        use ProcedureSpecificationKind::*;
        if let SpecificationItem::Refined(base, refined) = self {
            match (base, refined) {
                (Impure, Impure) | (Impure, Pure) | (Pure, Pure) | (Predicate(_), Predicate(_)) => {
                    Ok(())
                }
                _ => Err(ProcedureSpecificationKindError::InvalidSpecKindRefinement(
                    *base, *refined,
                )),
            }
        } else {
            Ok(())
        }
    }
}

impl<T> SpecificationItem<Vec<T>> {
    pub fn new(vec: Vec<T>) -> Self {
        if vec.is_empty() {
            SpecificationItem::Empty
        } else {
            SpecificationItem::Inherent(vec)
        }
    }

    pub fn extract_with_selective_replacement_iter(&self) -> Box<dyn Iterator<Item = &T> + '_> {
        if let Some(items) = self.extract_with_selective_replacement() {
            return Box::new(items.iter());
        }
        Box::new(std::iter::empty())
    }
}

impl<T: Clone> SpecificationItem<Vec<T>> {
    pub fn push(&mut self, value: T) {
        match self {
            SpecificationItem::Empty => *self = SpecificationItem::Inherent(vec![value]),
            SpecificationItem::Inherent(values) => values.push(value),
            SpecificationItem::Refined(_, values) => values.push(value),
            SpecificationItem::Inherited(inherited) => {
                *self = SpecificationItem::Refined(inherited.clone(), vec![value])
            }
        }
    }
}

pub trait Refinable {
    fn refine(self, other: &Self) -> Self
    where
        Self: Sized;
}

impl<T: Debug + Clone + PartialEq> Refinable for SpecificationItem<T> {
    #[tracing::instrument(level = "trace", ret)]
    fn refine(self, other: &Self) -> Self
    where
        Self: Sized,
    {
        use SpecificationItem::*;
        let other_val = match other {
            Empty => unreachable!("Trait spec should never be empty"),
            Inherent(val) => val,
            Inherited(val) => val,
            Refined(_, _) => panic!("Can not refine with a refined item"),
        };

        match self {
            Empty => Inherited(other_val.clone()),
            Inherent(val) | Inherited(val) => Refined(other_val.clone(), val),
            Refined(from, val) if &from == other_val => Refined(from, val),
            Refined(_, _) => panic!("Can not refine this refined item"),
        }
    }
}

impl Refinable for ProcedureSpecification {
    fn refine(self, other: &Self) -> Self {
        // Unspecified trait specs should be treated as a default value instead of nothing
        // See issue-1022
        type SpecVec<T> = SpecificationItem<Vec<T>>;
        static EMPTYL: SpecVec<DefId> = SpecificationItem::Inherent(vec![]);
        static EMPTYP: SpecVec<Pledge> = SpecificationItem::Inherent(vec![]);
        fn replace_empty<'a, T>(empty: &'a SpecVec<T>, spec: &'a SpecVec<T>) -> &'a SpecVec<T> {
            match spec {
                SpecificationItem::Empty => empty,
                other => other,
            }
        }
        ProcedureSpecification {
            source: self.source,
            pres: self.pres.refine(replace_empty(&EMPTYL, &other.pres)),
            posts: self.posts.refine(replace_empty(&EMPTYL, &other.posts)),
            broken_pres: self
                .broken_pres
                .refine(replace_empty(&EMPTYL, &other.broken_pres)),
            broken_posts: self
                .broken_posts
                .refine(replace_empty(&EMPTYL, &other.broken_posts)),
            pledges: self.pledges.refine(replace_empty(&EMPTYP, &other.pledges)),
            kind: self.kind.refine(&other.kind),
            trusted: self.trusted.refine(&other.trusted),
            no_panic: self.no_panic.refine(&other.no_panic),
            no_panic_ensures_postcondition: self
                .no_panic_ensures_postcondition
                .refine(&other.no_panic_ensures_postcondition),
            terminates: self.terminates.refine(&other.terminates),
            purity: self.purity.refine(&other.purity),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod refinement {
        use crate::specs::typed::{Refinable, SpecificationItem};
        use SpecificationItem::{Empty, Inherent, Inherited, Refined};

        macro_rules! refine_success_tests {
            ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                fn $name() {
                    let (from, with, expected) = $value;
                    let result = from.refine(&with);
                    assert_eq!(result, expected);
                }
            )*
            }
        }

        macro_rules! refine_fail_tests {
            ($($name:ident: $value:expr,)*) => {
            $(
                #[test]
                #[should_panic]
                fn $name() {
                    let (from, with) = $value;
                    from.refine(&with);
                }
            )*
            }
        }

        refine_success_tests!(
            refine_from_empty_with_inherent: (Empty, Inherent(1), Inherited(1)),
            refine_from_empty_with_inherited: (Empty, Inherited(1), Inherited(1)),
        );

        refine_fail_tests!(
            refine_from_empty_with_refined: (Empty, Refined(1,2)),
        );

        refine_success_tests!(
            refine_from_inherent_with_inherent: (Inherent(1), Inherent(2), Refined(2, 1)),
            refine_from_inherent_with_inherited: (Inherent(1), Inherited(2), Refined(2, 1)),
        );

        refine_fail_tests!(
            refine_from_inherent_with_refined: (Inherent(1), Refined(2,3)),
        );

        refine_success_tests!(
            refine_from_inherited_with_inherent: (Inherited(1), Inherent(2), Refined(2, 1)),
            refine_from_inherited_with_inherited: (Inherited(1), Inherited(2), Refined(2, 1)),
        );

        refine_fail_tests!(
            refine_from_inherited_with_refined: (Inherited(1), Refined(2,3)),
        );

        refine_success_tests!(
            // Generally, we can not refine a refined item.
            // In this case it is possible, because the refined-from part does not change.
            refine_from_refined_with_inherited_refinable: (Refined(1, 2), Inherited(1), Refined(1, 2)),
        );

        refine_fail_tests!(
            refine_from_refined_with_inherent: (Refined(1, 2), Inherent(3)),
            refine_from_refined_with_inherited_unrefinable: (Refined(1, 2), Inherited(3)),
            refine_from_refined_with_refined: (Refined(1, 2), Refined(3,4)),
        );
    }

    mod specification_item {
        use crate::specs::typed::SpecificationItem;

        #[test]
        fn set_value_of_empty() {
            let mut item: SpecificationItem<i32> = SpecificationItem::Empty;
            item.set(1);
            assert!(matches!(item, SpecificationItem::Inherent(1)));
        }

        #[test]
        fn set_value_of_inherent() {
            let mut item = SpecificationItem::Inherent(1);
            item.set(2);
            assert!(matches!(item, SpecificationItem::Inherent(2)));
        }

        #[test]
        fn set_value_of_inherited() {
            let mut item = SpecificationItem::Inherited(1);
            item.set(2);
            assert!(matches!(item, SpecificationItem::Refined(1, 2)));
        }

        #[test]
        fn set_value_of_refined() {
            let mut item = SpecificationItem::Refined(1, 2);
            item.set(3);
            assert!(matches!(item, SpecificationItem::Refined(1, 3)));
        }

        #[test]
        fn push_value_to_empty() {
            let mut item: SpecificationItem<Vec<i32>> = SpecificationItem::Empty;
            item.push(1);
            let vec = item.expect_inherent();
            assert_eq!(vec, &vec![1]);
        }

        #[test]
        fn push_value_to_inherent() {
            let mut item = SpecificationItem::Inherent(vec![1]);
            item.push(2);
            let vec = item.expect_inherent();
            assert_eq!(vec, &vec![1, 2]);
        }

        #[test]
        fn push_value_to_inherited() {
            let mut item = SpecificationItem::Inherited(vec![1, 2]);
            item.push(3);
            let (refined_from, refined) = item.expect_refined();
            assert_eq!(refined_from, &vec![1, 2]);
            assert_eq!(refined, &vec![3]);
        }

        #[test]
        fn push_value_to_refined() {
            let mut item = SpecificationItem::Refined(vec![1, 2], vec![3, 4]);
            item.push(5);
            let (refined_from, refined) = item.expect_refined();
            assert_eq!(refined_from, &vec![1, 2]);
            assert_eq!(refined, &vec![3, 4, 5]);
        }
    }

    mod specification_item_kind {
        use super::*;
        use ProcedureSpecificationKind::*;
        use SpecificationItem::*;

        mod invalid_refinements {
            use super::*;

            #[test]
            fn refine_impure_with_predicate() {
                let item = Refined(Impure, Predicate(None));
                let result = item.validate().expect_err("Expected error");
                assert!(matches!(
                    result,
                    ProcedureSpecificationKindError::InvalidSpecKindRefinement(_, _)
                ));
            }

            #[test]
            fn refine_pure_with_impure() {
                let item = Refined(Pure, Impure);
                let result = item.validate().expect_err("Expected error");
                assert!(matches!(
                    result,
                    ProcedureSpecificationKindError::InvalidSpecKindRefinement(_, _)
                ));
            }

            #[test]
            fn refine_pure_with_predicate() {
                let item = Refined(Pure, Predicate(None));
                let result = item.validate().expect_err("Expected error");
                assert!(matches!(
                    result,
                    ProcedureSpecificationKindError::InvalidSpecKindRefinement(_, _)
                ));
            }

            #[test]
            fn refine_predicate_with_pure() {
                let item = Refined(Predicate(None), Pure);
                let result = item.validate().expect_err("Expected error");
                assert!(matches!(
                    result,
                    ProcedureSpecificationKindError::InvalidSpecKindRefinement(_, _)
                ));
            }

            #[test]
            fn refine_predicate_with_impure() {
                let item = Refined(Predicate(None), Impure);
                let result = item.validate().expect_err("Expected error");
                assert!(matches!(
                    result,
                    ProcedureSpecificationKindError::InvalidSpecKindRefinement(_, _)
                ));
            }
        }

        mod is_impure {
            use super::*;

            macro_rules! impure_checks {
                    ($($name:ident: $value:expr,)*) => {
                        $(
                            #[test]
                            fn $name() {
                                let (item, expected) = $value;
                                let item: SpecificationItem<ProcedureSpecificationKind> = item;
                                let result = item.is_impure().expect("Expected impure");
                                assert_eq!(result, expected);
                            }
                        )*
                    }
                }

            impure_checks!(
                    empty: (Empty, true),
                    inherent_impure: (Inherent(Impure), true),
                    inherent_pure: (Inherent(Pure), false),
                    inherent_predicate: (Inherent(Predicate(None)), false),
                    inherited_impure: (Inherited(Impure), true),
                    inherited_pure: (Inherited(Pure), false),
                    inherited_predicate: (Inherited(Predicate(None)), false),
                    refined_impure_parent_impure_child: (Refined(Impure, Impure), true),
                    refined_impure_parent_pure_child: (Refined(Impure, Pure), false),
                    refined_pure_parent_with_pure_child: (Refined(Pure, Pure), false),
                    refined_predicate_parent_with_predicate_child: (Refined(Predicate(None), Predicate(None)), false),
            );
        }

        mod is_pure {
            use super::*;

            macro_rules! pure_checks {
                    ($($name:ident: $value:expr,)*) => {
                        $(
                            #[test]
                            fn $name() {
                                let (item, expected) = $value;
                                let item: SpecificationItem<ProcedureSpecificationKind> = item;
                                let result = item.is_pure().expect("Expected pure");
                                assert_eq!(result, expected);
                            }
                        )*
                    }
                }

            pure_checks!(
                    empty: (Empty, false),
                    inherent_impure: (Inherent(Impure), false),
                    inherent_pure: (Inherent(Pure), true),
                    inherent_predicate: (Inherent(Predicate(None)), true),
                    inherited_impure: (Inherited(Impure), false),
                    inherited_pure: (Inherited(Pure), true),
                    inherited_predicate: (Inherited(Predicate(None)), true),
                    refined_impure_parent_impure_child: (Refined(Impure, Impure), false),
                    refined_impure_parent_pure_child: (Refined(Impure, Pure), true),
                    refined_pure_parent_with_pure: (Refined(Pure, Pure), true),
                    refined_predicate_parent_with_predicate_child: (Refined(Predicate(None), Predicate(None)), true),
            );
        }
    }
}
