use crate::{
    error::Error,
    parser::{EventKind, TheoryKind},
    types::{Level, QuantifierId, TermId, BUILTIN_QUANTIFIER_ID},
};
use csv::Writer;
use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt::Write;

pub(crate) struct Quantifier {
    name: String,
}

pub(crate) enum Term {
    FunctionApplication { name: String, args: Vec<TermId> },
    Variable { index: u32 },
    AttachMeaning { ident: String, value: String },
}

#[derive(Debug)]
/// The specified term was used to trigger a quantifier instantiation.
pub(crate) struct TermUsedInTriggerEvent {
    level: Level,
    term_id: TermId,
}

impl TermUsedInTriggerEvent {
    fn new(level: Level, term_id: TermId) -> Self {
        Self { level, term_id }
    }
}

#[derive(Debug)]
/// The quantifier was matched event.
pub(crate) struct QuantifierMatchedEvent {
    level: Level,
    counter: usize,
}

impl QuantifierMatchedEvent {
    fn new(level: Level) -> Self {
        Self { level, counter: 1 }
    }
}

#[derive(Debug)]
/// The quantifier was instantiated event.
pub(crate) struct QuantifierInstanceEvent {
    level: Level,
    counter: usize,
}

impl QuantifierInstanceEvent {
    fn new(level: Level) -> Self {
        Self { level, counter: 1 }
    }
}

#[derive(Debug, Clone)]
/// The basic block label was visited event.
pub(crate) struct BasicBlockVisitedEvent {
    level: Level,
    label: String,
}

/// What is the largest number of quantifier matches removed with a single pop
/// operation.
#[derive(Default)]
struct LargestPop {
    /// How many quantifier matches were removed.
    quantifier_matches_removed: usize,
    /// How many active scopes were popped with that pop operation?
    active_scopes_popped: Level,
    /// How many instances of each quantifier were removed in that pop?
    removed_quantifiers: FxHashMap<QuantifierId, usize>,
    /// Popped labels.
    labels: Vec<BasicBlockVisitedEvent>,
    /// Labels leading to the popped labels.
    trace_prefix: Vec<BasicBlockVisitedEvent>,
}

#[derive(Default)]
pub(crate) struct State {
    quantifiers: FxHashMap<QuantifierId, Quantifier>,
    terms: FxHashMap<TermId, Term>,
    /// Frequencies of each event kind.
    event_kind_counters: FxHashMap<EventKind, usize>,
    /// The currently matched quantifiers (via [new-match]) at a given level.
    quantifiers_matched_events: FxHashMap<QuantifierId, Vec<QuantifierMatchedEvent>>,
    /// The currently discovered quantifiers (via [inst-discovered]) at a given level.
    quantifiers_inst_disovered_events: FxHashMap<TheoryKind, Vec<QuantifierMatchedEvent>>,
    /// How many times each quantifier was matched (ignoring push/pop).
    total_quantifiers_matched_counters: FxHashMap<QuantifierId, usize>,
    /// How many times each quantifier was discovered (ignoring push/pop).
    total_quantifiers_inst_disovered_counters: FxHashMap<TheoryKind, usize>,
    /// How many instantiations we had of each quantifier.
    max_quantifier_matched_event_counters: FxHashMap<QuantifierId, usize>,
    /// How many instantiations we had of each theory.
    max_quantifier_inst_discovered_event_counters: FxHashMap<TheoryKind, usize>,
    unique_quantifier_triggers: FxHashMap<QuantifierId, FxHashSet<TermId>>,
    term_used_in_trigger_events: FxHashMap<QuantifierId, Vec<TermUsedInTriggerEvent>>,
    max_term_used_in_trigger_event_counters: FxHashMap<QuantifierId, usize>,
    /// Quantifiers that the triggered by exactly the same term multiple times.
    /// (Push/pop is taken into account.)
    multi_term_quantifiers: FxHashMap<QuantifierId, Vec<TermId>>,
    /// A total number of times the quantifiers were instantiated via [instance]
    /// (ignoring push/pop).
    total_quantifiers_instance_counters: usize,
    /// How many time quantifiers were instantiated on the current trace.
    quantifiers_instance_events: Vec<QuantifierInstanceEvent>,
    /// A maximum number of times the quantifiers were instantiated via [instance]
    /// on a specific trace.
    max_quantifier_instance_event_counters: usize,
    /// The current trace through CFG.
    trace: Vec<BasicBlockVisitedEvent>,
    largest_pop: LargestPop,
    current_active_scopes_count: Level,
    traced_quantifier: Option<QuantifierId>,
    traced_quantifier_triggers: Option<String>,
    decide_and_or_terms: Vec<(TermId, String, TermId, String)>,
}

impl State {
    pub(crate) fn register_event_kind(&mut self, event_kind: EventKind) {
        let entry = self.event_kind_counters.entry(event_kind).or_insert(0);
        *entry += 1;
    }

    pub(crate) fn register_label(&mut self, label: String) {
        self.trace.push(BasicBlockVisitedEvent {
            level: self.current_active_scopes_count,
            label,
        });
    }

    pub(crate) fn register_quantifier(&mut self, quantifier_id: QuantifierId, name: String) {
        self.quantifiers.insert(quantifier_id, Quantifier { name });
        self.quantifiers_matched_events
            .insert(quantifier_id, Vec::new());
        self.total_quantifiers_matched_counters
            .insert(quantifier_id, 0);
        self.max_quantifier_matched_event_counters
            .insert(quantifier_id, 0);
        self.unique_quantifier_triggers
            .insert(quantifier_id, FxHashSet::default());
        self.term_used_in_trigger_events
            .insert(quantifier_id, Vec::new());
        self.max_term_used_in_trigger_event_counters
            .insert(quantifier_id, 0);
    }

    pub(crate) fn register_matched_quantifier(
        &mut self,
        quantifier_id: QuantifierId,
    ) -> Result<(), Error> {
        *self
            .total_quantifiers_matched_counters
            .get_mut(&quantifier_id)
            .unwrap() += 1;
        let events = self
            .quantifiers_matched_events
            .get_mut(&quantifier_id)
            .unwrap();
        if let Some(last) = events.last_mut() {
            if last.level == self.current_active_scopes_count {
                last.counter += 1;
                return Ok(());
            }
        }
        events.push(QuantifierMatchedEvent::new(
            self.current_active_scopes_count,
        ));
        Ok(())
    }

    pub(crate) fn register_theory(&mut self, theory: TheoryKind) {
        self.quantifiers_inst_disovered_events
            .insert(theory, Vec::new());
        self.total_quantifiers_inst_disovered_counters
            .insert(theory, 0);
        self.max_quantifier_inst_discovered_event_counters
            .insert(theory, 0);
    }

    pub(crate) fn register_inst_discovered(
        &mut self,
        theory_kind: TheoryKind,
    ) -> Result<(), Error> {
        *self
            .total_quantifiers_inst_disovered_counters
            .get_mut(&theory_kind)
            .unwrap() += 1;
        let events = self
            .quantifiers_inst_disovered_events
            .get_mut(&theory_kind)
            .unwrap();
        if let Some(last) = events.last_mut() {
            if last.level == self.current_active_scopes_count {
                last.counter += 1;
                return Ok(());
            }
        }
        events.push(QuantifierMatchedEvent::new(
            self.current_active_scopes_count,
        ));
        Ok(())
    }

    pub(crate) fn register_matched_trigger_term(
        &mut self,
        quantifier_id: QuantifierId,
        term_id: TermId,
    ) -> Result<(), Error> {
        self.trace_quantifier_trigger(quantifier_id, term_id)?;
        self.unique_quantifier_triggers
            .get_mut(&quantifier_id)
            .unwrap()
            .insert(term_id);
        let term_used_in_trigger_events = &mut self
            .term_used_in_trigger_events
            .get_mut(&quantifier_id)
            .unwrap_or_else(|| panic!("quantifier_id: {quantifier_id}"));
        if term_used_in_trigger_events
            .iter()
            .any(|event| event.term_id == term_id)
        {
            let terms = self
                .multi_term_quantifiers
                .entry(quantifier_id)
                .or_default();
            terms.push(term_id);
        }
        term_used_in_trigger_events.push(TermUsedInTriggerEvent::new(
            self.current_active_scopes_count,
            term_id,
        ));
        Ok(())
    }

    fn trace_quantifier_trigger(
        &mut self,
        quantifier_id: QuantifierId,
        term_id: TermId,
    ) -> Result<(), Error> {
        if let Some(traced_quantifier_id) = self.traced_quantifier {
            if !self.unique_quantifier_triggers[&quantifier_id].contains(&term_id)
                && traced_quantifier_id == quantifier_id
            {
                let mut buf = self.traced_quantifier_triggers.take().unwrap();
                write!(buf, "{term_id},").unwrap();
                self.render_term(term_id, &mut buf, 30).unwrap();
                writeln!(buf).unwrap();
                self.traced_quantifier_triggers = Some(buf);
            }
        }
        Ok(())
    }

    pub(crate) fn mark_quantifier_for_tracing(&mut self, quantifier: Option<QuantifierId>) {
        assert!(self.traced_quantifier.is_none());
        self.traced_quantifier = quantifier;
        if let Some(quantifier) = quantifier {
            let mut buf = String::new();
            writeln!(buf, "{quantifier},").unwrap();
            self.traced_quantifier_triggers = Some(buf);
        }
    }

    pub(crate) fn register_instance(&mut self) -> Result<(), Error> {
        self.total_quantifiers_instance_counters += 1;
        let events = &mut self.quantifiers_instance_events;
        if let Some(last) = events.last_mut() {
            if last.level == self.current_active_scopes_count {
                last.counter += 1;
                return Ok(());
            }
        }
        events.push(QuantifierInstanceEvent::new(
            self.current_active_scopes_count,
        ));
        Ok(())
    }

    pub(crate) fn register_term_function_application(
        &mut self,
        term_id: TermId,
        name: String,
        args: Vec<TermId>,
    ) {
        self.terms
            .insert(term_id, Term::FunctionApplication { name, args });
    }

    pub(crate) fn register_term_bound_variable(&mut self, term_id: TermId, index: u32) {
        self.terms.insert(term_id, Term::Variable { index });
    }

    pub(crate) fn register_term_attach_meaning(
        &mut self,
        term_id: TermId,
        ident: String,
        value: String,
    ) {
        self.terms
            .insert(term_id, Term::AttachMeaning { ident, value });
    }

    pub(crate) fn register_decide_and_or_term(&mut self, term_id: TermId, undef_child_id: TermId) {
        let mut rendered_term = String::new();
        self.render_term(term_id, &mut rendered_term, 30).unwrap();
        let mut rendered_undef_child = String::new();
        self.render_term(undef_child_id, &mut rendered_undef_child, 30)
            .unwrap();
        self.decide_and_or_terms.push((
            term_id,
            rendered_term,
            undef_child_id,
            rendered_undef_child,
        ));
    }

    pub(crate) fn active_scopes_count(&self) -> Level {
        self.current_active_scopes_count
    }

    pub(crate) fn push_scope(&mut self) {
        self.current_active_scopes_count += 1;
    }

    pub(crate) fn pop_scopes(&mut self, scopes_to_pop: u32) {
        self.current_active_scopes_count -= scopes_to_pop;

        let max_instances = self
            .quantifiers_instance_events
            .iter()
            .map(|event| event.counter)
            .sum();
        if self.max_quantifier_instance_event_counters < max_instances {
            self.max_quantifier_instance_event_counters = max_instances;
        }
        while let Some(event) = self.quantifiers_instance_events.last() {
            if event.level > self.current_active_scopes_count {
                self.quantifiers_instance_events.pop();
            } else {
                break;
            }
        }

        for (quantifier_id, term_used_in_trigger_events) in &mut self.term_used_in_trigger_events {
            let max = self
                .max_term_used_in_trigger_event_counters
                .get_mut(quantifier_id)
                .unwrap();
            if *max < term_used_in_trigger_events.len() {
                *max = term_used_in_trigger_events.len();
            }
            while let Some(event) = term_used_in_trigger_events.last() {
                if event.level > self.current_active_scopes_count {
                    term_used_in_trigger_events.pop();
                } else {
                    break;
                }
            }
        }

        let mut removed_labels = Vec::new();
        while let Some(event) = self.trace.last() {
            if event.level > self.current_active_scopes_count {
                removed_labels.push(self.trace.pop().unwrap());
            } else {
                break;
            }
        }

        for (theory, events) in &mut self.quantifiers_inst_disovered_events {
            let max = self
                .max_quantifier_inst_discovered_event_counters
                .get_mut(theory)
                .unwrap();
            let sum = events.iter().map(|event| event.counter).sum();
            if *max < sum {
                *max = sum;
            }
            while let Some(event) = events.last() {
                if event.level > self.current_active_scopes_count {
                    events.pop();
                } else {
                    break;
                }
            }
        }

        let mut removed_quantifiers = FxHashMap::default();
        let mut total_quantifier_matches_removed = 0;
        for (quantifier_id, events) in &mut self.quantifiers_matched_events {
            let max = self
                .max_quantifier_matched_event_counters
                .get_mut(quantifier_id)
                .unwrap();
            let sum = events.iter().map(|event| event.counter).sum();
            if *max < sum {
                *max = sum;
            }
            let mut quantifier_matches_removed = 0;
            while let Some(event) = events.last() {
                if event.level > self.current_active_scopes_count {
                    quantifier_matches_removed += event.counter;
                    events.pop();
                } else {
                    break;
                }
            }
            total_quantifier_matches_removed += quantifier_matches_removed;
            if quantifier_matches_removed > 0 {
                removed_quantifiers.insert(*quantifier_id, quantifier_matches_removed);
            }
        }

        if self.largest_pop.quantifier_matches_removed < total_quantifier_matches_removed {
            self.largest_pop.active_scopes_popped = scopes_to_pop;
            self.largest_pop.quantifier_matches_removed = total_quantifier_matches_removed;
            self.largest_pop.removed_quantifiers = removed_quantifiers;
            removed_labels.reverse();
            self.largest_pop.labels = removed_labels;
            self.largest_pop.trace_prefix = self.trace.clone();
        }
    }

    pub(crate) fn pop_all_scopes(&mut self) {
        self.pop_scopes(self.current_active_scopes_count);
    }

    fn render_term(&self, term_id: TermId, f: &mut impl Write, depth: u16) -> std::fmt::Result {
        if depth == 0 {
            write!(f, "…")?;
        } else if let Some(term) = self.terms.get(&term_id) {
            match term {
                Term::FunctionApplication { name, args } => {
                    if args.is_empty() {
                        write!(f, "{name}")?;
                    } else {
                        write!(f, "({name}")?;
                        for arg in args {
                            write!(f, " ")?;
                            self.render_term(*arg, f, depth - 1)?;
                        }
                        write!(f, ")")?;
                    }
                }
                Term::Variable { index } => {
                    write!(f, "var({index})")?;
                }
                Term::AttachMeaning { ident, value } => {
                    write!(f, "( {ident} {value} )")?;
                }
            }
        } else {
            write!(f, "n/a")?;
        }
        Ok(())
    }

    fn quantifier_matches_counts(&self) -> Vec<(usize, QuantifierId)> {
        let mut counts: Vec<_> = self
            .max_quantifier_matched_event_counters
            .iter()
            .map(|(quantifier_id, counter)| (*counter, *quantifier_id))
            .collect();
        counts.sort_unstable();
        counts
    }

    pub(crate) fn write_statistics(&self, input_file: &str) {
        {
            let mut writer = Writer::from_path(format!("{input_file}.event-kinds.csv")).unwrap();
            writer.write_record(["Event Kind", "Count"]).unwrap();
            for (event_kind, counter) in &self.event_kind_counters {
                writer
                    .write_record([format!("{event_kind:?}"), counter.to_string()])
                    .unwrap();
            }
        }

        {
            // [instance] – the number of quantifier instantiations.
            let mut writer = Writer::from_path(format!("{input_file}.instances.csv")).unwrap();
            writer
                .write_record([
                    "Total Quantifier Instance Count",
                    "Max Trace Quantifier Instance Count",
                ])
                .unwrap();
            writer
                .write_record([
                    self.total_quantifiers_instance_counters.to_string(),
                    self.max_quantifier_instance_event_counters.to_string(),
                ])
                .unwrap();
        }

        {
            // The number of trigger matches per quantifier.
            let mut writer = Writer::from_path(format!("{input_file}.triggers.csv")).unwrap();
            let mut counts: Vec<_> = self
                .max_term_used_in_trigger_event_counters
                .iter()
                .map(|(quantifier_id, counter)| (*counter, *quantifier_id))
                .collect();
            counts.sort_unstable();
            writer
                .write_record(["Quantifier ID", "Quantifier Name", "Trigger Count"])
                .unwrap();
            for (counter, quantifier_id) in counts {
                writer
                    .write_record([
                        &quantifier_id.to_string(),
                        &self.quantifiers[&quantifier_id].name,
                        &counter.to_string(),
                    ])
                    .unwrap();
            }
        }

        {
            // The number of unique triggers per quantifier.
            let mut writer =
                Writer::from_path(format!("{input_file}.unique-triggers.csv")).unwrap();
            let mut counts: Vec<_> = self
                .unique_quantifier_triggers
                .iter()
                .map(|(quantifier_id, terms)| (terms.len(), *quantifier_id))
                .collect();
            counts.sort_unstable();
            writer
                .write_record(["Quantifier ID", "Quantifier Name", "Unique trigger Count"])
                .unwrap();
            for (counter, quantifier_id) in counts {
                writer
                    .write_record([
                        &quantifier_id.to_string(),
                        &self.quantifiers[&quantifier_id].name,
                        &counter.to_string(),
                    ])
                    .unwrap();
            }
        }

        // { This seems to be useless and is very slow.
        //     // The unique triggers per quantifier.
        //     let mut writer =
        //         Writer::from_path(format!("{}.unique-trigger-terms.csv", input_file)).unwrap();
        //     writer
        //         .write_record(&["Quantifier ID", "Quantifier Name", "Term Id", "Trigger"])
        //         .unwrap();
        //     let mut term = String::new();
        //     for (quantifier_id, triggers) in &self.unique_quantifier_triggers {
        //         for trigger in triggers {
        //             term.clear();
        //             self.render_term(*trigger, &mut term, 10).unwrap();
        //             writer
        //                 .write_record(&[
        //                     &quantifier_id.to_string(),
        //                     &self.quantifiers[&quantifier_id].name,
        //                     &trigger.to_string(),
        //                     &term,
        //                 ])
        //                 .unwrap();
        //         }
        //     }
        // }

        {
            // The quantifiers that were matched multiple times with the same
            // trigger.
            let mut writer = Writer::from_path(format!("{input_file}.multi-triggers.csv")).unwrap();
            let mut multi_term_instantiation_counts: Vec<_> = self
                .multi_term_quantifiers
                .iter()
                .map(|(quantifier_id, terms)| (terms.len(), *quantifier_id))
                .collect();
            multi_term_instantiation_counts.sort_unstable();
            writer
                .write_record(["Quantifier ID", "Quantifier Name", "Trigger Count"])
                .unwrap();
            for (counter, quantifier_id) in multi_term_instantiation_counts {
                writer
                    .write_record([
                        &quantifier_id.to_string(),
                        &self.quantifiers[&quantifier_id].name,
                        &counter.to_string(),
                    ])
                    .unwrap();
            }
        }

        {
            // [new-match] – The number of quantifier matches.
            let mut writer = Writer::from_path(format!("{input_file}.matches.csv")).unwrap();
            let counts = self.quantifier_matches_counts();
            writer
                .write_record([
                    "Quantifier ID",
                    "Quantifier Name",
                    "Matches",
                    "Total Matches",
                ])
                .unwrap();
            for (counter, quantifier_id) in counts {
                let total = self.total_quantifiers_matched_counters[&quantifier_id];
                writer
                    .write_record([
                        &quantifier_id.to_string(),
                        &self.quantifiers[&quantifier_id].name,
                        &counter.to_string(),
                        &total.to_string(),
                    ])
                    .unwrap();
            }
        }

        {
            // [inst-discovered] – The number of quantifier instance discoveries.
            let mut writer =
                Writer::from_path(format!("{input_file}.inst-discoveries.csv")).unwrap();
            let mut counts: Vec<_> = self
                .max_quantifier_inst_discovered_event_counters
                .iter()
                .map(|(theory, counter)| (counter, *theory))
                .collect();
            counts.sort_unstable();
            writer
                .write_record(["Theory", "Discoveries", "Total Discoveries"])
                .unwrap();
            for (counter, theory) in counts {
                let total = self.total_quantifiers_inst_disovered_counters[&theory];
                writer
                    .write_record([
                        &format!("{theory:?}"),
                        &counter.to_string(),
                        &total.to_string(),
                    ])
                    .unwrap();
            }
        }

        {
            // [decide-and-or] – Case splits.
            let mut writer = Writer::from_path(format!("{input_file}.decide-and-or.csv")).unwrap();
            writer
                .write_record([
                    "TermId",
                    "Rendered Term",
                    "Undef child ID",
                    "Rendered undef child",
                ])
                .unwrap();
            for (term_id, rendered_term, child_id, rendered_child) in &self.decide_and_or_terms {
                writer
                    .write_record([
                        &term_id.to_string(),
                        rendered_term,
                        &child_id.to_string(),
                        rendered_child,
                    ])
                    .unwrap();
            }
        }

        {
            println!(
                "The largest number of quantifier matches removed in a single “pop {}” operation: {}",
                self.largest_pop.active_scopes_popped, self.largest_pop.quantifier_matches_removed
            );
            // The number of quantifier matches poped in the largest match.
            let mut writer =
                Writer::from_path(format!("{input_file}.largest_pop_matches.csv")).unwrap();
            let mut counts: Vec<_> = self
                .largest_pop
                .removed_quantifiers
                .iter()
                .map(|(quantifier_id, counter)| (*counter, *quantifier_id))
                .collect();
            counts.sort_unstable();
            writer
                .write_record(["Quantifier ID", "Quantifier Name", "Matches Removed"])
                .unwrap();
            for (counter, quantifier_id) in counts {
                writer
                    .write_record([
                        &quantifier_id.to_string(),
                        &self.quantifiers[&quantifier_id].name,
                        &counter.to_string(),
                    ])
                    .unwrap();
            }

            let mut label_writer =
                Writer::from_path(format!("{input_file}.largest_pop_labels.csv")).unwrap();
            label_writer
                .write_record(["Basic Block Label", "Level", "Was popped?"])
                .unwrap();
            for event in &self.largest_pop.trace_prefix {
                label_writer
                    .write_record([&event.label, &event.level.to_string(), "false"])
                    .unwrap();
            }
            for event in &self.largest_pop.labels {
                label_writer
                    .write_record([&event.label, &event.level.to_string(), "true"])
                    .unwrap();
            }
        }

        if let Some(quantifier_id) = self.traced_quantifier {
            let mut file = std::fs::File::create(format!(
                "{input_file}.quantifier-{quantifier_id}-triggers.csv"
            ))
            .unwrap();
            std::io::Write::write_all(
                &mut file,
                self.traced_quantifier_triggers.as_ref().unwrap().as_bytes(),
            )
            .unwrap();
        }
    }

    fn check_bounds_explanatory_quantifier_name(&self, quantifier_id: QuantifierId) -> String {
        if self.quantifiers[&quantifier_id].name.starts_with("k!") {
            format!(
                "{} (quantifiers with name k!<line> are defined on \
                <line>'th line of the smt2 file)",
                self.quantifiers[&quantifier_id].name
            )
        } else {
            self.quantifiers[&quantifier_id].name.clone()
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn check_bounds(
        &self,
        input_file: &str,
        quantifier_instantiations_ignore_builtin: bool,
        quantifier_instantiations_bound_global_kind: Option<u64>,
        quantifier_instantiations_bound_trace: Option<u64>,
        quantifier_instantiations_bound_trace_kind: Option<u64>,
        unique_triggers_bound: Option<u64>,
        unique_triggers_bound_total: Option<u64>,
    ) {
        if quantifier_instantiations_bound_trace.is_none()
            && quantifier_instantiations_bound_trace_kind.is_none()
            && quantifier_instantiations_bound_global_kind.is_none()
        {
            return;
        }
        let mut sum = 0;
        let mut violating_quantifiers = Vec::new();
        for (counter, quantifier_id) in self.quantifier_matches_counts() {
            if quantifier_id == BUILTIN_QUANTIFIER_ID && quantifier_instantiations_ignore_builtin {
                continue;
            }
            sum += counter;
            let total = self.total_quantifiers_matched_counters[&quantifier_id];
            if counter < total {
                if let Some(bound) = quantifier_instantiations_bound_trace_kind {
                    if counter > bound.try_into().unwrap() {
                        violating_quantifiers.push(format!(
                            "Quantifier {} (id={}) instantiated {} times in trace (allowed: {})",
                            self.check_bounds_explanatory_quantifier_name(quantifier_id),
                            quantifier_id,
                            counter,
                            bound,
                        ))
                    }
                }
            }
            if let Some(bound) = quantifier_instantiations_bound_global_kind {
                if counter > bound.try_into().unwrap() {
                    violating_quantifiers.push(format!(
                        "Quantifier {} (id={}) instantiated {} times in trace and in total (allowed: {})",
                        self.check_bounds_explanatory_quantifier_name(quantifier_id), quantifier_id, counter, bound,
                    ));
                }
            }
        }
        assert!(
            violating_quantifiers.is_empty(),
            "the number of allowed instantiations (in {}) were \
            exceeded by the following quantifiers:\n{}",
            input_file,
            violating_quantifiers.join("\n")
        );
        if let Some(bound) = quantifier_instantiations_bound_trace {
            assert!(
                sum <= bound.try_into().unwrap(),
                "the number of quantifier instantiations (in {input_file}) on a specific \
                trace ({sum}) exceeded the allowed bound ({bound})"
            );
        }
        let mut total_unique_triggers_count = 0;
        let mut violating_quantifiers = Vec::new();
        for (&quantifier_id, triggers) in &self.unique_quantifier_triggers {
            if quantifier_id == BUILTIN_QUANTIFIER_ID && quantifier_instantiations_ignore_builtin {
                continue;
            }
            let count = triggers.len();
            total_unique_triggers_count += count;
            if let Some(bound) = unique_triggers_bound {
                if count > bound.try_into().unwrap() {
                    violating_quantifiers.push(format!(
                        "Quantifier {} (id={}) has {} unique triggers (allowed: {})",
                        self.check_bounds_explanatory_quantifier_name(quantifier_id),
                        quantifier_id,
                        count,
                        bound,
                    ));
                }
            }
        }
        assert!(
            violating_quantifiers.is_empty(),
            "the number of allowed unique triggers (in {}) were \
            exceeded by the following quantifiers:\n{}",
            input_file,
            violating_quantifiers.join("\n")
        );
        if let Some(bound) = unique_triggers_bound_total {
            assert!(
                total_unique_triggers_count <= bound.try_into().unwrap(),
                "the number of unique triggers ({total_unique_triggers_count}) exceeded the allowed bound ({bound}) in {input_file}"
            );
        }
    }
}
