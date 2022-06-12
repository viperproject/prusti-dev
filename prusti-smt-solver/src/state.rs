use csv::Writer;

use crate::{
    error::Error,
    types::{Level, QuantifierId, TermId},
};
use std::collections::HashMap;

pub(crate) struct Quantifier {
    name: String,
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
    removed_quantifiers: HashMap<QuantifierId, usize>,
    /// Popped labels.
    labels: Vec<String>,
}

#[derive(Default)]
pub(crate) struct State {
    quantifiers: HashMap<QuantifierId, Quantifier>,
    /// The currently instantiated quantifiers at a given level.
    quantifiers_matched_events: HashMap<QuantifierId, Vec<QuantifierMatchedEvent>>,
    /// How many times each quantifier was matched (ignoring push/pop).
    total_quantifiers_matched_counters: HashMap<QuantifierId, usize>,
    /// How many instantiations we had of each quantifier.
    max_quantifier_matched_event_counters: HashMap<QuantifierId, usize>,
    term_used_in_trigger_events: HashMap<QuantifierId, Vec<TermUsedInTriggerEvent>>,
    max_term_used_in_trigger_event_counters: HashMap<QuantifierId, usize>,
    /// Quantifiers that the triggered by exactly the same term multiple times.
    /// (Push/pop is taken into account.)
    multi_term_quantifiers: HashMap<QuantifierId, Vec<TermId>>,
    /// The current trace through CFG.
    trace: Vec<BasicBlockVisitedEvent>,
    largest_pop: LargestPop,
    current_active_scopes_count: Level,
}

impl State {
    pub(crate) fn register_quantifier(&mut self, quantifier_id: QuantifierId, name: String) {
        self.quantifiers.insert(quantifier_id, Quantifier { name });
        self.quantifiers_matched_events
            .insert(quantifier_id, Vec::new());
        self.total_quantifiers_matched_counters
            .insert(quantifier_id, 0);
        self.max_quantifier_matched_event_counters
            .insert(quantifier_id, 0);
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

    pub(crate) fn register_matched_trigger_term(
        &mut self,
        quantifier_id: QuantifierId,
        term_id: TermId,
    ) -> Result<(), Error> {
        let term_used_in_trigger_events = &mut self
            .term_used_in_trigger_events
            .get_mut(&quantifier_id)
            .unwrap_or_else(|| panic!("quantifier_id: {}", quantifier_id));
        if term_used_in_trigger_events
            .iter()
            .any(|event| event.term_id == term_id)
        {
            if quantifier_id == 485 && term_id == 268 {
                eprintln!("events: {:?}", term_used_in_trigger_events);
            }
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

    pub(crate) fn active_scopes_count(&self) -> Level {
        self.current_active_scopes_count
    }

    pub(crate) fn push_scope(&mut self) {
        self.current_active_scopes_count += 1;
    }

    pub(crate) fn pop_scopes(&mut self, scopes_to_pop: u32) {
        self.current_active_scopes_count -= scopes_to_pop;
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
        let mut removed_quantifiers = HashMap::new();
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
        }
    }

    pub(crate) fn write_statistics(&self, input_file: &str) {
        {
            // The number of trigger matches per quantifier.
            let mut writer = Writer::from_path(format!("{}.triggers.csv", input_file)).unwrap();
            let mut counts: Vec<_> = self
                .max_term_used_in_trigger_event_counters
                .iter()
                .map(|(quantifier_id, counter)| (*counter, *quantifier_id))
                .collect();
            counts.sort();
            writer
                .write_record(&["Quantifier ID", "Quantifier Name", "Trigger Count"])
                .unwrap();
            for (counter, quantifier_id) in counts {
                writer
                    .write_record(&[
                        &quantifier_id.to_string(),
                        &self.quantifiers[&quantifier_id].name,
                        &counter.to_string(),
                    ])
                    .unwrap();
                // eprintln!(
                //     "#{:<7} {:>50}: {:>5}",

                // );
            }
        }

        {
            // The quantifiers that were matched multiple times with the same
            // trigger.
            let mut writer =
                Writer::from_path(format!("{}.multi-triggers.csv", input_file)).unwrap();
            let mut multi_term_instantiation_counts: Vec<_> = self
                .multi_term_quantifiers
                .iter()
                .map(|(quantifier_id, terms)| (terms.len(), *quantifier_id))
                .collect();
            multi_term_instantiation_counts.sort();
            writer
                .write_record(&["Quantifier ID", "Quantifier Name", "Trigger Count"])
                .unwrap();
            for (counter, quantifier_id) in multi_term_instantiation_counts {
                writer
                    .write_record(&[
                        &quantifier_id.to_string(),
                        &self.quantifiers[&quantifier_id].name,
                        &counter.to_string(),
                    ])
                    .unwrap();
                // eprintln!(
                //     "#{:<7} {:>50}: {:>5}",
                //     quantifier_id, self.quantifiers[&quantifier_id].name, counter
                // );
            }
        }

        {
            // The number of quantifier matches.
            let mut writer = Writer::from_path(format!("{}.matches.csv", input_file)).unwrap();
            let mut counts: Vec<_> = self
                .max_quantifier_matched_event_counters
                .iter()
                .map(|(quantifier_id, counter)| (*counter, *quantifier_id))
                .collect();
            counts.sort();
            writer
                .write_record(&[
                    "Quantifier ID",
                    "Quantifier Name",
                    "Matches",
                    "Total Matches",
                ])
                .unwrap();
            for (counter, quantifier_id) in counts {
                let total = self.total_quantifiers_matched_counters[&quantifier_id];
                writer
                    .write_record(&[
                        &quantifier_id.to_string(),
                        &self.quantifiers[&quantifier_id].name,
                        &counter.to_string(),
                        &total.to_string(),
                    ])
                    .unwrap();
                // eprintln!(
                //     "#{:<7} {:>50}: {:>5} ({})",
                //     quantifier_id, self.quantifiers[&quantifier_id].name, counter, total
                // );
            }
        }

        {
            eprintln!("The largest number of quantifier matches removed in a single “pop {}” operation: {}", self.largest_pop.active_scopes_popped, self.largest_pop.quantifier_matches_removed);
            // The number of quantifier matches poped in the largest match.
            let mut writer =
                Writer::from_path(format!("{}.largest_pop_matches.csv", input_file)).unwrap();
            let mut counts: Vec<_> = self
                .largest_pop
                .removed_quantifiers
                .iter()
                .map(|(quantifier_id, counter)| (*counter, *quantifier_id))
                .collect();
            counts.sort();
            writer
                .write_record(&["Quantifier ID", "Quantifier Name", "Matches Removed"])
                .unwrap();
            for (counter, quantifier_id) in counts {
                writer
                    .write_record(&[
                        &quantifier_id.to_string(),
                        &self.quantifiers[&quantifier_id].name,
                        &counter.to_string(),
                    ])
                    .unwrap();
                // eprintln!(
                //     "#{:<7} {:>50}: {:>5} ({})",
                //     quantifier_id, self.quantifiers[&quantifier_id].name, counter, total
                // );
            }
        }
    }
}
