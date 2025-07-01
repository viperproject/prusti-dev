use std::collections::{btree_set::IntoIter, BTreeSet};

use prusti_rustc_interface::{ast::Attribute, data_structures::fx::FxHashMap, hir::Mutability};

use crate::utils::{read_prusti_attr, read_prusti_attrs};

use super::ExternSpecification;

pub fn get_translated_specs(
    attrs: &[Attribute],
    function_name: &str,
    mutability: Mutability,
) -> Option<(String, String, (String, String))> {
    let collector = read_prusti_attr("translated_spec_collector", attrs)?;
    let extern_source_file = read_prusti_attr("extern_source_file", attrs)?;
    let collector = get_translated_spec_collector(&collector)?;
    let attribute_values = collector
        .get_supported_attributes()
        .iter()
        .map(|attr| {
            (
                attr.to_owned().to_owned(),
                read_prusti_attrs(attr, attrs)
                    .into_iter()
                    .filter(|attr| !attr.is_empty())
                    .collect(),
            )
        })
        .collect::<FxHashMap<String, Vec<String>>>();
    Some((
        extern_source_file,
        function_name.replace("prusti_extern_spec_", ""),
        collector.collect_translated_specs(attribute_values, mutability),
    ))
}

pub trait TranslatedSpecCollector {
    fn get_supported_attributes(&self) -> &[&'static str];

    fn collect_translated_specs(
        &self,
        values_of_supported_attributes: FxHashMap<String, Vec<String>>,
        mutability: Mutability,
    ) -> ExternSpecification;
}

pub fn get_translated_spec_collector(
    translated_spec_collector: &str,
) -> Option<Box<dyn TranslatedSpecCollector>> {
    match translated_spec_collector {
        "verifast" => Some(Box::new(VerifastSpecCollector)),
        _ => None,
    }
}

struct VerifastSpecCollector;
const VERIFAST_PRECALL_FIELD_BINDINGS: &'static str = "verifast_precall_field_bindings";
const VERIFAST_POSTCALL_FIELD_BINDINGS: &'static str = "verifast_postcall_field_bindings";
const VERIFAST_PRECONDITION: &'static str = "verifast_precondition";
const VERIFAST_POSTCONDITION: &'static str = "verifast_postcondition";
const VERIFAST_ATTRIBUTES: [&'static str; 4] = [
    VERIFAST_PRECALL_FIELD_BINDINGS,
    VERIFAST_POSTCALL_FIELD_BINDINGS,
    VERIFAST_PRECONDITION,
    VERIFAST_POSTCONDITION,
];

impl TranslatedSpecCollector for VerifastSpecCollector {
    fn get_supported_attributes(&self) -> &[&'static str] {
        &VERIFAST_ATTRIBUTES
    }

    fn collect_translated_specs(
        &self,
        values_of_supported_attributes: FxHashMap<String, Vec<String>>,
        mutability: Mutability,
    ) -> ExternSpecification {
        let mut separated_conjuncts: FxHashMap<String, BTreeSet<String>> =
            values_of_supported_attributes
                .into_iter()
                .map(|(key, values)| {
                    (
                        key,
                        values
                            .iter()
                            .flat_map(|value| value.split(" &*& "))
                            .map(|value| value.to_owned())
                            .collect(),
                    )
                })
                .collect();

        if matches!(mutability, Mutability::Not) {
            let precall_bindings = separated_conjuncts
                .get(VERIFAST_POSTCALL_FIELD_BINDINGS)
                .map(|postcall_bindings| {
                    postcall_bindings
                        .iter()
                        .map(|binding| binding.replace("_post_", "_pre_"))
                        .collect::<BTreeSet<_>>()
                })
                .unwrap_or_default();

            separated_conjuncts
                .insert(VERIFAST_PRECALL_FIELD_BINDINGS.to_owned(), precall_bindings);

            add_fractional_permissions(
                &mut separated_conjuncts,
                VERIFAST_PRECALL_FIELD_BINDINGS,
                true,
            );
            add_fractional_permissions(
                &mut separated_conjuncts,
                VERIFAST_POSTCALL_FIELD_BINDINGS,
                false,
            );
        }

        (
            merge(
                &mut separated_conjuncts,
                VERIFAST_PRECALL_FIELD_BINDINGS,
                VERIFAST_PRECONDITION,
            ),
            merge(
                &mut separated_conjuncts,
                VERIFAST_POSTCALL_FIELD_BINDINGS,
                VERIFAST_POSTCONDITION,
            ),
        )
    }
}

fn add_fractional_permissions(
    separated_conjuncts: &mut FxHashMap<String, BTreeSet<String>>,
    bindings_key: &str,
    add_q_mark: bool,
) {
    separated_conjuncts
        .entry(bindings_key.to_owned())
        .and_modify(|values| {
            *values = values
                .iter()
                .enumerate()
                .map(|(i, b)| format!("[{}_frac_{i}]{b}", if add_q_mark { "?" } else { "" }))
                .collect();
        });
}

fn merge(
    separated_conjuncts: &mut FxHashMap<String, BTreeSet<String>>,
    bindings_key: &str,
    conjuncts_key: &str,
) -> String {
    take(separated_conjuncts, bindings_key)
        .chain(take(separated_conjuncts, conjuncts_key))
        .reduce(|mut acc, ref value| {
            acc.push_str(" &*& ");
            acc.push_str(value);
            acc
        })
        .unwrap_or("true".to_owned())
}

fn take(
    separated_conjuncts: &mut FxHashMap<String, BTreeSet<String>>,
    key: &str,
) -> IntoIter<String> {
    separated_conjuncts
        .remove(key)
        .unwrap_or_default()
        .into_iter()
}
