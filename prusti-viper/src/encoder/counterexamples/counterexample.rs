use prusti_interface::PrustiError;
use prusti_rustc_interface::span::Span;
use std::fmt;

/// Counterexample information for a single variable.
pub struct CounterexampleEntry {
    span: Span,
    /// Name of local variable or None for the result.
    name: Option<String>,
    /// Value in the prestate.
    initial_value: Option<Entry>,
    /// Value in the poststate (or at assertion failure).
    final_value: Entry,
}

impl CounterexampleEntry {
    pub fn with_one_value(span: Span, name: Option<String>, final_value: Entry) -> Self {
        CounterexampleEntry {
            span,
            name,
            initial_value: None,
            final_value,
        }
    }

    pub fn with_two_values(
        span: Span,
        name: Option<String>,
        initial_value: Entry,
        final_value: Entry,
    ) -> Self {
        CounterexampleEntry {
            span,
            name,
            initial_value: Some(initial_value),
            final_value,
        }
    }
}

/// Indents the debug output of the given value with "  " starting with the
/// second line.
fn indented_debug<T: std::fmt::Debug>(val: &T) -> String {
    format!("{val:#?}")
        .split('\n')
        .collect::<Vec<&str>>()
        .join("\n  ")
}

impl fmt::Display for CounterexampleEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "counterexample for ")?;
        if let Some(name) = &self.name {
            write!(f, "\"{name}\"")?;
        } else {
            write!(f, "result")?;
        }
        if let Some(initial_value) = &self.initial_value {
            write!(f, "\n  initial value: {}", indented_debug(&initial_value))?;
        }
        write!(
            f,
            "\n  final value:   {}",
            indented_debug(&self.final_value)
        )
    }
}

/// A concrete counterexample containing mapped values of arguments and locals
/// (the latter only for impure functions), as well as the result (if any).
pub struct Counterexample(Vec<CounterexampleEntry>);

impl Counterexample {
    pub fn new(entries: Vec<CounterexampleEntry>) -> Self {
        Self(entries)
    }

    /// Annotates a Prusti error with notes for any variable present in the
    /// mapped counterexample.
    pub fn annotate_error(&self, mut prusti_error: PrustiError) -> PrustiError {
        for entry in &self.0 {
            prusti_error = prusti_error.add_note(format!("{entry}"), Some(entry.span));
        }
        prusti_error
    }
}

/// An expression mapped from a Silicon counterexample.
#[derive(Clone, Default)]
pub enum Entry {
    /// A string is used to be able to represent integers outside the 128-bit
    /// range.
    Int(String),
    Float(String),
    Bool(bool),
    Char(char),
    Ref(Box<Entry>),
    Box(Box<Entry>),
    Struct {
        name: String,
        field_entries: Vec<(String, Entry)>,
    },
    Enum {
        super_name: String,
        name: String,
        field_entries: Vec<(String, Entry)>,
        //note: if fields are not named, their order is important!
        //that is why no FxHashMap is used
    },
    Tuple(Vec<Entry>),
    #[default]
    Unknown,
}

impl Entry {
    pub fn is_unit(&self) -> bool {
        match self {
            Entry::Tuple(fields) => fields.is_empty(),
            _ => false,
        }
    }
    pub fn merge(&self, other: &Entry) -> Entry {
        match (self, other) {
            (Entry::Int(x), _) => Entry::Int(x.clone()),
            (Entry::Float(x), _) => Entry::Float(x.clone()),
            (Entry::Bool(x), _) => Entry::Bool(*x),
            (Entry::Char(x), _) => Entry::Char(*x),
            (Entry::Ref(entry), _) => Entry::Ref(Box::new(entry.merge(other))),
            (Entry::Box(entry), _) => Entry::Box(Box::new(entry.merge(other))),
            (
                Entry::Struct {
                    name: name1,
                    field_entries: field_entries1,
                },
                Entry::Struct {
                    name: name2,
                    field_entries: field_entries2,
                },
            ) => {
                if *name1 == *name2 && field_entries1.len() == field_entries2.len() {
                    let mut other_iter = field_entries2.iter();
                    let new_field_entries = field_entries1
                        .iter()
                        .map(|x| {
                            let next = other_iter.next().unwrap();
                            (x.0.clone(), x.1.merge(&next.1))
                        })
                        .collect();
                    return Entry::Struct {
                        name: name1.to_string(),
                        field_entries: new_field_entries,
                    };
                }
                self.clone()
            }
            (
                Entry::Enum {
                    super_name: super_name1,
                    name: name1,
                    field_entries: field_entries1,
                },
                Entry::Enum {
                    super_name: super_name2,
                    name: name2,
                    field_entries: field_entries2,
                },
            ) => {
                if *super_name1 == *super_name2 {
                    if *name1 == *"?" {
                        return other.clone();
                    }

                    if *name1 == *name2 && field_entries1.len() == field_entries2.len() {
                        let mut other_iter = field_entries2.iter();
                        let new_field_entries = field_entries1
                            .iter()
                            .map(|x| {
                                let next = other_iter.next().unwrap();
                                (x.0.clone(), x.1.merge(&next.1))
                            })
                            .collect();
                        return Entry::Enum {
                            super_name: super_name1.to_string(),
                            name: name1.to_string(),
                            field_entries: new_field_entries,
                        };
                    }
                }
                self.clone()
            }
            (Entry::Tuple(entries1), Entry::Tuple(entries2)) => {
                if entries1.len() == entries2.len() {
                    let mut other_iter = entries2.iter();
                    let new_entries = entries1
                        .iter()
                        .map(|x| {
                            let next = other_iter.next().unwrap();
                            x.merge(next)
                        })
                        .collect();
                    return Entry::Tuple(new_entries);
                }
                self.clone()
            }
            _ => self.clone(),
        }
    }
}

impl fmt::Debug for Entry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Entry::Int(value) => write!(f, "{value}"),
            Entry::Float(value) => write!(f, "{value}"),
            Entry::Bool(value) => write!(f, "{value}"),
            Entry::Char(value) => {
                if value.is_control() {
                    // avoid displaying line breaks etc directly
                    write!(f, "0x{:x}", *value as i32)
                } else {
                    write!(f, "'{}' (0x{:x})", value, *value as i32)
                }
            }
            Entry::Ref(el) => write!(f, "ref({el:#?})"),
            Entry::Box(el) => write!(f, "box({el:#?})"),
            Entry::Enum {
                super_name,
                name,
                field_entries,
            } => {
                let named_fields =
                    !field_entries.is_empty() && field_entries[0].0.parse::<usize>().is_err();
                let enum_name = format!("{super_name}::{name}");
                if named_fields {
                    let mut f1 = f.debug_struct(&enum_name);
                    for (fieldname, entry) in field_entries {
                        f1.field(fieldname, entry);
                    }
                    f1.finish()
                } else {
                    let mut f1 = f.debug_tuple(&enum_name);
                    for (_, entry) in field_entries {
                        f1.field(entry);
                    }
                    f1.finish()
                }
            }
            Entry::Struct {
                name,
                field_entries,
            } => {
                let mut f1 = f.debug_struct(name);
                for (fieldname, entry) in field_entries {
                    f1.field(fieldname, entry);
                }
                f1.finish()
            }
            Entry::Tuple(fields) => {
                if fields.is_empty() {
                    write!(f, "()")
                } else {
                    let mut f1 = f.debug_tuple("");
                    for entry in fields {
                        f1.field(entry);
                    }
                    f1.finish()
                }
            }
            Entry::Unknown => write!(f, "?"),
        }
    }
}
