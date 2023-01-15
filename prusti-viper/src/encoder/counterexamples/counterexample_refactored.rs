use prusti_interface::PrustiError;
use prusti_rustc_interface::errors::MultiSpan;
use std::fmt;

/// Counterexample information for a single variable.
#[derive(Debug)]
pub struct CounterexampleEntry {
    /// Name of local variable or None for the result.
    name: Option<String>,
    /// history of all Variables with Span
    history: Vec<(Entry, MultiSpan)>,
}

impl CounterexampleEntry {
    pub fn new(name: Option<String>, history: Vec<(Entry, MultiSpan)>) -> Self {
        CounterexampleEntry { name, history }
    }
    fn history_to_string(&self) -> Vec<String> {
        let mut messages = Vec::new();
        for (value, _) in &self.history {
            messages.push(format!(
                "counterexample for \"{}\"\n value:   {}",
                self.name.as_ref().unwrap_or(&"result".to_string()),
                indented_debug(value)
            ));
        }
        messages
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
        for message in self.history_to_string() {
            write!(f, "{message}")?;
        }
        Ok(())
    }
}

/// A concrete counterexample containing mapped values of arguments and locals
pub struct Counterexample(Vec<CounterexampleEntry>);

impl Counterexample {
    pub fn new(entries: Vec<CounterexampleEntry>) -> Self {
        Self(entries)
    }

    /// Annotates a Prusti error with notes for any variable present in the
    /// mapped counterexample.
    pub fn annotate_error(&self, mut prusti_error: PrustiError) -> PrustiError {
        for counterexample_entry in &self.0 {
            let messages = counterexample_entry.history_to_string();
            let mut iter = messages.iter();
            for (_, span) in &counterexample_entry.history {
                prusti_error.add_note_mut(iter.next().unwrap(), Some(span.clone()));
            }
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
        //this vec stores how a sruct should be formated to the user
        custom_print_option: Option<Vec<String>>,
    },
    Enum {
        super_name: String,
        name: String,
        //note: if fields are not named, their order is important!
        //that is why no FxHashMap is used
        field_entries: Vec<(String, Entry)>,
        //this vec stores how a enum should be formated to the user
        custom_print_option: Option<Vec<String>>,
    },
    Union {
        name: String,
        field_entry: (String, Box<Entry>),
    },
    Array(Vec<Entry>),
    Tuple(Vec<Entry>),
    Seq(Vec<Entry>),
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
                custom_print_option,
            } => {
                if let Some(custom_print) = custom_print_option {
                    let mut custom_print_iter = custom_print.iter();
                    let text = custom_print_iter.next().unwrap(); //safe because custom_print has at least one element
                    let mut text_iter = text.split("{}");
                    let mut output = text_iter.next().unwrap().to_string(); //safe because text_iter has at least one element
                    for next in text_iter {
                        let fieldname = custom_print_iter.next().unwrap(); //safe because of encoding (checked by compiler)
                        let field_entry = &field_entries
                            .iter()
                            .find(|(name, _)| fieldname == name)
                            .unwrap()
                            .1; //safe because of encoding (checked by compiler)
                        output.push_str(&format!("{field_entry:#?}"));
                        output.push_str(next);
                    }
                    write!(f, "{output}")
                } else {
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
            }
            Entry::Struct {
                name,
                field_entries,
                custom_print_option,
            } => {
                if let Some(custom_print) = custom_print_option {
                    let mut custom_print_iter = custom_print.iter();
                    let text = custom_print_iter.next().unwrap(); //safe because custom_print has at least one element
                    let mut text_iter = text.split("{}");
                    let mut output = text_iter.next().unwrap().to_string(); //safe because text_iter has at least one element
                    for next in text_iter {
                        let fieldname = custom_print_iter.next().unwrap(); //safe because of encoding (checked by compiler)
                        let field_entry = &field_entries
                            .iter()
                            .find(|(name, _)| fieldname == name)
                            .unwrap()
                            .1; //safe because of encoding (checked by compiler)
                        output.push_str(&format!("{field_entry:#?}"));
                        output.push_str(next);
                    }
                    write!(f, "{output}")
                } else {
                    let mut f1 = f.debug_struct(name);
                    for (fieldname, entry) in field_entries {
                        f1.field(fieldname, entry);
                    }
                    f1.finish()
                }
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
            Entry::Seq(elements) => {
                if elements.is_empty() {
                    write!(f, "Seq()")
                } else {
                    let mut output = "".to_string();
                    for elem in elements {
                        output.push_str(&format!("{elem:#?}, "));
                    }
                    write!(f, "Seq({output})")
                }
            }
            Entry::Union { name, field_entry } => {
                //write!(f, "Union {{ {}: {:#?}}}", field_entry.0, field_entry.1)
                let mut f1 = f.debug_struct(name);
                f1.field(&field_entry.0, &*(field_entry.1));
                f1.finish()
            }
            Entry::Array(elements) => {
                if elements.is_empty() {
                    write!(f, "[]")
                } else {
                    let mut output = "".to_string();
                    for elem in elements {
                        output.push_str(&format!("{elem:#?}, "));
                    }
                    write!(f, "[{output}]")
                }
            }
            Entry::Unknown => write!(f, "?"),
        }
    }
}
