use std::fmt;
use rustc_span::Span;
use prusti_interface::PrustiError;

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
    pub fn with_one_value(
        span: Span,
        name: Option<String>,
        final_value: Entry,
    ) -> Self {
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
        final_value: Entry
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
    format!("{:#?}", val)
        .split('\n')
        .collect::<Vec<&str>>()
        .join("\n  ")
}

impl fmt::Display for CounterexampleEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "counterexample for ")?;
        if let Some(name) = &self.name {
            write!(f, "\"{}\"", name)?;
        } else {
            write!(f, "result")?;
        }
        if let Some(initial_value) = &self.initial_value {
            write!(f, "\n  initial value: {}", indented_debug(&initial_value))?;
        }
        write!(f, "\n  final value:   {}", indented_debug(&self.final_value))
    }
}

/// A concrete counterexample containing mapped values of arguments and locals
/// (the latter only for impure functions), as well as the result (if any).
pub struct Counterexample(Vec<CounterexampleEntry>);

impl Counterexample {
    pub fn new(
        entries: Vec<CounterexampleEntry>,
    ) -> Self {
        Self(entries)
    }

    /// Annotates a Prusti error with notes for any variable present in the
    /// mapped counterexample.
    pub fn annotate_error(&self, mut prusti_error: PrustiError) -> PrustiError {
        for entry in &self.0 {
            prusti_error = prusti_error.add_note(
                &format!("{}", entry),
                Some(entry.span),
            );
        }
        prusti_error
    }
}

/// An expression mapped from a Silicon counterexample.
#[derive(Clone)]
pub enum Entry {
    /// A string is used to be able to represent integers outside the 128-bit
    /// range.
    Int(String),
    Bool(bool),
    Char(char),
    Ref(Box<Entry>),
    Struct {
        name: String,
        field_entries: Vec<(String, Entry)>,
    },
    Enum {
        super_name: String,
        name: String,
        field_entries: Vec<(String, Entry)>,
        //note: if fields are not named, their order is important!
        //that is why no HashMap is used
    },
    Tuple(Vec<Entry>),
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

impl Default for Entry {
    fn default() -> Self {
        Entry::Unknown
    }
}

impl fmt::Debug for Entry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Entry::Int(value) => write!(f, "{}", value),
            Entry::Bool(value) => write!(f, "{}", value),
            Entry::Char(value) => {
                if value.is_control() {
                    // avoid displaying line breaks etc directly
                    write!(f, "0x{:x}", *value as i32)
                } else {
                    write!(f, "'{}' (0x{:x})", value, *value as i32)
                }
            }
            Entry::Ref(el) => write!(f, "ref({:#?})", el),
            Entry::Enum { super_name, name, field_entries } => {
                let named_fields = !field_entries.is_empty() && field_entries[0].0.parse::<usize>().is_err();
                let enum_name = format!("{}::{}", super_name, name);
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
            Entry::Struct { name, field_entries } => {
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
