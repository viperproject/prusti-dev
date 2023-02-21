use rustc_hash::FxHashMap;
use serde;

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct SiliconCounterexample {
    //pub heap: Heap,
    //pub old_heaps: FxHashMap<String, Heap>,
    pub model: Model,
    pub functions: Functions,
    pub domains: Domains,
    pub old_models: FxHashMap<String, Model>,
    // label_order because HashMaps do not guarantee order of elements
    // whereas the Map used in scala does guarantee it
    pub label_order: Vec<String>,
}

// Model Definitions
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Model {
    pub entries: FxHashMap<String, ModelEntry>,
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum ModelEntry {
    LitInt(String),
    LitFloat(String),
    LitBool(bool),
    LitPerm(String),
    Ref(String, FxHashMap<String, ModelEntry>),
    NullRef(String),
    RecursiveRef(String),
    Var(String),
    Seq(String, Vec<ModelEntry>),
    Other(String, String),
    DomainValue(String, String),
    UnprocessedModel, //used for Silicon's Snap type
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Functions {
    pub entries: FxHashMap<String, FunctionEntry>,
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct FunctionEntry {
    pub options: Vec<(Vec<Option<ModelEntry>>, Option<ModelEntry>)>,
    pub default: Option<ModelEntry>,
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct Domains {
    pub entries: FxHashMap<String, DomainEntry>,
}

#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct DomainEntry {
    pub functions: Functions,
}

impl FunctionEntry {
    /// Given a vec of params it finds the correct entry in a function.
    pub fn get_function_value(&self, params: &Vec<Option<ModelEntry>>) -> &Option<ModelEntry> {
        for option in &self.options {
            if &option.0 == params {
                return &option.1;
            }
        }
        &None
    }
}
