use std::collections::HashMap;

use jni::{objects::JObject, JNIEnv};
use jni_utils::JniUtils;
use viper_sys::wrappers::{scala, viper::silicon};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SiliconCounterexample {
    //pub heap: Heap,
    //pub old_heaps: HashMap<String, Heap>,
    pub model: Model,
    pub old_models: HashMap<String, Model>,
    // label_order because HashMaps do not guarantee order of elements
    // whereas the Map used in scala does guarantee it
    pub label_order: Vec<String>,
}

impl SiliconCounterexample {
    pub fn new<'a>(
        env: &'a JNIEnv<'a>,
        jni: JniUtils<'a>,
        counterexample: JObject<'a>,
    ) -> SiliconCounterexample {
        unwrap_counterexample(env, jni, counterexample)
    }
}

// Heap Definitions
/*
this stuff might be useful at a later stage, when we can actually
trigger unfolding of certain predicates, but for now there is
nothing to be used stored in the heap
*/
/*
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Heap {
    pub entries: Vec<HeapEntry>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum HeapEntry {
    FieldEntry {
        recv: ModelEntry,
        //perm & sort omitted
        field: String,
        entry: ModelEntry,
    },
    PredicateEntry {
        name: String,
        args: Vec<ModelEntry>,
    },
}
*/

// Model Definitions
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Model {
    pub entries: HashMap<String, ModelEntry>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ModelEntry {
    LitInt(String),
    LitFloat(String),
    LitBool(bool),
    LitPerm(f64),
    Ref(String, HashMap<String, ModelEntry>),
    NullRef(String),
    RecursiveRef(String),
    Var(String),
    Seq(String, Vec<ModelEntry>), // not necessarily supported
    Other(String, String),
    UnprocessedModel, // do not use these at all
}

// methods unwrapping scala converter to newly defined structures

fn unwrap_counterexample<'a>(
    env: &'a JNIEnv<'a>,
    jni: JniUtils<'a>,
    counterexample: JObject<'a>,
) -> SiliconCounterexample {
    let converter_wrapper = silicon::reporting::Converter::with(env);
    let ce_wrapper = silicon::interfaces::SiliconMappedCounterexample::with(env);
    let converter_original = jni.unwrap_result(ce_wrapper.call_converter(counterexample));

    /*
    let heap_scala = jni.
        unwrap_result(
            converter_wrapper
                .call_extractedHeap(converter_original)
            );
    let heap = unwrap_heap(env, jni, heap_scala);


    let old_heaps_scala = jni
        .unwrap_result(
            converter_wrapper
            .call_extractedHeaps(converter_original)
        );
    let old_heaps_map = jni.stringmap_to_hashmap(old_heaps_scala);
    let mut old_heaps = HashMap::new();
    for (label, h) in old_heaps_map {
        let old_heap = unwrap_heap(env, jni, h);
        old_heaps.insert(label, old_heap);
    }
    */

    let model_scala = jni.unwrap_result(converter_wrapper.call_extractedModel(converter_original));
    let model = unwrap_model(env, jni, model_scala);

    let old_models_scala =
        jni.unwrap_result(converter_wrapper.call_modelAtLabel(converter_original));
    let old_models = jni
        .stringmap_to_hashmap(old_models_scala)
        .into_iter()
        .map(|(label, m)| (label, unwrap_model(env, jni, m)))
        .collect::<HashMap<_, _>>();

    SiliconCounterexample {
        //heap,
        //old_heaps,
        model,
        old_models,
        label_order: jni.stringmap_to_keyvec(old_models_scala),
    }
}

/*
fn unwrap_heap<'a>(env: &'a JNIEnv<'a>, jni: JniUtils<'a>, heap: JObject<'a>) -> Heap {
    let heap_wrapper = silicon::reporting::ExtractedHeap::with(env);
    let entries_scala = jni
        .unwrap_result(
            heap_wrapper.call_entries(heap)
        ); // List[HeapEntries] in scala
    let entries_vec = jni.list_to_vec(entries_scala);
    let mut entries = vec![];
    for i in 0..(entries_vec.len()) {
        let entry = unwrap_heap_entry(env, jni, entries_vec[i]);
        match entry{
            Some(e) => entries.push(e),
            None => ()
        };
    }
    Heap{
        entries
    }
}

fn unwrap_heap_entry<'a>(
    env: &'a JNIEnv<'a>,
    jni: JniUtils<'a>,
    entry: JObject<'a>
) -> Option<HeapEntry> {
    //we can ignore FieldEntries since the ones that are interesting should already be in model
    //let field_entry_wrapper = silicon::reporting::FieldHeapEntry::with(env);
    let predicate_entry_wrapper = silicon::reporting::PredHeapEntry::with(env);

    if jni.is_instance_of(entry, "viper/silicon/reporting/PredHeapEntry"){
        //get fields:
        let name_scala = jni.unwrap_result(predicate_entry_wrapper.call_name(entry));
        let name = jni.to_string(name_scala);

        let args_scala = jni
            .unwrap_result(
                predicate_entry_wrapper
                .call_args(entry)
            );
        let args_vec = jni.seq_to_vec(args_scala);
        let mut args = vec![];
        for el in args_vec{
            let me = unwrap_model_entry(env, jni, el);
            match me{
                Some(e) => args.push(e),
                None => ()
            }
        }

        let res = HeapEntry::PredicateEntry{
            name,
            args
        };
        Some(res)
    } else {
        //extend for FieldEntries if needed
        None
    }
}
*/

fn unwrap_model<'a>(env: &'a JNIEnv<'a>, jni: JniUtils<'a>, model: JObject<'a>) -> Model {
    let model_wrapper = silicon::reporting::ExtractedModel::with(env);
    let entries_scala = jni.unwrap_result(model_wrapper.call_entries(model));
    let map_string_scala = jni.stringmap_to_hashmap(entries_scala);
    let mut entries = HashMap::new();
    for (name, entry_scala) in map_string_scala {
        let entry = unwrap_model_entry(env, jni, entry_scala, &mut entries);
        if let Some(e) = entry {
            entries.insert(name, e);
        }
    }
    Model { entries }
}

fn unwrap_model_entry<'a>(
    env: &'a JNIEnv<'a>,
    jni: JniUtils<'a>,
    entry: JObject<'a>,
    entries: &mut HashMap<String, ModelEntry>,
) -> Option<ModelEntry> {
    match jni.class_name(entry).as_str() {
        "viper.silicon.reporting.LitIntEntry" => {
            let lit_int_wrapper = silicon::reporting::LitIntEntry::with(env);
            let value_scala = jni.unwrap_result(lit_int_wrapper.call_value(entry));
            let value = jni.to_string(value_scala);
            Some(ModelEntry::LitInt(value))
        }
        "viper.silicon.reporting.LitBoolEntry" => {
            let lit_bool_wrapper = silicon::reporting::LitBoolEntry::with(env);
            let value = jni.unwrap_result(lit_bool_wrapper.call_value(entry));
            Some(ModelEntry::LitBool(value))
        }
        "viper.silicon.reporting.LitPermEntry" => {
            let lit_perm_wrapper = silicon::reporting::LitPermEntry::with(env);
            let value = jni.unwrap_result(lit_perm_wrapper.call_value(entry));
            Some(ModelEntry::LitPerm(value))
        }
        "viper.silicon.reporting.RefEntry" => {
            let ref_wrapper = silicon::reporting::RefEntry::with(env);
            let product_wrapper = scala::Product::with(env);
            // get name
            let name_scala = jni.unwrap_result(ref_wrapper.call_name(entry));
            let fields_scala = jni.unwrap_result(ref_wrapper.call_fields(entry));
            let name = jni.to_string(name_scala);
            // get list of fields
            let result = jni
                .stringmap_to_hashmap(fields_scala)
                .into_iter()
                .filter_map(|(field, tuple_scala)| {
                    let element_scala =
                        jni.unwrap_result(product_wrapper.call_productElement(tuple_scala, 0));
                    Some((field, unwrap_model_entry(env, jni, element_scala, entries)?))
                })
                .collect::<HashMap<_, _>>();
            entries.insert(name.clone(), ModelEntry::Ref(name.clone(), result.clone()));
            Some(ModelEntry::Ref(name, result))
        }
        "viper.silicon.reporting.NullRefEntry" => {
            let null_ref_wrapper = silicon::reporting::NullRefEntry::with(env);
            let name = jni.to_string(jni.unwrap_result(null_ref_wrapper.call_name(entry)));
            Some(ModelEntry::NullRef(name))
        }
        "viper.silicon.reporting.RecursiveRefEntry" => {
            let rec_ref_wrapper = silicon::reporting::RecursiveRefEntry::with(env);
            let name = jni.to_string(jni.unwrap_result(rec_ref_wrapper.call_name(entry)));
            Some(ModelEntry::RecursiveRef(name))
        }
        "viper.silicon.reporting.VarEntry" => {
            let var_wrapper = silicon::reporting::VarEntry::with(env);
            let name = jni.to_string(jni.unwrap_result(var_wrapper.call_name(entry)));
            Some(ModelEntry::Var(name))
        }
        "viper.silicon.reporting.OtherEntry" => {
            let other_wrapper = silicon::reporting::OtherEntry::with(env);
            let value = jni.to_string(jni.unwrap_result(other_wrapper.call_value(entry)));
            let problem = jni.to_string(jni.unwrap_result(other_wrapper.call_problem(entry)));
            Some(ModelEntry::Other(value, problem))
        }
        "viper.silicon.reporting.SeqEntry" => {
            let seq_wrapper = silicon::reporting::SeqEntry::with(env);
            let name = jni.to_string(jni.unwrap_result(seq_wrapper.call_name(entry)));
            let list_scala = jni.unwrap_result(seq_wrapper.call_values(entry));
            let res = jni
                .list_to_vec(list_scala)
                .into_iter()
                .filter_map(|el| unwrap_model_entry(env, jni, el, entries))
                .collect();
            Some(ModelEntry::Seq(name, res))
        }
        _ => None,
    }
}
