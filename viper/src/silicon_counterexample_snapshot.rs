//use std::default;

use rustc_hash::FxHashMap;

use jni::{objects::JObject, JNIEnv};
use jni_utils::JniUtils;
use viper_sys::wrappers::{scala, viper::silicon};


#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SiliconCounterexample {

    pub model: Model,
    pub functions: Functions,
    pub domains: Domains,
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

// Model Definitions
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Model {
    pub entries: FxHashMap<String, ModelEntry>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ModelEntry {
    LitInt(String),
    LitFloat(String),
    LitBool(bool),
    LitPerm(String),
    Ref(String, FxHashMap<String, ModelEntry>),
    NullRef(String),
    RecursiveRef(String),
    Var(String),
    Seq(String, Vec<ModelEntry>), // not necessarily supported
    Other(String, String),
    DomainValue(String, String), //(domain name, var name)
    UnprocessedModel, // do not use these at all
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Functions{
    pub entries: FxHashMap<String, FunctionEntry>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FunctionEntry{
    pub options: Vec<(Vec<Option<ModelEntry>>,Option<ModelEntry>)>,
    pub default: Option<ModelEntry>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Domains{
    pub entries: FxHashMap<String, DomainEntry>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct DomainEntry{
    pub functions: Functions,
}

impl FunctionEntry{
    pub fn get_function_value(&self, params: &Vec<Option<ModelEntry>>) -> &Option<ModelEntry>{
        for option in &self.options{
            debug!("posssible option: {:?}", &option.0);
            debug!("params: {:?}", params);
            if &option.0 == params{
                debug!("option found");
                return &option.1
            }
        } 
        &None
    }
    pub fn get_function_value_with_default(&self, params: &Vec<Option<ModelEntry>>) -> &Option<ModelEntry>{
        for option in &self.options{
            debug!("posssible option: {:?}", &option.0);
            debug!("params: {:?}", params);
            if &option.0 == params{
                debug!("option found");
                return &option.1
            }
        } 
        &self.default
    }
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
    
    //get model
    let model_scala = jni.unwrap_result(converter_wrapper.call_extractedModel(converter_original));
    let model = unwrap_model(env, jni, model_scala);

    //get labels: Option 2
    //need a simpler method from silicon to get all the labels
    //let model_scala = jni.unwrap_result(converter_wrapper.call_extractedModel(converter_original));
    //let labels = jni.stringmap_to_keyvec(model_scala); 

    //get domain independent functions
    let functions_scala = jni.unwrap_result(converter_wrapper.call_non__domain__functions(converter_original));
    debug!("Print functions: {:?}", jni.to_string(functions_scala));
    let functions = unwrap_functions(env, jni, functions_scala);
    debug!("Print translated functions: {:?}", functions);

    //get domains
    let domains_scala = jni.unwrap_result(converter_wrapper.call_domains(converter_original));
    debug!("Print domains: {:?}", jni.to_string(domains_scala));
    let domains = unwrap_domains(env, jni, domains_scala);
    debug!("Print translated domains: {:?}", domains);

    SiliconCounterexample {
        model,
        functions,
        domains,
    }
}

fn unwrap_model<'a>(env: &'a JNIEnv<'a>, jni: JniUtils<'a>, model: JObject<'a>) -> Model {
    let model_wrapper = silicon::reporting::ExtractedModel::with(env);
    let entries_scala = jni.unwrap_result(model_wrapper.call_entries(model));
    let map_string_scala = jni.stringmap_to_hashmap(entries_scala);
    let mut entries = FxHashMap::default();
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
    entries: &mut FxHashMap<String, ModelEntry>,
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
            let value = jni.to_string(jni.unwrap_result(lit_perm_wrapper.call_value(entry))); //not very elegant
            debug!("LitPermEntry: {:?}", value);
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
                .collect::<FxHashMap<_, _>>();
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
        "viper.silicon.reporting.DomainValueEntry" => {
            let domain_wrapper = silicon::reporting::DomainValueEntry::with(env);
            let domain = jni.to_string(jni.unwrap_result(domain_wrapper.call_domain(entry)));
            let id = jni.to_string(jni.unwrap_result(domain_wrapper.call_id(entry)));
            Some(ModelEntry::DomainValue(domain, id))
        }
        _ => None,
    }
}

fn unwrap_functions<'a>(env: &'a JNIEnv<'a>, jni: JniUtils<'a>, functions: JObject<'a>) -> Functions {
    let functions_wrapper = silicon::reporting::ExtractedFunction::with(env);
    let entries_scala = jni.seq_to_vec(functions);
    let mut entries = FxHashMap::default();
    for entry_scala in entries_scala{
        let fname = jni.to_string(jni.unwrap_result(functions_wrapper.call_fname(entry_scala)));
        let entry = unwrap_function_entry(env, jni, entry_scala, &functions_wrapper);
        entries.insert(fname,entry);
    }
    Functions{entries}
}


fn unwrap_function_entry<'a>(
    env: &'a JNIEnv<'a>,
    jni: JniUtils<'a>,
    entry: JObject<'a>,
    functions_wrapper: &silicon::reporting::ExtractedFunction
) -> FunctionEntry {
    let default_scala = jni.unwrap_result(functions_wrapper.call_default(entry));
    let mut tmp = FxHashMap::default(); //We don't care about recusivley unwrapped ModelEntries
                                                                        //Since default is always a ConstantEntry, tmp will remain empty
    let default = unwrap_model_entry(env, jni, default_scala, &mut tmp);

    let iter_wrapper = scala::collection::Iterable::with(env);
    let options_scala = jni.unwrap_result(functions_wrapper.call_options(entry));
    let options_scala_seq = jni.unwrap_result(iter_wrapper.call_toSeq(options_scala));
    let options = jni.seq_to_vec(options_scala_seq)
            .into_iter()
            .map( | entry | {
                unwrap_option_entry(env, jni, entry)
            }
        ).collect::<Vec<_>>();
    FunctionEntry { options, default }
}
fn unwrap_option_entry<'a>(
    env: &'a JNIEnv<'a>,
    jni: JniUtils<'a>,
    entry: JObject<'a>,
) -> (Vec<Option<ModelEntry>>, Option<ModelEntry>) {
    let product_wrapper = scala::Product::with(env);
    let args_scala = jni.unwrap_result(product_wrapper.call_productElement(entry, 0));
    let result_scala = jni.unwrap_result(product_wrapper.call_productElement(entry, 1));
    let args = jni.list_to_vec(args_scala).into_iter()
    .filter_map(| arg | { //filter out any snap arg 
        let mut tmp = FxHashMap::default();
        match unwrap_model_entry(env, jni, arg, &mut tmp){ 
            Some(arg) => Some(Some(arg)),
            None => None
        }
    }).collect::<Vec<_>>();
    let mut tmp = FxHashMap::default(); //We don't care about recusivley unwrapped ModelEntries
                                                                        //Since default is always a ConstantEntry, tmp will remain empty
    let result = unwrap_model_entry(env, jni, result_scala, &mut tmp);
    (args, result)
}

fn unwrap_domains<'a>(env: &'a JNIEnv<'a>, jni: JniUtils<'a>, domains: JObject<'a>) -> Domains {
    let domains_wrapper = silicon::reporting::DomainEntry::with(env);
    let entries_scala = jni.seq_to_vec(domains);
    let mut entries = FxHashMap::default();
    for entry_scala in entries_scala{
        let dname = jni.to_string(jni.unwrap_result(domains_wrapper.call_name(entry_scala)));
        let functions_scala = jni.unwrap_result(domains_wrapper.call_functions(entry_scala));
        let entry = unwrap_functions(env, jni, functions_scala);
        entries.insert(dname,DomainEntry{functions: entry});
    }
    Domains{entries}
}