use rustc_hash::{FxHashMap};
use rustc_span::source_map::Spanned;
use super::{VarMappingInterface, VarMapping};
//use super::DiscriminantsStateInterface;
use crate::encoder::errors::PositionManager;
use crate::encoder::mir::specifications::SpecificationsInterface;


use log::{debug};

//use viper::silicon_counterexample_snapshot::*;
use viper::silicon_counterexample::*;

use prusti_interface::data::ProcedureDefId;
use crate::encoder::Encoder;
use crate::encoder::places::{Local, LocalVariableManager};
use super::counterexample_snapshot2::*;

use rustc_middle::mir::{self, VarDebugInfo};
use rustc_errors::MultiSpan;
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::iter;
use rustc_span::symbol::Ident;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::ExprKind;
use rustc_hir::StmtKind;
use rustc_hir::Lit;
use rustc_hir::Expr;
use rustc_hir::Block;
use rustc_ast::LitKind;
use rustc_hir::QPath;
use rustc_hir::Path;



pub fn backtranslate(
    encoder: &Encoder,
    position_manager: &PositionManager,
    def_id: ProcedureDefId,
    silicon_counterexample: &SiliconCounterexample,
) ->  Counterexample {
    let mut translator = CounterexampleTranslator::new(encoder, def_id, silicon_counterexample);

    translator.create_mapping(def_id, &encoder); //creates the mapping between mir var and the corresponding snapshot var
    let label_markers = translator.get_label_markers();
    debug!("label_markers: {:?}", &label_markers);

    let counterexample_entry_vec = translator.process_entries(position_manager, &label_markers);

    debug!("found counterexample entry: {:?}", counterexample_entry_vec);
    //TODO sort counterexample entries by span for testing

    Counterexample::new(counterexample_entry_vec)
}

//Cache for domains //TODO remove struct and use just a map
#[derive(Default)]
struct TranslatedDomains{
    cached_domains: FxHashMap<(String, String), Entry>,
}

pub struct CounterexampleTranslator<'ce, 'tcx, 'v> {
    //mir: mir::Body<'tcx>, //not used
    //def_id: ProcedureDefId,
    //lowerer: Lowerer, //for name encodings
    encoder: &'ce Encoder<'v, 'tcx>,
    silicon_counterexample: &'ce SiliconCounterexample,
    tcx: TyCtxt<'tcx>, 
    //is_pure: bool,  //not used
    //pub(super) disc_info: FxHashMap<(ProcedureDefId, String), Vec<String>>, //not used anymore
    var_debug_info: Vec<VarDebugInfo<'tcx>>,
    local_variable_manager: LocalVariableManager<'tcx>, 
    pub(super) var_mapping: VarMapping, 
    
}

impl<'ce, 'tcx, 'v> CounterexampleTranslator<'ce, 'tcx, 'v> {
    pub fn new(
        encoder: &'ce Encoder<'v, 'tcx>,
        def_id: ProcedureDefId,
        silicon_counterexample: &'ce SiliconCounterexample,
    ) -> Self {
        let mir = encoder.env().get_procedure(def_id).get_mir().clone();
        let var_debug_info = mir.var_debug_info.clone();
        let local_variable_manager = LocalVariableManager::new(&mir.local_decls);
        Self {
            //mir,
            //def_id,
            //lowerer: Lowerer::new(encoder),
            encoder: encoder,
            silicon_counterexample,
            tcx: encoder.env().tcx(),
            //is_pure: false, // No verified functions are pure. encoder.is_pure(def_id),
                            // TODO: This assumption should allow simplifying the translator quite a bit.
            //disc_info: encoder.discriminants_info(),
            var_debug_info,
            local_variable_manager,
            var_mapping: Default::default(),
        }
    }

    fn get_label_markers(&self) -> FxHashMap<String, bool>{
        debug!("silicon_counterexample_model: {:?}",&self.silicon_counterexample.model.entries);
        self.var_mapping.labels_successor_mapping.iter().map(
            | (label, _) | {
                match self.silicon_counterexample.model.entries.get(&format!("{}$marker",label)){
                    Some(ModelEntry::LitBool(b)) => (label.clone(), b.clone()),
                    _ => (label.clone(), false) //label marker not found is equivalent with label not visited (should not be impossible) 
                }
            }
        ).collect::<FxHashMap<String, bool>>()
    }

    fn get_trace_of_var(&self, position_manager: &PositionManager, var: &String, label_markers: &FxHashMap<String, bool>) -> Vec<(String, MultiSpan)>{//Option<MultiSpan>)>{
        let mut label = &format!("start_label");
        let mut snapshot_var_vec = Vec::new();
        if let Some(label_snapshot_mapping) = self.var_mapping.var_snaphot_mapping.get(var){
            loop {
                debug!("label: {:?} and mapping: {:?}", label, label_snapshot_mapping);
                if let Some(snapshot_vars) = label_snapshot_mapping.get(label){ //misssing .name, Span);
                    debug!("value of snapshot_vars {:?}: ", snapshot_vars);
                    snapshot_var_vec.extend(snapshot_vars.iter().map(|x| (x.name.clone(), self.get_span(position_manager, &x.position))));
                }
                if let Some(next) = self.get_successor(label, label_markers){
                    debug!("value of next {:?}: ", next);
                    label = next;
                } else {
                    break;
                }
            }
        }
        debug!("trace of var {:?}: {:?}", var, snapshot_var_vec);
        snapshot_var_vec
    }

    fn process_entries(&self, position_manager: &PositionManager, label_markers: &FxHashMap<String, bool>) -> Vec< CounterexampleEntry> {
        let mut translated_domains = TranslatedDomains::default();
        let mut entries = vec![];

        for vdi in &self.var_debug_info{ //variables and params
            let rust_name = vdi.name.to_ident_string();
            let local: mir::Local = if let mir::VarDebugInfoContents::Place(place) = vdi.value {
                if let Some(local) = place.as_local() {
                    local
                } else {
                    continue;
                }
            } else {
                continue;
            };
           // let index = local.index();
            let var_local = Local::from(local);
            let typ = self.local_variable_manager.get_type(var_local);
            let vir_name = self.local_variable_manager.get_name(var_local);
            debug!("rust name: {:?}", &rust_name);
            debug!("rust typ: {:?}", &typ.kind());
            debug!("vir name: {:?}", &vir_name);
            let trace = self.get_trace_of_var(&position_manager, &vir_name, &label_markers);
            debug!("trace: {:?}", &trace);
            let history = self.process_entry(&trace, typ, &mut translated_domains);
            
            entries.push( CounterexampleEntry::new(Some(rust_name), history))
        } 
        //result
        let vir_name = format!("_0");
        let return_local = Local::from(mir::Local::from_usize(0));
        let typ = self.local_variable_manager.get_type(return_local);
        debug!("rust typ: {:?}", &typ.kind());
        debug!("vir name: {:?}", &vir_name);
        let trace = self.get_trace_of_var(&position_manager, &vir_name, &label_markers);
        debug!("trace: {:?}", &trace);
        let history = self.process_entry(&trace, typ, &mut translated_domains);
        entries.push( CounterexampleEntry::new(None, history));
        entries
    }

    fn process_entry(&self, trace: &Vec<(String, MultiSpan)>, ty: Ty<'tcx>, translated_domains: &mut TranslatedDomains) -> Vec<(Entry,MultiSpan)> {
        let mut entries = vec![];
        for (snapshot_var, span) in trace{ //FIXME is domain_name really needed?
            debug!("start translation for {:?}", snapshot_var);
            let model_entry = self.silicon_counterexample.model.entries.get(snapshot_var);
            let entry = self.translate_snapshot_entry(model_entry, Some(ty), translated_domains, false);
            entries.push((entry, span.clone()));
        }        
        entries
    }

    fn custom_print(&self, prusti_counterexample_print: Vec<(Option<String>, LocalDefId)>, variant_option: Option<String>) -> Option<Vec<String>>{
        debug!("variant: {:?}", variant_option);
        let def_id_option = match variant_option{
            Some(_) => prusti_counterexample_print.iter().find(|x| x.0 == variant_option),
            None => prusti_counterexample_print.first(),
        };
        
        if let Some(def_id) = def_id_option{
            let hir_id = self.tcx.hir().local_def_id_to_hir_id(def_id.1);
            debug!("Counterexample print found: {:?}", hir_id);
            let expr = &self.tcx.hir().body(self.tcx.hir().body_owned_by(hir_id)).value;
            debug!("print expr: {:?}", expr);
            if let ExprKind::Block(Block{ expr: Some(Expr{kind: ExprKind::If(_, expr, _), ..}), ..}, _) = expr.kind{
                if let ExprKind::Block(block, _) = expr.kind{
                debug!("print if expr: {:?}", expr);
                    let stmts = block.stmts;
                    debug!("print stmts: {:?}", stmts);
                    let args = stmts.iter().filter_map(|stmt | {
                        debug!("print stmt: {:?}", stmt);
                        match stmt.kind{
                            StmtKind::Semi(Expr{kind: ExprKind::Lit(Spanned {node: LitKind::Str(symbol, _), ..} ), ..}) => Some(symbol.to_ident_string()), //first arg
                            StmtKind::Semi(Expr{kind: ExprKind::Lit(Spanned {node: LitKind::Int(int, _), ..} ), ..}) => Some(int.to_string()), //unnamed fields
                            StmtKind::Semi(Expr{kind: ExprKind::Path(QPath::Resolved(_, Path{segments, ..})), ..}) => { //named fields
                                if let Some(path_segment) = segments.first() {
                                    Some(path_segment.ident.name.to_ident_string())
                                } else {
                                    None
                                }
                            },

                            _ => None
                        }
                    }).collect::<Vec<String>>();
                    debug!("print translated args: {:?}", args);
                    return Some(args);
                }
            }
        }
        None
    }

    //TODO remove default
    fn translate_snapshot_entry(&self,
        /*typ: Ty<'tcx>,
        snapshot_var: Option<&ModelEntry>,
        encoded_typ_option: Option<String>,
        translated_domains: &mut TranslatedDomains,*/
        model_entry: Option<&ModelEntry>,
        typ: Option<Ty<'tcx>>,
        translated_domains: &mut TranslatedDomains,
        default: bool, //if we use default cases
    ) -> Entry {
        if let Some(ModelEntry::DomainValue(domain, var)) = model_entry{
            debug!("print cache: {:?}", translated_domains.cached_domains);
            if let Some(entry) = translated_domains.cached_domains.get(&(domain.clone(), var.clone())){
                debug!("found in cache");
                return entry.clone();
            }
        }
        /*if let Some(entry) = model_entry.and_then(|x| translated_domains.cached_domains.get(x)){ //check cache
            debug!("found in cache");
            return entry; 
        }*/
        debug!("typ: {:?}", typ.and_then(|x| Some(x.kind())));
        let entry = match (model_entry, typ.and_then(|x| Some(x.kind()))){
            (Some(ModelEntry::LitInt(string)),_) => Entry::Int(string.clone()),
            (Some(ModelEntry::LitFloat(string)),_) => Entry::Float(string.clone()),
            (Some(ModelEntry::LitBool(bool)),_) => Entry::Bool(bool.clone()),
            (Some(ModelEntry::DomainValue(domain_name, _)), Some(ty::TyKind::Ref(_, typ, _))) => {
                debug!("typ is ref");
                //this should never fail since a DomainValue can only exist if the corresponding domain exists
                let sil_domain = self.silicon_counterexample.domains.entries.get(domain_name).unwrap();
                debug!("domain for ref type: {:?}", domain_name);
                let sil_fn_name = format!("destructor${}$$target_current", domain_name);
                Entry::Ref(box self.extract_field_value(&sil_fn_name, Some(typ.clone()), model_entry, sil_domain, translated_domains, default))
            },
           (Some(ModelEntry::DomainValue(domain_name, _)), Some(ty::TyKind::Tuple(subst))) => {
                debug!("typ is tuple");
                let sil_domain = self.silicon_counterexample.domains.entries.get(domain_name).unwrap();
                debug!("silicon domain: {:?}", sil_domain);
                let len = subst.len();
                let mut fields = vec![];
                for i in 0..len {
                    let field_typ = subst[i];
                    debug!("field typ: {:?}", &field_typ.kind());
                    let field_name = format!("tuple_{}", i);
                    debug!("field name: {:?}", &field_name);
                    let sil_fn_name = format!("destructor${}$${}", domain_name, &field_name);
                    let field_entry = self.extract_field_value(&sil_fn_name, Some(field_typ), model_entry, sil_domain, translated_domains, default);
                    fields.push(field_entry);
                }
                Entry::Tuple(fields)
            },
                
            /*ty::TyKind::Adt(adt_def, subst) if adt_def.is_box() => {
                debug!("typ is box");
                let new_typ = subst.type_at(0);
                debug!("type inside box: {:?}", &new_typ);
                let entry = self.translate_silicon_entry_with_snapshot(new_typ, snapshot_var, encoded_typ_option, translated_domains).unwrap_or_default();
                Entry::Box(box entry)
            } ,*/
            (Some(ModelEntry::DomainValue(domain_name, ..)), Some(ty::TyKind::Adt(adt_def, subst))) if adt_def.is_struct() => {
                debug!("typ is struct");
                debug!("typ: {:?}", typ);
                //this should never fail since a DomainValue can only exist if the corresponding domain exists
                //let sil_domain = self.silicon_counterexample.domains.entries.get(domain_name);
                //debug!("Domain entry: {:?}", sil_domain);
                let variant = adt_def.variants().iter().next().unwrap();
                let struct_name = variant.ident(self.tcx).name.to_ident_string();
                //check if struct is a model
                if let Some((to_model, model_id), ) = self.encoder.get_type_specs(adt_def.did()).and_then(|p| p.has_model){
                    let entry = self.extract_model(model_entry, domain_name, translated_domains, default, to_model, model_id);
                    if let Entry::Struct{field_entries, custom_print_option,..} = entry{
                        Entry::Struct{
                            name: format!("{}_model",struct_name),
                            field_entries,
                            custom_print_option,
                        }
                    }  else {
                        entry
                    }
                } else {
                    let field_entries = self.translate_snapshot_adt_fields(
                        variant,
                        model_entry,
                        subst,
                        translated_domains,
                        default, 
                    );
                    let custom_print_option = self.encoder.get_type_specs(adt_def.did()).and_then(| p | self.custom_print(p.counterexample_print, None));
                    Entry::Struct {
                        name: struct_name,
                        field_entries,
                        custom_print_option,
                    }
                }
            },
            (Some(ModelEntry::DomainValue(domain_name, _)), Some(ty::TyKind::Adt(adt_def, subst))) if adt_def.is_enum() => {
                debug!("typ is enum");
                debug!("domain name: {:?}", domain_name);
                let disc_function_name = format!("discriminant${}", domain_name);//domain_name.strip_prefix("Snap$").unwrap_or_default());
                //self.lowerer.encode_discriminant_name(domain_name).ok().unwrap();
                debug!("discriminant function: {:?}", disc_function_name);
                //this should never fail since a DomainValue can only exist if the corresponding domain exists
                let sil_domain = self.silicon_counterexample.domains.entries.get(domain_name).unwrap();
                let sil_fn_param = vec![model_entry.cloned()];
                if let Some(disc_function) = sil_domain.functions.entries.get(&disc_function_name){
                    match disc_function.get_function_value_with_default(&sil_fn_param){
                        Some(ModelEntry::LitInt(disc_value)) => {
                            let super_name = format!("{:?}", adt_def);
                            debug!("enum name: {:?}", &super_name);
                            let disc_value_int = disc_value.parse::<u32>().unwrap();
                            debug!("discriminant: {:?}", &disc_value_int);
                            if let Some(variant) = adt_def.variants().iter().find(|x| get_discriminant_of_vardef(x) == Some(disc_value_int)){
                                debug!("variant found");
                                let variant_name = variant.ident(self.tcx).name.to_ident_string();
                                debug!("variant name: {:?}", &variant_name);
                                //let variant_domain_name = format!("{}${}$", domain_name, &variant_name);
                                //debug!("variant domain name: {:?}", &variant_domain_name);
                                //let variant_domain_option = self.silicon_counterexample.domains.entries.get(&variant_domain_name);
                                //debug!("variant domain: {:?}", variant_domain_option);
                                let destructor_sil_name = format!("destructor${}${}$value", domain_name, &variant_name);
                                 if let Some(value_function) = sil_domain.functions.entries.get(&destructor_sil_name){
                                    debug!("destructor found: {:?}", &value_function);
                                    let domain_entry = if default {
                                        value_function.get_function_value_with_default(&sil_fn_param)
                                    } else {
                                        value_function.get_function_value(&sil_fn_param)
                                    };
                                    debug!("new Model entry: {:?}", &domain_entry);
                                    let field_entries = self.translate_snapshot_adt_fields(&variant, domain_entry.as_ref(), subst, translated_domains, default);
                                    debug!("list of fields: {:?}", &field_entries);
                                    let custom_print_option = self.encoder.get_type_specs(adt_def.did()).and_then(| p | self.custom_print(p.counterexample_print, Some(variant_name.clone())));
                                    debug!("custom print option: {:?}", custom_print_option);
                                    return Entry::Enum {
                                        super_name,
                                        name: variant_name,
                                        field_entries,
                                        custom_print_option,
                                    };
                                }
                            }
                        },
                        _ =>  // should not be possible
                            debug!("discriminant value not int!"),
                    }
                    debug!("discriminant value not found");
                }
                Entry::Enum {
                    super_name: format!("{:?}", adt_def),
                    name: "?".to_string(),
                    field_entries: vec![],
                    custom_print_option: None,
                }
            },
            (Some(ModelEntry::DomainValue(domain_name, _)), _) => { //snapshot typ for primitive typ
                //this should never fail since a DomainValue can only exist if the corresponding domain exists
                let sil_domain = self.silicon_counterexample.domains.entries.get(domain_name).unwrap();
                debug!("domain for primitive type: {:?}", domain_name);
                let sil_fn_name = format!("destructor${}$$value", domain_name);
                self.extract_field_value(&sil_fn_name, None, model_entry, sil_domain, translated_domains, default)
            }  
            _ => Entry::Unknown,
        };
        if let Some(ModelEntry::DomainValue(domain, var)) = model_entry{//save in cache
            debug!("save in cache");
            translated_domains.cached_domains.insert((domain.clone(), var.clone()), entry.clone());
        }
        entry
    }
    
    fn translate_snapshot_adt_fields(&self,
    //domain_name: &String,
    variant: &ty::VariantDef,
    model_entry: Option<&ModelEntry>,
    //sil_domain_option: Option<&DomainEntry>, 
    subst: ty::subst::SubstsRef<'tcx>,
    translated_domains: &mut TranslatedDomains,
    default: bool, //if we use default cases
    ) -> Vec<(String, Entry)> {
        match model_entry {
            Some(ModelEntry::DomainValue(domain_name, _)) => {
                //this should never fail since a DomainValue can only exist if the corresponding domain exists
                let sil_domain = self.silicon_counterexample.domains.entries.get(domain_name).unwrap();
                debug!("translate fields");
                let mut fields = vec![];
                for f in &variant.fields {
                    let field_name = f.ident(self.tcx).name.to_ident_string();
                    debug!("field name: {:?}", &field_name);
                    let field_typ = f.ty(self.tcx, subst);
                    debug!("field typ: {:?}", &field_typ.kind());
                    let sil_fn_name = format!("destructor${}$$f${}", domain_name, &field_name);
                    /* if domain_name.ends_with("$"){
                        format!("destructor${}$$f${}", domain_name, &field_name)
                    } else { 
                        format!("destructor${}$$value", domain_name)
                    };*/
                    let field_entry = self.extract_field_value(&sil_fn_name, Some(field_typ), model_entry, sil_domain, translated_domains, default);

                    fields.push((field_name, field_entry));
                }
                debug!("list of fields: {:?}", &fields);
                fields
            },
            _ => iter::zip(variant.fields.iter().map(|x| x.ident(self.tcx).name.to_ident_string()), iter::repeat(Entry::Unknown)).collect()
        }
    }  

    fn extract_field_value(&self, 
    sil_fn_name: &String,
    field_typ: Option<Ty<'tcx>>,
    model_entry: Option<&ModelEntry>,
    sil_domain: &DomainEntry,
    translated_domains: &mut TranslatedDomains,
    default: bool, //if we use default cases
    ) -> Entry {
        debug!("function name: {:?}", &sil_fn_name);
        let sil_fn_param = vec![model_entry.cloned()];
        let field_value = if let Some(function) = sil_domain.functions.entries.get(sil_fn_name){
            if default {
                debug!("without default");
                function.get_function_value_with_default(&sil_fn_param)
            } else {
                debug!("with default");
                function.get_function_value(&sil_fn_param)
            }    
        } else {
            &None
        };
        debug!("field value: {:?}", field_value);
        self.translate_snapshot_entry(field_value.as_ref(), field_typ, translated_domains, default)
    }

    fn extract_model(&self,
        model_entry: Option<&ModelEntry>,
        domain_name: &String, 
        translated_domains: &mut TranslatedDomains,
        default: bool,
        to_model: String, 
        model_id: LocalDefId,
    )->Entry{
        debug!("typ has model");
        debug!("to model name: {:?}", to_model);
        let domain_name_wo_snap = domain_name.trim_start_matches("Snap");
        let ref_to_model_domain_name = format!("Snap$ref$Shared{}", domain_name_wo_snap); //might be called Snap$ref$Unique
        debug!("ref to model name: {}", ref_to_model_domain_name);
        let ref_to_model_function_name = format!("constructor${}$no_alloc", ref_to_model_domain_name); 
        debug!("ref to model function name: {}", ref_to_model_function_name);
        if let Some(sil_domain) = self.silicon_counterexample.domains.entries.get(&ref_to_model_domain_name){
            let sil_fn_param = vec![model_entry.cloned()];
            if let Some(ref_to_model_function) = sil_domain.functions.entries.get(&ref_to_model_function_name){
                debug!("function found");
                let sil_ref_domain = ref_to_model_function.get_function_value_with_default(&sil_fn_param);
                let sil_ref_fn_param = vec![sil_ref_domain.clone()];
                let sil_to_model_fn_name = format!("caller_for$m_{}$$model{}$",to_model, domain_name_wo_snap);
                debug!("sil to model fn name: {}", sil_to_model_fn_name);
                if let Some(sil_to_model_fn) = self.silicon_counterexample.functions.entries.get(&sil_to_model_fn_name){
                    debug!("caller function found");
                    let sil_model = sil_to_model_fn.get_function_value_with_default(&sil_ref_fn_param);
                    debug!("model found: {:?}", sil_model);
                    let model_typ = self.tcx.type_of(model_id);
                    debug!("typ: {:?}", model_typ);
                    return self.translate_snapshot_entry(sil_model.as_ref(), Some(model_typ), translated_domains, default);
                }
            } 
        }
        Entry::Unknown
    }
}

fn get_discriminant_of_vardef(vardef: &ty::VariantDef) -> Option<u32> {
    // TODO: this is not a good way to calculate discriminants
    // (might be wrong for enums with explicit discriminants, does not handle
    // large discriminant values)
    // instead we should maintain a mapping in the Enum predicate we create
    match vardef.discr {
        ty::VariantDiscr::Relative(x) => Some(x),
        _ => None,
    }
}


    /*


    fn entries_to_process(&self, encoder: &Encoder<'_, 'tcx>) -> Vec<(String, Span, String, Ty<'tcx>, bool)> {
        let mut entries_to_process = vec![];
        for vdi in &self.var_debug_info {
            let rust_name = vdi.name.to_ident_string();
            let span = vdi.source_info.span;
            let local: mir::Local = if let mir::VarDebugInfoContents::Place(place) = vdi.value {
                if let Some(local) = place.as_local() {
                    local
                } else {
                    continue;
                }
            } else {
                continue;
            };
            let index = local.index();
            let var_local = Local::from(local);
            let typ = self.local_variable_manager.get_type(var_local);
            let is_arg = index > 0 && index <= self.mir.arg_count;
            let vir_name = self.local_variable_manager.get_name(var_local);
            //let ty = ty::u32; // encoder.get_domain("Snap$U32");
            //let encoding = encoder.encode_snapshot_type(typ).ok().unwrap().encode_as_string();
            //debug!("Snapshot type: {:?}", encoding);
            //let tmp = encoder.encode_snapshot_type(typ).ok().unwrap().encode_as_string();
            //let tmp2 = Type::snapshot(typ)
            let domain_typ = Type::Snapshot(SnapshotType{
                label: typ.to_string(),
                arguments: vec![],
                variant: String::from(""),
            });
            //let snapshot_ty = encoder.encode_s
            let vir_high_typ = encoder.encode_snapshot_type(typ).ok().unwrap();
            //vir_high_typ
            //let vir_poly_typ = IntoPolymorphic::From(vir_high_typ);

            let type_encoder = TypeEncoder::new(encoder, typ);
            let encoded_type_name = type_encoder.encode_predicate_use().ok();
            debug!("The new type is: {:?}", encoded_type_name);
            entries_to_process.push((rust_name.clone(), span, vir_name.clone(), typ, is_arg));
        }
        entries_to_process
    }

    fn result_to_process(&self) -> (String, Span, Ty<'tcx>) {
        // return the Silicon-name of result + its type
        // other than for entries, this is not always same as the vir-name
        let return_local = Local::from(mir::Local::from_usize(0));
        assert!(self.local_variable_manager.is_return(return_local));

        let hir = self.tcx.hir();
        let hir_id = hir.local_def_id_to_hir_id(self.def_id.as_local().unwrap());
        let span = hir.fn_decl_by_hir_id(hir_id).unwrap().output.span();

        let vir_name = if !self.is_pure {
            self.local_variable_manager.get_name(return_local)
        } else {
            "Result()".to_string()
        };
        let typ = self.local_variable_manager.get_type(return_local);
        (vir_name, span, typ)
    }

    fn process_variable_at_label(
        &self,
        label: Option<&str>,
        var_name: &str,
        typ: Ty<'tcx>,
    ) -> Entry {
        let silicon_model = match label {
            // should only be called on labels that actually exist
            Some(lbl) => &self.silicon_counterexample.model.entries, //&self.silicon_counterexample.old_models.get(lbl).unwrap().entries,
            None => &self.silicon_counterexample.model.entries,
        };
        let opt_sil_entry = silicon_model.get(var_name);
        self.translate_silicon_entry(
            typ,
            opt_sil_entry,
            var_name.to_string(),
            silicon_model,
        ).unwrap_or_default()
    }

    fn translate_silicon_entry(
        &self,
        typ: Ty<'tcx>,
        sil_entry: Option<&ModelEntry>,
        vir_name: String,
        silicon_ce_entries: &FxHashMap<String, ModelEntry>,
    ) -> Option<Entry> {
        Some(match (typ.kind(), sil_entry) {
            (ty::TyKind::Bool, Some(ModelEntry::LitBool(value)))
                => Entry::Bool(*value),
            (ty::TyKind::Bool, Some(ModelEntry::Ref(_, map))) => {
                let entry = map.get("val_bool")?;
                if let ModelEntry::LitBool(value) = entry {
                    Entry::Bool(*value)
                } else {
                    return None;
                }
            }
            (ty::TyKind::Int(_) | ty::TyKind::Uint(_), _)
                => Entry::Int(self.translate_int(sil_entry)?),
            (ty::TyKind::Float(ty::FloatTy::F32), _)
                => Entry::Float(self.translate_float32(sil_entry)?),
            (ty::TyKind::Float(ty::FloatTy::F64), _)
            => Entry::Float(self.translate_float64(sil_entry)?),
            (ty::TyKind::Char, _) => {
                let value_str = self.translate_int(sil_entry)?;
                let value = value_str.parse::<u32>().ok()?;
                Entry::Char(char::from_u32(value)?)
            }
            (ty::TyKind::Ref(_, typ, _), Some(ModelEntry::Ref(_, map)))
                => Entry::Ref(box self.translate_silicon_entry(
                    *typ,
                    map.get("val_ref"),
                    format!("{}.val_ref", vir_name),
                    silicon_ce_entries,
                ).unwrap_or_default()),
            (ty::TyKind::Ref(..), _) => Entry::Ref(box Entry::Unknown),
            (ty::TyKind::Tuple(subst), Some(ModelEntry::Ref(_, map))) => {
                let len = subst.len();
                let mut fields = vec![];
                for i in 0..len {
                    let typ = subst[i];
                    let field_id = format!("tuple_{}", i);
                    let field_entry = map.get(&field_id);
                    fields.push(self.translate_silicon_entry(
                        typ,
                        field_entry,
                        format!("{}.{}", vir_name, field_id),
                        silicon_ce_entries,
                    ).unwrap_or_default());
                }
                Entry::Tuple(fields)
            }
            (ty::TyKind::Adt(adt_def, subst), _) if adt_def.is_struct() => {
                let variant = adt_def.variants().iter().next().unwrap();
                let struct_name = variant.ident(self.tcx).name.to_ident_string();
                let field_entries = self.translate_vardef(
                    variant,
                    sil_entry,
                    vir_name,
                    subst,
                    silicon_ce_entries,
                );
                Entry::Struct {
                    name: struct_name,
                    field_entries,
                }
            }
            (ty::TyKind::Adt(adt_def, subst), Some(ModelEntry::Ref(_, map))) if adt_def.is_enum() => {
                let super_name = format!("{:?}", adt_def);
                let mut variant_name = "?".to_string();
                let mut field_entries = vec![];

                let mut variant = None;
                let mut opt_discriminant = self.translate_int(map.get("discriminant"));
                //need to find a discriminant to do something
                if opt_discriminant.is_none() {
                    //try to find disc in the associated local variable
                    let opt_discr_locations = self.disc_info.get(&(self.def_id, vir_name.clone()));
                    if let Some(discr_locations) = opt_discr_locations {
                        for name in discr_locations {
                            let disc_entry = silicon_ce_entries.get(name);
                            let value = self.translate_int(disc_entry);
                            if value.is_some() {
                                opt_discriminant = value;
                                break;
                            }
                        }
                    }
                }
                if let Some(x) = opt_discriminant {
                    // FIXME: should be able to handle larger discriminantes
                    let discriminant = x.parse::<u32>().unwrap();
                    variant = adt_def.variants().iter().find(|x| get_discriminant_of_vardef(x) == Some(discriminant));
                    if let Some(v) = variant {
                        variant_name = v.ident(self.tcx).name.to_ident_string();
                    }
                }

                if let Some(var_def) = variant {
                    let sil_name = format!("enum_{}", variant_name);
                    let opt_enum_entry = map.get(&sil_name);
                    //at this point it should be a subroutine same for structs and enum:
                    field_entries = self.translate_vardef(
                        var_def,
                        opt_enum_entry,
                        vir_name,
                        subst,
                        silicon_ce_entries,
                    );
                }

                Entry::Enum {
                    super_name,
                    name: variant_name,
                    field_entries,
                }
            }
            (ty::TyKind::Adt(adt_def, _), _) if adt_def.is_enum()
                => Entry::Enum {
                    super_name: format!("{:?}", adt_def),
                    name: "?".to_string(),
                    field_entries: vec![],
                },
            _ => Entry::Unknown,
        })
    }

    fn translate_vardef(
        &self,
        variant: &ty::VariantDef,
        sil_entry: Option<&ModelEntry>,
        vir_name: String,
        subst: ty::subst::SubstsRef<'tcx>,
        silicon_ce_entries: &FxHashMap<String, ModelEntry>,
    ) -> Vec<(String, Entry)> {
        let mut field_entries = vec![];
        for f in &variant.fields {
            let field_name = f.ident(self.tcx).name.to_ident_string();
            let typ = f.ty(self.tcx, subst);

            // extract recursively
            let sil_name = format!("f${}", field_name);
            let new_vir_name = format!("{}.f${}", vir_name, field_name);
            let mut field_entry = Entry::Unknown;
            if let Some(ModelEntry::Ref(_name, map)) = sil_entry {
                let rec_entry = map.get(&sil_name);
                field_entry = match rec_entry {
                    Some(ModelEntry::RecursiveRef(refname)) => {
                        // this unwrap should never fail unless
                        // there is a fault in the Silicon implementation
                        let real_ref_entry = silicon_ce_entries.get(refname);
                        self.translate_silicon_entry(
                            typ,
                            real_ref_entry,
                            new_vir_name,
                            silicon_ce_entries,
                        ).unwrap_or_default()
                    },
                    _ => self.translate_silicon_entry(
                        typ,
                        rec_entry,
                        new_vir_name,
                        silicon_ce_entries,
                    ).unwrap_or_default(),
                };
            }
            field_entries.push((field_name, field_entry));
        }
        field_entries
    }

    fn translate_int(&self, opt_sil_entry: Option<&ModelEntry>) -> Option<String> {
        match opt_sil_entry {
            Some(ModelEntry::LitInt(value)) => Some(value.to_string()),
            Some(ModelEntry::Ref(_, map)) => {
                let entry = map.get("val_int");
                if let Some(ModelEntry::LitInt(value)) = entry {
                    Some(value.to_string())
                } else {
                    None
                }
            },
            _ => None,
        }
    }

    fn translate_float32(&self, opt_sil_entry: Option<&ModelEntry>) -> Option<String> {
        match opt_sil_entry {
            Some(ModelEntry::LitFloat(value)) => Some(value.to_string()),
            Some(ModelEntry::Ref(_, map)) => {
                let entry = map.get("val_float32");
                if let Some(ModelEntry::LitFloat(value)) = entry {
                    Some(value.to_string())
                } else {
                    None
                }
            },
            _ => None,
        }
    }

    fn translate_float64(&self, opt_sil_entry: Option<&ModelEntry>) -> Option<String> {
        match opt_sil_entry {
            Some(ModelEntry::LitFloat(value)) => Some(value.to_string()),
            Some(ModelEntry::Ref(_, map)) => {
                let entry = map.get("val_float64");
                if let Some(ModelEntry::LitFloat(value)) = entry {
                    Some(value.to_string())
                } else {
                    None
                }
            },
            _ => None,
        }
    }

    fn get_domain_hd_function(&self, typ: Ty<'tcx>, encoder: &Encoder<'_, 'tcx>) -> Option<&FunctionEntry>{
        let type_encoder = TypeEncoder::new(encoder, typ);
        if let Some(type_encoded) = type_encoder.encode_predicate_use().ok(){ //not sure if this function is supposed to be used that way
            debug!("encoded type: {:?}", type_encoded);
            let function_name = format!("snap$__$TY$__Snap${}$", type_encoded);
            debug!("heap dependent function name: {:?}", &function_name);
            return self.silicon_counterexample.functions.entries.get(&function_name);
            /*if let Some(hd_function) = self.silicon_counterexample.functions.entries.get(&function_name){
                return Some(hd_function.clone());
            }*/
        }
        None
    }        

    fn snapshots_to_process(&self, encoder: &Encoder<'_,'tcx>) -> Vec<(String, Span, String, Ty<'tcx>, Option<String>, bool)> {
        let mut entries_to_process = vec![];
        for vdi in &self.var_debug_info {
            let rust_name = vdi.name.to_ident_string();
            debug!("Rust name: {:?}", rust_name);
            let span = vdi.source_info.span;
            debug!("Span: {:?}", span);
            let local: mir::Local = if let mir::VarDebugInfoContents::Place(place) = vdi.value {
                if let Some(local) = place.as_local() {
                    local
                } else {
                    continue;
                }
            } else {
                continue;
            };
            let index = local.index();
            debug!("Index: {:?}", index);
            let var_local = Local::from(local);
            debug!("var_local: {:?}", var_local);
            let typ = self.local_variable_manager.get_type(var_local);
            debug!("typ: {:?}", typ);
            let type_encoder = TypeEncoder::new(encoder, typ);
            let encoded_type_name = type_encoder.encode_predicate_use().ok();
            /*let typ_encoder = TypeEncoder::new(encoder, typ);
            if let type_string = typ_encoder.encode_predicate_use().ok(){
                debug!("typ string: {:?}", type_string);
            }*/

            //let vir_high_typ = typ_encoder.encode_type();
            //let vir_poly_typ = IntoPolymorphic::From(vir_high_typ);
            //let typ_string = vir_poly_typ.encode_as_string();
            //debug!("type name in viper: {:?}", typ_string);
            //let typ_encoder = TypeEncoder::new(encoder, typ);
            // encoder.high_type_encoder_state.encode_type().ok()
            /*if let encoded_types = encoder.high_type_encoder_state.encoded_types.try_borrow().ok(){
                if let vir_poly_typ = encode_types.get(&typ).clone(){
                    let typ_string = vir_poly_typ.encode_as_string();
                    debug!("type name in viper: {:?}", typ_string);
                }
            }*/
            //let encoded_type = Type::TypeVar(typ);
            //debug!("encoded_type: {:?} ", encoded_type);
            //debug!("Type: {:?}", typ); 
            //let typ_string = format!("m_{:?}", typ);

            //let type_var = TypeVar{label: vir_high_typ.to_string()};
           // let type_string = Type::Snapshot(SnapshotType::from(type_var)).encode_as_string();

            //let type_string = Type::snapshot(type_var).encode_as_string();
            //debug!("typ string: {:?}", type_string);
            let is_arg = index > 0 && index <= self.mir.arg_count;
            debug!("is_arg: {:?}", is_arg);
            let vir_name = self.local_variable_manager.get_name(var_local);
            debug!("vir_name: {:?}", vir_name);
            entries_to_process.push((rust_name.clone(), span, vir_name.clone(), typ, encoded_type_name.clone(), is_arg));
        }
        entries_to_process
    }
    /*fn translate_snapshot_entry(
        &self,
        typ: Ty<'tcx>,
        sil_entry: &ModelEntry,
        silicon_ce_entries: &FxHashMap<String, ModelEntry>,
        translated_domains_value: &mut FxHashMap<String, Entry>
    ) -> Option<&Entry> {
        let domain_name = sil_entry.0;
        debug!("Domainname: {:?} ", domain_name);
        let domain_entry = sil_entry.1;
        debug!("Domainentry: {:?} ", domain_entry);
        let translated_domains_value_name = format!("{:?}_{:?}",domain_name, domain_entry);
        if translated_domains_value.contains_key(&translated_domains_value_name){
            return translated_domains_value.get(&translated_domains_value_name);
        }
        match typ.kind(){


            ty::TyKind::Adt(adt_def, subst) if adt_def.is_enum() => {
                let disc_function_name = format!("discriminant$__$TY$__{:?}$", domain_name);
                debug!("discriminant function: {:?}", disc_function_name);
                if let Some(disc_function)  = domain_entry.functions.entries.get(&disc_function_name){
                    let params = Vec::from(sil_entry.clone());
                    if let Some(disc_function_val) = disc_function.get_function_value(&params){
                        match disc_function_val{
                            ModelEntry::LitInt(x) => {
                                //construct counterexample:
                                
                            }
                            _ => {
                                debug!("discriminant value not int!");
                                return None;
                            }
                        }
                    } else {
                        debug!("not discriminat found!");
                        return None;
                    }
                    
                } else {
                    debug!("not discriminat function found!");
                    return None;
                }



                /*
                let super_name = format!("{:?}", adt_def);
                let mut variant_name = "?".to_string();
                let mut field_entries = vec![];

                let mut variant = None;
                let mut opt_discriminant = self.translate_int(map.get("discriminant"));
                //need to find a discriminant to do something
                if opt_discriminant.is_none() {
                    //try to find disc in the associated local variable
                    let opt_discr_locations = self.disc_info.get(&(self.def_id, vir_name.clone()));
                    if let Some(discr_locations) = opt_discr_locations {
                        for name in discr_locations {
                            let disc_entry = silicon_ce_entries.get(name);
                            let value = self.translate_int(disc_entry);
                            if value.is_some() {
                                opt_discriminant = value;
                                break;
                            }
                        }
                    }
                }
                if let Some(x) = opt_discriminant {
                    // FIXME: should be able to handle larger discriminantes
                    let discriminant = x.parse::<u32>().unwrap();
                    variant = adt_def.variants().iter().find(|x| get_discriminant_of_vardef(x) == Some(discriminant));
                    if let Some(v) = variant {
                        variant_name = v.ident(self.tcx).name.to_ident_string();
                    }
                }

                if let Some(var_def) = variant {
                    let sil_name = format!("enum_{}", variant_name);
                    let opt_enum_entry = map.get(&sil_name);
                    //at this point it should be a subroutine same for structs and enum:
                    field_entries = self.translate_vardef(
                        var_def,
                        opt_enum_entry,
                        vir_name,
                        subst,
                        silicon_ce_entries,
                    );
                }

                Entry::Enum {
                    super_name,
                    name: variant_name,
                    field_entries,
                }*/
                return None;
            }
            _ => None
        }
        
    }*/
}

fn get_discriminant_of_vardef(vardef: &ty::VariantDef) -> Option<u32> {
    // TODO: this is not a good way to calculate discriminants
    // (might be wrong for enums with explicit discriminants, does not handle
    // large discriminant values)
    // instead we should maintain a mapping in the Enum predicate we create
    match vardef.discr {
        ty::VariantDiscr::Relative(x) => Some(x),
        _ => None,
    }
}

*/