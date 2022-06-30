use rustc_hash::{FxHashMap};

use log::{debug};

use viper::silicon_counterexample::*;
use super::high::types::HighTypeEncoderInterface;
use super::counterexample_snapshot::DiscriminantsStateInterface;
use prusti_interface::data::ProcedureDefId;
use crate::encoder::Encoder;
use crate::encoder::places::{Local, LocalVariableManager};
use crate::encoder::counterexample::*;
use prusti_rustc_interface::middle::mir::{self, VarDebugInfo};
use prusti_rustc_interface::middle::ty::{self, Ty, TyCtxt};
use prusti_rustc_interface::span::Span;
use std::iter;


/*
1) directly work in entries to process (new function, _to_process) use main model
2) find hd function
3) get domain value
4) recusivly solve domain entries while caching old ones
5) integrate it into the current counterexample algorithm
6) 




*/


pub fn backtranslate(
    encoder: &Encoder,
    def_id: ProcedureDefId,
    silicon_counterexample: &SiliconCounterexample,
) -> Counterexample {
    let translator = CounterexampleTranslator::new(encoder, def_id, silicon_counterexample);

   //let tmp = encoder.mid_core_proof_encoder_state;
   

    // TODO: ideally we would use the "main" counterexample from Silicon, the
    // one not associated with any label, because it contains the values of the
    // function when it fails. But currently most values can not be obtained
    // there because they are folded.
    // Instead, we use the last *labelled* counterexample.
    let last_label: Option<&str> = silicon_counterexample.label_order.last().map(|label| label.as_str());

    let old_impure_label = if silicon_counterexample
        .label_order
        .contains(&"l0".to_string()) {
        "l0".to_string()
    } else {
        "old".to_string()
    };
    let old_label = if translator.is_pure {
        None
    } else {
        Some(old_impure_label.as_str())
    };

    // FIXME: there might be one too many levels of indirection here. Maybe we
    // can perform the `process_variable` part immediately with `*_to_process`.

    // to be processed
    let entries_to_process = translator.entries_to_process(&encoder);
    //let snapshots_to_process = translator.snapshots_to_process(encoder);
    let (result_sil_name, result_span, result_typ, result_encoded_typ) = translator.result_to_process(encoder);

    // map those needed
    let mut entries = FxHashMap::default();
    let mut args = FxHashMap::default();

    //cache
    let mut translated_domains = TranslatedDomains::default();


    for (rust_name, span, vir_name, typ, encoded_typ, is_arg) in entries_to_process {
        if !translator.is_pure {

            let (silicon_model, opt_sil_entry) = translator.get_silicon_at_label(last_label, &vir_name); //We cannot use the "main" model of silicon because of references
            
            let entry_snapshot = translator.translate_silicon_entry_with_snapshot(typ.clone(), opt_sil_entry, Some(encoded_typ.clone()), &mut translated_domains).unwrap_or_default();
            entries.insert((format!("snapshot_{}",rust_name.clone()), span), entry_snapshot.clone()); //FIXME remove that line, just to see the difference between the two versions
            
            
            let entry_heap_based = translator.translate_silicon_entry(typ, opt_sil_entry, vir_name.clone(), silicon_model).unwrap_or_default();
            let entry = entry_heap_based.merge(&entry_snapshot); //We prefer the heap based counterexample over the snapshot one
            
            
            /*entries.insert((format!("snapshot_{}",rust_name.clone()), span), entry.clone()); //FIXME remove that line, just to see the difference between the two versions
            if matches!(entry, Entry::Unknown) { //if the snapshot translation fails it will try the heap based one
                entry = translator.translate_silicon_entry(typ, opt_sil_entry, vir_name.clone(), silicon_model).unwrap_or_default();
            }*/
            /*
            
            let entry = translator.process_variable_at_label(last_label, &vir_name, typ.clone(), &encoded_typ);
            entries.insert((rust_name.clone(), span.clone()), entry);


            //have to decide which label
            //let opt_sil_entry = translator.silicon_counterexample.model.entries.get(&vir_name);
            let silicon_model = match last_label {
                // should only be called on labels that actually exist
                Some(lbl) => &translator.silicon_counterexample.old_models.get(lbl).unwrap().entries,
                None => &translator.silicon_counterexample.model.entries,
            };
            let opt_sil_entry = silicon_model.get(&vir_name);
            let entry2 = translator.translate_silicon_entry_with_snapshot(typ.clone(), opt_sil_entry, Some(encoded_typ.clone()));*/
            entries.insert((format!("{}",rust_name.clone()), span), entry);
        }
        if is_arg {
            let (silicon_model, opt_sil_entry) = translator.get_silicon_at_label(old_label, &vir_name);
            let arg_entry = translator.translate_silicon_entry(typ, opt_sil_entry, vir_name.clone(), silicon_model).unwrap_or_default();
            //let arg_entry = translator.process_variable_at_label(old_label, &vir_name, typ, &encoded_typ);
            args.insert((rust_name, span), arg_entry);
        }
    }
           
    let (silicon_model, opt_sil_entry) = translator.get_silicon_at_label(last_label, &result_sil_name); //We cannot use the "main" model of silicon because of references

    let result_entry_snapshot = translator.translate_silicon_entry_with_snapshot(result_typ.clone(), opt_sil_entry, Some(result_encoded_typ), &mut translated_domains).unwrap_or_default();
    entries.insert(("snapshot_result".to_string(), result_span), result_entry_snapshot.clone()); //FIXME remove that line, just to see the difference between the two versions
    
    
    let result_entry_heap_based = translator.translate_silicon_entry(result_typ, opt_sil_entry, result_sil_name, silicon_model).unwrap_or_default();
    let result = result_entry_heap_based.merge(&result_entry_snapshot); //We prefer the heap based counterexample over the snapshot one
    
    /*let result = translator.process_variable_at_label(
        last_label,
        &result_sil_name,
        result_typ,
        &result_encoded_typ,
    );*/

    let mut ce_entries = vec![];

    // Due to translation to Viper functions, there are no locals in the
    // counterexample for pure functions. We can only see the arguments.
    let entries = if translator.is_pure {
        args.clone()
    } else {
        entries
    };

    // sort by span so we can compare output in tests
    let mut sorted_entries = entries.into_iter().collect::<Vec<_>>();
    sorted_entries.sort_by(|a, b| a.0.1.cmp(&b.0.1));

    // add counterexample notes for arguments and locals
    for (place, entry) in sorted_entries.into_iter() {
        // place is a tuple (Name of the variable, Option<Span>)
        ce_entries.push(if let Some(entry_arg) = args.get(&place) {
            CounterexampleEntry::with_two_values(
                place.1,
                Some(place.0),
                entry_arg.clone(),
                entry,
            )
        } else {
            CounterexampleEntry::with_one_value(
                place.1,
                Some(place.0),
                entry,
            )
        });
    }

    // add counterexample note for the return value, if any
    if !result.is_unit() {
        ce_entries.push(CounterexampleEntry::with_one_value(
            result_span,
            None,
            result,
        ));
    }

    Counterexample::new(ce_entries)
}

//Cache for domains
#[derive(Default)]
struct TranslatedDomains{
    in_progress: Vec<(String, String)>, //(domain name, var name)
    cached_domains: FxHashMap<(String, String), Entry>,
}



pub struct CounterexampleTranslator<'ce, 'tcx> {
    mir: mir::Body<'tcx>,
    def_id: ProcedureDefId,
    silicon_counterexample: &'ce SiliconCounterexample,
    tcx: TyCtxt<'tcx>,
    is_pure: bool,
    pub(super) disc_info: FxHashMap<(ProcedureDefId, String), Vec<String>>,
    var_debug_info: Vec<VarDebugInfo<'tcx>>,
    local_variable_manager: LocalVariableManager<'tcx>,
}

impl<'ce, 'tcx> CounterexampleTranslator<'ce, 'tcx> {
    pub fn new(
        encoder: &Encoder<'_, 'tcx>,
        def_id: ProcedureDefId,
        silicon_counterexample: &'ce SiliconCounterexample,
    ) -> Self {
        let mir = encoder.env().get_procedure(def_id).get_mir().clone();
        let var_debug_info = mir.var_debug_info.clone();
        let local_variable_manager = LocalVariableManager::new(&mir.local_decls);
        Self {
            mir,
            def_id,
            silicon_counterexample,
            tcx: encoder.env().tcx(),
            is_pure: false, // No verified functions are pure. encoder.is_pure(def_id),
                            // TODO: This assumption should allow simplifying the translator quite a bit.
            disc_info: encoder.discriminants_info(),
            var_debug_info,
            local_variable_manager,
        }
    }

    fn entries_to_process(&self, encoder: &Encoder<'_, 'tcx>) -> Vec<(String, Span, String, Ty<'tcx>, String, bool)> {
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
            let encoded_typ = self.get_encoded_type(typ.clone(), &encoder);
            entries_to_process.push((rust_name.clone(), span, vir_name.clone(), typ, encoded_typ, is_arg));
        }
        entries_to_process
    }

    fn result_to_process(&self, encoder: &Encoder<'_,'tcx>) -> (String, Span, Ty<'tcx>, String) {
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
        let encoded_typ = self.get_encoded_type(typ.clone(), encoder);
        (vir_name, span, typ, encoded_typ)
    }

    fn get_silicon_at_label(&self, label: Option<&str> , vir_name: &str) -> (&FxHashMap<String, ModelEntry>, Option<&ModelEntry>){
        let silicon_model = match label {
            // should only be called on labels that actually exist
            Some(lbl) => &self.silicon_counterexample.old_models.get(lbl).unwrap().entries,
            None => &self.silicon_counterexample.model.entries,
        };
        (silicon_model, silicon_model.get(vir_name))
    }



    /*fn process_variable_at_label(
        &self,
        label: Option<&str>,
        var_name: &str,
        typ: Ty<'tcx>,
        encoded_typ: &String,
    ) -> Entry {
        let silicon_model = match label {
            // should only be called on labels that actually exist
            Some(lbl) => &self.silicon_counterexample.old_models.get(lbl).unwrap().entries,
            None => &self.silicon_counterexample.model.entries,
        };
        let opt_sil_entry = silicon_model.get(var_name);
        self.translate_silicon_entry(
            typ,
            opt_sil_entry,
            var_name.to_string(),
            silicon_model,
        ).unwrap_or_default()
    }*/

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
            (ty::TyKind::Adt(adt_def, subst),Some(ModelEntry::Ref(_, map))) if adt_def.is_box() => {
                debug!("heap: typ is box");
                let new_typ = subst.type_at(0);
                debug!("heap: type inside box: {:?}", &new_typ);
                let entry = self.translate_silicon_entry(new_typ,map.get("val_ref"), format!("{}.val_ref", vir_name), silicon_ce_entries).unwrap_or_default();
                debug!("heap: print entry: {:?}", entry);
                debug!("heap: print sil_entry: {:?}", sil_entry);
                Entry::Box(box entry)
            }
            (ty::TyKind::Adt(adt_def, _),_) if adt_def.is_box() => Entry::Box(box Entry::Unknown),
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

    fn get_encoded_type(&self, typ: Ty<'tcx>, encoder: &Encoder<'_, 'tcx>) -> String{
        match encoder.encode_type(typ).ok(){
            Some(poly_typ) => format!("Snap${}",poly_typ.encode_as_string()),
            _ => "".to_string(),
        }
    }

    fn get_hd_function_value(&self, encoded_typ: &String, params: &Vec<Option<ModelEntry>>) -> &Option<ModelEntry>{
        debug!("Encoded type: {:?}", encoded_typ);
        let function_name = format!("snap$__$TY$__{}$", encoded_typ); //snap$__$TY$__Snap$struct$m_X$ //struct$m_X
        debug!("heap dependent function name: {:?}", &function_name);
        if let Some(hd_function) = self.silicon_counterexample.functions.entries.get(&function_name){
            hd_function.get_function_value(params)
        } else {
            &None
        }
       
    }        
    
    fn translate_silicon_entry_with_snapshot(&self,
        typ: Ty<'tcx>,
        sil_entry: Option<&ModelEntry>,
        encoded_typ_option: Option<String>,
        translated_domains: &mut TranslatedDomains,
    ) -> Option<Entry> {
        debug!("translate silicon entry: {:?}", &sil_entry);
        Some(match sil_entry {
            Some(ModelEntry::LitInt(string)) =>  match typ.kind() {
                ty::TyKind::Int(_) => Entry::Int(string.clone()), 
                ty::TyKind::Char => {
                    let value_int = string.parse::<u32>().ok()?;
                    Entry::Char(char::from_u32(value_int)?)
                },
                _ => Entry::Unknown
            }
            Some(ModelEntry::LitFloat(string)) => Entry::Float(string.clone()),
            Some(ModelEntry::LitBool(bool)) => Entry::Bool(bool.clone()),
            Some(ModelEntry::Ref(name, _))=> {  
                let encoded_typ = encoded_typ_option.unwrap_or_default();
                debug!("ref entry: {:?}", &encoded_typ);
                if let Some(_) = self.silicon_counterexample.domains.entries.get(&encoded_typ) {  //need a domain to extract a counterexample
                    let hd_function_param = vec![Some(ModelEntry::Var(name.clone()))];
                    let snapshot_var = self.get_hd_function_value(&encoded_typ, &hd_function_param);
                    debug!("snapshot found: {:?}", &snapshot_var);
                    self.translate_snapshot_entry(typ, snapshot_var.as_ref(), Some(encoded_typ), translated_domains)          
                } else {
                    //if we don't find a domain we might find the ref value in the heap based encoding
                    //this part is not perfect, alternatively we could have a map of all var_ref assignments
                    //from the viper program and choose the last one before the failing assert.
                    self.translate_snapshot_entry(typ, sil_entry, Some(encoded_typ), translated_domains)
                }
            },
            Some(ModelEntry::RecursiveRef(ref_name)) => {
                    // this unwrap should never fail unless
                    // there is a fault in the Silicon implementation
                    let real_ref_entry = self.silicon_counterexample.model.entries.get(ref_name);
                    debug!("real ref entry: {:?}", real_ref_entry);
                    self.translate_silicon_entry_with_snapshot(typ, real_ref_entry, encoded_typ_option, translated_domains).unwrap_or_default()
            },  
            Some(ModelEntry::DomainValue(name, var)) => 
                //first we try if it is already cached
                if let Some(snapshot_entry) = translated_domains.cached_domains.get(&(name.clone(), var.clone())){
                    debug!("Domain value found in cache");
                    snapshot_entry.clone()
                } else if translated_domains.in_progress.contains(&(name.clone(), var.clone())){ //found cycle
                    debug!("cycle detected");
                    Entry::Unknown
                } else {
                    //only push if typ is not ref or box 
                    match typ.kind(){
                        ty::TyKind::Ref(..) => (),
                        ty::TyKind::Adt(adt_def, _) if adt_def.is_box() => (),
                        _ => translated_domains.in_progress.push((name.clone(), var.clone())),
                    }
                    debug!("translated domains cached: {:?}", translated_domains.cached_domains);
                    debug!("translated domains in progress: {:?}", translated_domains.in_progress);
                    let entry = self.translate_snapshot_entry(typ, sil_entry, encoded_typ_option, translated_domains);

                    translated_domains.in_progress.retain(|x| x.0 != name.clone() && x.1 != var.clone());
                    translated_domains.cached_domains.insert((name.clone(), var.clone()), entry.clone());
                    debug!("translated domains cached: {:?}", translated_domains.cached_domains);
                    debug!("translated domains in progress: {:?}", translated_domains.in_progress);
                    entry
                },
        _ => Entry::Unknown,
        })
    }

    
    fn translate_snapshot_entry(&self,
        typ: Ty<'tcx>,
        snapshot_var: Option<&ModelEntry>,
        encoded_typ_option: Option<String>,
        translated_domains: &mut TranslatedDomains,
    ) -> Entry {
        debug!("typ: {:?}", &typ.kind());
        match typ.kind(){
           ty::TyKind::Ref(_, typ, _) => {
               match snapshot_var{
                    Some(ModelEntry::Ref(_, map)) => {
                    debug!("ty is ref");
                    if let Some(encoded_typ) = encoded_typ_option{
                        let new_encoded_typ = Some(encoded_typ.replacen("ref$", "", 1)); //remove a ref
                        debug!("new encoded_typ: {:?}", &new_encoded_typ);
                        let sil_entry = map.get("val_ref");
                        debug!("new silicon Entry: {:?} ", sil_entry);
                        Entry::Ref(box self.translate_silicon_entry_with_snapshot(typ.clone(), sil_entry, new_encoded_typ, translated_domains).unwrap_or_default())
                    } else {
                       Entry::Ref(box Entry::Unknown)
                    }
                },
                _ => Entry::Ref(box Entry::Unknown),
               }
           },
            ty::TyKind::Tuple(subst) => {
                debug!("typ is tuple");
                match snapshot_var{
                    Some(ModelEntry::DomainValue(domain, _)) => {
                        //should always be called with a DomainValue
                    let sil_domain = self.silicon_counterexample.domains.entries.get(domain).unwrap();
                    let encoded_typ = encoded_typ_option.unwrap_or_default();
                    let len = subst.len();
                    let mut fields = vec![];
                    for i in 0..len {
                        let field_typ = subst[i];
                        debug!("field typ: {:?}", &field_typ.kind());
                        let field_name = format!("tuple_{}", i);
                        debug!("field name: {:?}", &field_name);
                        let sil_fn_name = format!("{}$0$field${}__$TY$__", &encoded_typ, &field_name);
                        let field_entry = self.extract_field_value(&sil_fn_name, field_typ, snapshot_var, sil_domain, translated_domains);
                        fields.push(field_entry.unwrap_or_default());
                    }
                    Entry::Tuple(fields)
                    },
                    _ => Entry::Tuple(vec![]),
                }
            },
            ty::TyKind::Adt(adt_def, subst) if adt_def.is_box() => {
                debug!("typ is box");
                let new_typ = subst.type_at(0);
                debug!("type inside box: {:?}", &new_typ);
                let entry = self.translate_silicon_entry_with_snapshot(new_typ, snapshot_var, encoded_typ_option, translated_domains).unwrap_or_default();
                Entry::Box(box entry)
            } ,
            ty::TyKind::Adt(adt_def, subst) if adt_def.is_struct() => {
                debug!("typ is struct");
                let variant = adt_def.variants().iter().next().unwrap();
                let struct_name = variant.ident(self.tcx).name.to_ident_string();
                let field_entries = self.translate_snapshot_adt_fields(
                    variant,
                    snapshot_var,
                    encoded_typ_option.unwrap_or_default(),
                    subst,
                    translated_domains,
                );
                Entry::Struct {
                    name: struct_name,
                    field_entries,
                }
            },
            ty::TyKind::Adt(adt_def, subst) if adt_def.is_enum() => {
                debug!("typ is enum");
                match snapshot_var{
                    Some(ModelEntry::DomainValue(domain, _)) => {
                        if let Some(encoded_typ) = encoded_typ_option {
                            let disc_function_name = format!("discriminant$__$TY$__{}$", &encoded_typ);
                            debug!("discriminant function: {:?}", disc_function_name);
                            //this should never fail since a DomainValue can only exist if the corresponding domain exists
                            let sil_domain = self.silicon_counterexample.domains.entries.get(domain).unwrap();
                            let sil_fn_param = vec![snapshot_var.cloned()];
                            if let Some(disc_function) = sil_domain.functions.entries.get(&disc_function_name){
                                match disc_function.get_function_value(&sil_fn_param){
                                    Some(ModelEntry::LitInt(disc_value)) => {
                                        let super_name = format!("{:?}", adt_def);
                                        debug!("enum name: {:?}", &super_name);
                                        let disc_value_int = disc_value.parse::<u32>().unwrap();
                                        debug!("discriminant: {:?}", &disc_value_int);
                                        if let Some(variant) = adt_def.variants().iter().find(|x| get_discriminant_of_vardef(x) == Some(disc_value_int)){
                                            debug!("variant found");
                                            let variant_name = variant.ident(self.tcx).name.to_ident_string();
                                            debug!("variant name: {:?}", &variant_name);
                                            let field_entries = self.translate_snapshot_adt_fields(&variant, snapshot_var, encoded_typ, subst, translated_domains);
                                            return Entry::Enum {
                                                super_name,
                                                name: variant_name,
                                                field_entries,
                                            };
                                        }
                                    }
                                    _ =>  // should not be possible
                                        debug!("discriminant value not int!"),
                                }
                                debug!("discriminant value not found");
                            }
                            debug!("discriminat function not found!");
                        }
                    }, 
                    _ => ()
                }
                Entry::Enum {
                    super_name: format!("{:?}", adt_def),
                    name: "?".to_string(),
                    field_entries: vec![],
                }
            },
            _ => Entry::Unknown,
        }
    }

    fn translate_snapshot_adt_fields(&self,
        variant: &ty::VariantDef,
        snapshot_var: Option<&ModelEntry>,
        encoded_typ: String, 
        subst: ty::subst::SubstsRef<'tcx>,
        translated_domains: &mut TranslatedDomains,
        ) -> Vec<(String, Entry)> {
            debug!("translate fields");
            match snapshot_var {
                Some(ModelEntry::DomainValue(domain, _)) => {let mut fields = vec![];
                    debug!("sil entry is domain value");
                    //this should never fail since a DomainValue can only exist if the corresponding domain exists
                    let sil_domain = self.silicon_counterexample.domains.entries.get(domain).unwrap();
                    for f in &variant.fields {
                        let field_name = f.ident(self.tcx).name.to_ident_string();
                        debug!("field name: {:?}", &field_name);
                        let field_typ = f.ty(self.tcx, subst);
                        debug!("field typ: {:?}", &field_typ.kind());
                        let sil_fn_name = format!("{}$0$field$f${}__$TY$__", &encoded_typ, &field_name);
                        let field_entry = self.extract_field_value(&sil_fn_name, field_typ, snapshot_var, sil_domain, translated_domains);
                        fields.push((field_name, field_entry.unwrap_or_default()));
                    }
                    debug!("list of fields: {:?}", &fields);
                    fields
                }
                _ => {//if the function is called with anything else than a DomainValue
                    debug!("not a snapshot value: {:?}", &snapshot_var); 
                    iter::zip(variant.fields.iter().map(|x| x.ident(self.tcx).name.to_ident_string()), iter::repeat(Entry::Unknown)).collect()
                }
            }
    }
    fn extract_field_value(&self, 
    sil_fn_name: &String,
    field_typ: Ty<'tcx>,
    snapshot_var: Option<&ModelEntry>,
    sil_domain: &DomainEntry,
    translated_domains: &mut TranslatedDomains,
    ) -> Option<Entry> {
    
        debug!("function name: {:?}", &sil_fn_name);
        let sil_fn_param = vec![snapshot_var.cloned()];
        let field_value = if let Some(function) = sil_domain.functions.entries.get(sil_fn_name){
                function.get_function_value(&sil_fn_param)
            } else {
                &None
        };
        debug!("field value: {:?}", &field_value);
        let encoded_typ_field = match field_value  {
            Some(ModelEntry::DomainValue(domain, _)) => Some(domain.clone()),
            _ => None,
        };
        debug!("encoded type field: {:?}", &encoded_typ_field);
        self.translate_silicon_entry_with_snapshot(field_typ, field_value.as_ref(), encoded_typ_field, translated_domains)
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
