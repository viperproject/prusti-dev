use std::collections::HashMap;
use std::convert::TryFrom;

use viper::silicon_counterexample::*;
use viper::VerificationError;
use prusti_interface::data::ProcedureDefId;
use crate::encoder::Encoder;
use crate::encoder::places::{Local, LocalVariableManager, Place};
use crate::encoder::counterexample::*;

use rustc_middle::mir::{self, VarDebugInfo};
use rustc_middle::ty::{self, Ty, AdtKind, AdtDef, TyCtxt};
use rustc_span::Span;

pub fn backtranslate<'tcx>(
    encoder: &Encoder,
    def_id: ProcedureDefId,
    silicon_counterexample: &SiliconCounterexample,
) -> Counterexample {
    let translator = CounterexampleTranslator::new(encoder, def_id, silicon_counterexample);

    // TODO: ideally we would use the "main" counterexample from Silicon, the
    // one not associated with any label, because it contains the values of the
    // function when it fails. But currently most values can not be obtained
    // there because they are folded.
    // Instead, we use the last *labelled* counterexample.
    let last_label: Option<&String> = silicon_counterexample.label_order.last();

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
        Some(&old_impure_label)
    };

    // FIXME: there might be one too many levels of indirection here. Maybe we
    // can perform the `process_variable` part immediately with `*_to_process`.

    // to be processed
    let entries_to_process = translator.entries_to_process();
    let (result_sil_name, result_span, result_typ) = translator.result_to_process();

    // map those needed
    let mut entries = HashMap::new();
    let mut args = HashMap::new();

    for (rust_name, span, vir_name, typ, is_arg) in entries_to_process {
        if !translator.is_pure {
            let entry = translator.process_variable_at_label(last_label, &vir_name, typ);
            entries.insert((rust_name.clone(), span.clone()), entry);
        }
        if is_arg {
            let arg_entry = translator.process_variable_at_label(old_label, &vir_name, typ);
            args.insert((rust_name, span), arg_entry);
        }
    }
    let result = translator.process_variable_at_label(
        last_label,
        &result_sil_name,
        result_typ,
    );

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

pub struct CounterexampleTranslator<'ce, 'tcx> {
    mir: mir::Body<'tcx>,
    def_id: ProcedureDefId,
    silicon_counterexample: &'ce SiliconCounterexample,
    tcx: TyCtxt<'tcx>,
    is_pure: bool,
    disc_info: HashMap<(ProcedureDefId, String), Vec<String>>,
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

    fn entries_to_process(&self) -> Vec<(String, Span, String, Ty<'tcx>, bool)> {
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
            entries_to_process.push((rust_name.clone(), span.clone(), vir_name.clone(), typ, is_arg));
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
        label: Option<&String>,
        var_name: &String,
        typ: Ty<'tcx>,
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
    }

    fn translate_silicon_entry(
        &self,
        typ: Ty<'tcx>,
        sil_entry: Option<&ModelEntry>,
        vir_name: String,
        silicon_ce_entries: &HashMap<String, ModelEntry>,
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
            (ty::TyKind::Char, _) => {
                let value_str = self.translate_int(sil_entry)?;
                let value = value_str.parse::<u32>().ok()?;
                Entry::Char(char::from_u32(value)?)
            }
            (ty::TyKind::Ref(_, typ, _), Some(ModelEntry::Ref(_, map)))
                => Entry::Ref(box self.translate_silicon_entry(
                    typ,
                    map.get("val_ref"),
                    format!("{}.val_ref", vir_name),
                    silicon_ce_entries,
                ).unwrap_or_default()),
            (ty::TyKind::Ref(..), _) => Entry::Ref(box Entry::Unknown),
            (ty::TyKind::Tuple(subst), Some(ModelEntry::Ref(_, map))) => {
                let len = subst.types().count();
                let mut fields = vec![];
                for i in 0..len {
                    let typ = subst.type_at(i);
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
                let variant = adt_def.variants.iter().next().unwrap();
                let struct_name = variant.ident.name.to_ident_string();
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
                if !opt_discriminant.is_some() {
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
                    variant = adt_def.variants.iter()
                        .filter(|x| get_discriminant_of_vardef(x) == Some(discriminant))
                        .next();
                    if let Some(v) = variant {
                        variant_name = v.ident.name.to_ident_string();
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
        silicon_ce_entries: &HashMap<String, ModelEntry>,
    ) -> Vec<(String, Entry)> {
        let mut field_entries = vec![];
        for f in &variant.fields {
            let field_name = f.ident.name.to_ident_string();
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
