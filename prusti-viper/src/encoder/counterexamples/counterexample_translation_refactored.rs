use super::{counterexample_refactored::*, VarMapping, VarMappingInterface};
use crate::encoder::{
    counterexamples::mapping::PureFunction,
    errors::PositionManager,
    mir::{pure::PureFunctionEncoderInterface, specifications::SpecificationsInterface},
    places::{Local, LocalVariableManager},
    Encoder,
};
use prusti_common::config;
use prusti_interface::data::ProcedureDefId;
use prusti_rustc_interface::{
    ast::LitKind,
    errors::MultiSpan,
    hir::{def_id::LocalDefId, Block, Expr, ExprKind, Path, QPath, StmtKind},
    middle::{
        mir::{self, VarDebugInfo},
        ty::{self, Ty, TyCtxt},
    },
    span::source_map::Spanned,
};
use rustc_hash::FxHashMap;
use std::{iter, vec};
use viper::silicon_counterexample::*;

pub fn backtranslate(
    encoder: &Encoder,
    position_manager: &PositionManager,
    def_id: ProcedureDefId,
    silicon_counterexample: &SiliconCounterexample,
) -> Counterexample {
    let mut translator = CounterexampleTranslator::new(encoder, def_id, silicon_counterexample);

    translator.create_mapping(def_id, encoder); //creates the mapping between mir var and the corresponding snapshot var
    let label_markers = translator.get_label_markers(false);
    if let Some(path) = config::save_failing_trace_to_file() {
        let label_markers = translator.get_label_markers(true);
        let mut file = std::fs::File::create(path).unwrap();
        serde_json::to_writer_pretty(&mut file, &label_markers).unwrap();
        file.sync_all().unwrap();
    }

    let counterexample_entry_vec = translator.process_entries(position_manager, &label_markers);

    Counterexample::new(counterexample_entry_vec)
}

pub struct CounterexampleTranslator<'ce, 'tcx, 'v> {
    encoder: &'ce Encoder<'v, 'tcx>,
    silicon_counterexample: &'ce SiliconCounterexample,
    tcx: TyCtxt<'tcx>,
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
            encoder,
            silicon_counterexample,
            tcx: encoder.env().tcx(),
            var_debug_info,
            local_variable_manager,
            var_mapping: Default::default(),
        }
    }
    ///get all label markers and there value in the counterexample
    ///
    /// `default_for_not_found` – the value to use for labels that are not
    /// found. For counterexamples, it should be `false` to show only the blocks
    /// that were certainly visited to the user. For generating the failing
    /// trace, it should be `true` to not delete blocks that were potentially
    /// visited.
    fn get_label_markers(&self, default_for_not_found: bool) -> FxHashMap<String, bool> {
        self.var_mapping
            .labels_successor_mapping
            .keys()
            .map(|label| {
                match self
                    .silicon_counterexample
                    .model
                    .entries
                    .get(&format!("{label}$marker"))
                {
                    Some(ModelEntry::LitBool(b)) => (label.clone(), *b),
                    _ => (label.clone(), default_for_not_found),
                }
            })
            .collect::<FxHashMap<String, bool>>()
    }

    //Given a MIR var name, it returns all relevant snapshot variables
    fn get_trace_of_var(
        &self,
        position_manager: &PositionManager,
        var: &String,
        label_markers: &FxHashMap<String, bool>,
    ) -> Vec<(String, MultiSpan)> {
        let mut label = "start_label".to_string();
        let mut snapshot_var_vec = Vec::new();
        if let Some(label_snapshot_mapping) = self.var_mapping.var_snaphot_mapping.get(var) {
            loop {
                if let Some(snapshot_vars) = label_snapshot_mapping.get(&label) {
                    snapshot_var_vec.extend(
                        snapshot_vars.iter().map(|x| {
                            (x.name.clone(), self.get_span(position_manager, &x.position))
                        }),
                    );
                }
                if let Some(next) = self.get_successor(&label, label_markers) {
                    label = next.to_string();
                } else {
                    break;
                }
            }
        }
        snapshot_var_vec
    }

    fn process_entries(
        &self,
        position_manager: &PositionManager,
        label_markers: &FxHashMap<String, bool>,
    ) -> Vec<CounterexampleEntry> {
        //variables
        let mut entries = vec![];

        for vdi in &self.var_debug_info {
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
            let var_local = Local::from(local);
            let typ = self.local_variable_manager.get_type(var_local);
            let vir_name = self.local_variable_manager.get_name(var_local);
            let trace = self.get_trace_of_var(position_manager, &vir_name, label_markers);
            let history = self.process_entry(&trace, typ);
            entries.push(CounterexampleEntry::new(Some(rust_name), history))
        }

        //result
        let vir_name = "_0".to_string();
        let return_local = Local::from(mir::Local::from_usize(0));
        let typ = self.local_variable_manager.get_type(return_local);
        let trace = self.get_trace_of_var(position_manager, &vir_name, label_markers);
        let history = self.process_entry(&trace, typ);
        entries.push(CounterexampleEntry::new(None, history));

        //pure functions
        let mut relevant_pure_functions = vec![];

        for (key, val) in self.var_mapping.pure_functions_mapping.iter() {
            if label_markers.get(key) == Some(&true) {
                relevant_pure_functions.extend(val.iter());
            }
        }
        for pure_fn in relevant_pure_functions {
            let ce_pure_fn = self.process_pure_function(pure_fn, position_manager);
            let mut pure_fn_name = format!(
                "{}()",
                pure_fn
                    .name
                    .trim_start_matches("caller_for$m_")
                    .trim_end_matches('$')
            );
            pure_fn_name = pure_fn_name.split('$').last().unwrap().to_string(); //remove prefix of functions in implementations
            entries.push(CounterexampleEntry::new(
                Some(pure_fn_name),
                vec![ce_pure_fn],
            ));
        }

        entries
    }

    fn process_pure_function(
        &self,
        pure_fn: &PureFunction,
        position_manager: &PositionManager,
    ) -> (Entry, MultiSpan) {
        let typ = self
            .encoder
            .get_proc_def_id(pure_fn.name.trim_start_matches("caller_for$").to_string())
            .map(|fn_proc_id| {
                self.tcx
                    .fn_sig(fn_proc_id)
                    .instantiate_identity()
                    .skip_binder()
                    .output()
            });
        let sil_arguments = pure_fn
            .args
            .iter()
            .map(|arg| self.silicon_counterexample.model.entries.get(arg).cloned())
            .collect();

        let return_value = if let Some(function) = self
            .silicon_counterexample
            .functions
            .entries
            .get(&pure_fn.name)
        {
            function.get_function_value(&sil_arguments)
        } else {
            &None
        };
        (
            self.translate_snapshot_entry(return_value.as_ref(), typ, true),
            self.get_span(position_manager, &pure_fn.position),
        )
    }

    fn process_entry(
        &self,
        trace: &Vec<(String, MultiSpan)>,
        ty: Ty<'tcx>,
    ) -> Vec<(Entry, MultiSpan)> {
        let mut entries = vec![];
        for (snapshot_var, span) in trace {
            let model_entry = self.silicon_counterexample.model.entries.get(snapshot_var);
            let entry = self.translate_snapshot_entry(model_entry, Some(ty), true);
            entries.push((entry, span.clone()));
            if config::print_counterexample_if_model_is_present() {
                //if the original type should be part of the counterexample in addition to the model
                match &ty.kind() {
                    &ty::TyKind::Adt(adt_def, _) if adt_def.is_struct() => {
                        if self
                            .encoder
                            .get_type_specs(adt_def.did())
                            .and_then(|p| p.model)
                            .is_some()
                        {
                            let entry = self.translate_snapshot_entry(model_entry, Some(ty), false); //extract the counterexample of the original type
                            entries.push((entry, span.clone()));
                        }
                    }
                    _ => (),
                }
            }
        }
        entries
    }

    fn custom_print(
        &self,
        prusti_counterexample_print: Vec<(Option<String>, LocalDefId)>,
        variant_option: Option<String>,
    ) -> Option<Vec<String>> {
        let def_id_option = match variant_option {
            Some(_) => prusti_counterexample_print
                .iter()
                .find(|x| x.0 == variant_option),
            None => prusti_counterexample_print.first(),
        };

        if let Some(def_id) = def_id_option {
            let expr = &self
                .tcx
                .hir()
                .body(self.tcx.hir().body_owned_by(def_id.1))
                .value;
            if let ExprKind::Block(
                Block {
                    expr:
                        Some(Expr {
                            kind: ExprKind::If(_, expr, _),
                            ..
                        }),
                    ..
                },
                _,
            ) = expr.kind
            {
                if let ExprKind::Block(block, _) = expr.kind {
                    let stmts = block.stmts;
                    let args = stmts
                        .iter()
                        .filter_map(|stmt| {
                            match stmt.kind {
                                StmtKind::Semi(Expr {
                                    kind:
                                        ExprKind::Lit(Spanned {
                                            node: LitKind::Str(symbol, _),
                                            ..
                                        }),
                                    ..
                                }) => Some(symbol.to_ident_string()), //first arg
                                StmtKind::Semi(Expr {
                                    kind:
                                        ExprKind::Lit(Spanned {
                                            node: LitKind::Int(int, _),
                                            ..
                                        }),
                                    ..
                                }) => Some(int.to_string()), //unnamed fields
                                StmtKind::Semi(Expr {
                                    kind: ExprKind::Path(QPath::Resolved(_, Path { segments, .. })),
                                    ..
                                }) => {
                                    //named fields
                                    segments.first().map(|path_segment| {
                                        path_segment.ident.name.to_ident_string()
                                    })
                                }
                                _ => None,
                            }
                        })
                        .collect::<Vec<String>>();
                    return Some(args);
                }
            }
        }
        None
    }

    fn translate_snapshot_entry(
        &self,
        model_entry: Option<&ModelEntry>,
        typ: Option<Ty<'tcx>>,
        model: bool, //if false, ignore models
    ) -> Entry {
        match (model_entry, typ.map(|x| x.kind())) {
            (Some(ModelEntry::LitInt(string)), Some(ty::TyKind::Char)) => {
                if let Ok(value_int) = string.parse::<u32>() {
                    if let Some(value_char) = char::from_u32(value_int) {
                        Entry::Char(value_char)
                    } else {
                        Entry::Unknown
                    }
                } else {
                    Entry::Unknown
                }
            }
            (Some(ModelEntry::LitInt(string)), _) => Entry::Int(string.clone()),
            (Some(ModelEntry::LitFloat(string)), _) => Entry::Float(string.clone()),
            (Some(ModelEntry::LitBool(bool)), _) => Entry::Bool(*bool),
            (Some(ModelEntry::DomainValue(domain_name, _)), Some(ty::TyKind::Ref(_, typ, _))) => {
                //this should never fail since a DomainValue can only exist if the corresponding domain exists
                let sil_domain = self
                    .silicon_counterexample
                    .domains
                    .entries
                    .get(domain_name)
                    .unwrap();
                let sil_fn_name = format!("destructor${domain_name}$$target_current");
                Entry::Ref(Box::new(self.extract_field_value(
                    &sil_fn_name,
                    Some(*typ),
                    model_entry,
                    sil_domain,
                    model,
                )))
            }
            (Some(ModelEntry::DomainValue(domain_name, _)), Some(ty::TyKind::Tuple(subst))) => {
                let sil_domain = self
                    .silicon_counterexample
                    .domains
                    .entries
                    .get(domain_name)
                    .unwrap();
                let len = subst.len();
                let mut fields = vec![];
                for i in 0..len {
                    let field_typ = subst[i];
                    let field_name = format!("tuple_{i}");
                    let sil_fn_name = format!("destructor${}$${}", domain_name, &field_name);
                    let field_entry = self.extract_field_value(
                        &sil_fn_name,
                        Some(field_typ),
                        model_entry,
                        sil_domain,
                        model,
                    );
                    fields.push(field_entry);
                }
                Entry::Tuple(fields)
            }
            (
                Some(ModelEntry::DomainValue(domain_name, ..)),
                Some(ty::TyKind::Adt(adt_def, subst)),
            ) if adt_def.is_box() => {
                //this should never fail since a DomainValue can only exist if the corresponding domain exists
                let sil_domain = self
                    .silicon_counterexample
                    .domains
                    .entries
                    .get(domain_name)
                    .unwrap();
                let sil_fn_name = format!("destructor${domain_name}$$val_ref");
                let new_typ = subst.type_at(0);
                Entry::Box(Box::new(self.extract_field_value(
                    &sil_fn_name,
                    Some(new_typ),
                    model_entry,
                    sil_domain,
                    model,
                )))
            }

            (
                Some(ModelEntry::DomainValue(domain_name, ..)),
                Some(ty::TyKind::Adt(adt_def, subst)),
            ) if adt_def.is_struct() => {
                if domain_name == "Snap$Unbounded" {
                    //FIXME check for correct type instead of name
                    let sil_domain = self
                        .silicon_counterexample
                        .domains
                        .entries
                        .get(domain_name)
                        .unwrap();
                    let sil_fn_name = format!("destructor${domain_name}$$value");
                    let variant = adt_def.variants().iter().next().unwrap();
                    let int_typ = Some(variant.fields[0usize.into()].ty(self.tcx, subst));
                    return self.extract_field_value(
                        &sil_fn_name,
                        int_typ,
                        model_entry,
                        sil_domain,
                        model,
                    );
                }
                let variant = adt_def.variants().iter().next().unwrap();
                let struct_name = variant.ident(self.tcx).name.to_ident_string();
                //check if a model should replace the original type in the counterexample
                if model {
                    if let Some((to_model, model_id)) = self
                        .encoder
                        .get_type_specs(adt_def.did())
                        .and_then(|p| p.model)
                    {
                        let entry =
                            self.extract_model(model_entry, domain_name, to_model, model_id);
                        return if let Entry::Struct {
                            field_entries,
                            custom_print_option,
                            ..
                        } = entry
                        {
                            Entry::Struct {
                                name: format!("{struct_name}_model"),
                                field_entries,
                                custom_print_option,
                            }
                        } else {
                            entry
                        };
                    }
                }
                let field_entries =
                    self.translate_snapshot_adt_fields(variant, model_entry, subst, model);
                let custom_print_option = self
                    .encoder
                    .get_type_specs(adt_def.did())
                    .and_then(|p| self.custom_print(p.counterexample_print, None));
                Entry::Struct {
                    name: struct_name,
                    field_entries,
                    custom_print_option,
                }
            }
            (
                Some(ModelEntry::DomainValue(domain_name, _)),
                Some(ty::TyKind::Adt(adt_def, subst)),
            ) if adt_def.is_union() => {
                let disc_function_name = format!("discriminant${domain_name}");
                //this should never fail since a DomainValue can only exist if the corresponding domain exists
                let sil_domain = self
                    .silicon_counterexample
                    .domains
                    .entries
                    .get(domain_name)
                    .unwrap();
                let sil_fn_param = vec![model_entry.cloned()];
                if let Some(disc_function) = sil_domain.functions.entries.get(&disc_function_name) {
                    if let Some(ModelEntry::LitInt(disc_value)) =
                        disc_function.get_function_value(&sil_fn_param)
                    {
                        let super_name = format!("{adt_def:?}");
                        let disc_value_int = disc_value.parse::<usize>().unwrap();
                        let variant = adt_def.variants().iter().next().unwrap();
                        let variant_name = variant.fields[disc_value_int.into()]
                            .ident(self.tcx)
                            .name
                            .to_ident_string();
                        let field_typ =
                            Some(variant.fields[disc_value_int.into()].ty(self.tcx, subst));

                        let destructor_sil_name =
                            format!("destructor${}${}$value", domain_name, &variant_name);

                        if let Some(value_function) =
                            sil_domain.functions.entries.get(&destructor_sil_name)
                        {
                            let new_model_entry = value_function.get_function_value(&sil_fn_param);
                            if let Some(ModelEntry::DomainValue(domain_name, _)) = new_model_entry {
                                let sil_domain = self
                                    .silicon_counterexample
                                    .domains
                                    .entries
                                    .get(domain_name)
                                    .unwrap();
                                let sil_fn_name = format!("destructor${domain_name}$$value");
                                let field_entry = self.extract_field_value(
                                    &sil_fn_name,
                                    field_typ,
                                    new_model_entry.as_ref(),
                                    sil_domain,
                                    model,
                                );
                                return Entry::Union {
                                    name: super_name,
                                    field_entry: (variant_name, Box::new(field_entry)),
                                };
                            }
                            return Entry::Union {
                                name: super_name,
                                field_entry: (variant_name, Box::new(Entry::Unknown)),
                            };
                        }
                    }
                }
                Entry::Union {
                    name: format!("{adt_def:?}"),
                    field_entry: ("?".to_string(), Box::new(Entry::Unknown)),
                }
            }
            (
                Some(ModelEntry::DomainValue(domain_name, _)),
                Some(ty::TyKind::Adt(adt_def, subst)),
            ) if adt_def.is_enum() => {
                let disc_function_name = format!("discriminant${domain_name}");
                let sil_domain = self
                    .silicon_counterexample
                    .domains
                    .entries
                    .get(domain_name)
                    .unwrap();
                let sil_fn_param = vec![model_entry.cloned()];
                if let Some(disc_function) = sil_domain.functions.entries.get(&disc_function_name) {
                    if let Some(ModelEntry::LitInt(disc_value)) =
                        disc_function.get_function_value(&sil_fn_param)
                    {
                        let super_name = format!("{adt_def:?}");
                        let disc_value_int = disc_value.parse::<u32>().unwrap();
                        if let Some(variant) = adt_def
                            .variants()
                            .iter()
                            .find(|x| get_discriminant_of_vardef(x) == Some(disc_value_int))
                        {
                            let variant_name = variant.ident(self.tcx).name.to_ident_string();
                            let destructor_sil_name =
                                format!("destructor${}${}$value", domain_name, &variant_name);
                            if let Some(value_function) =
                                sil_domain.functions.entries.get(&destructor_sil_name)
                            {
                                let domain_entry = value_function.get_function_value(&sil_fn_param);
                                let field_entries = self.translate_snapshot_adt_fields(
                                    variant,
                                    domain_entry.as_ref(),
                                    subst,
                                    model,
                                );
                                let custom_print_option =
                                    self.encoder.get_type_specs(adt_def.did()).and_then(|p| {
                                        self.custom_print(
                                            p.counterexample_print,
                                            Some(variant_name.clone()),
                                        )
                                    });
                                return Entry::Enum {
                                    super_name,
                                    name: variant_name,
                                    field_entries,
                                    custom_print_option,
                                };
                            }
                        }
                    }
                }
                Entry::Enum {
                    super_name: format!("{adt_def:?}"),
                    name: "?".to_string(),
                    field_entries: vec![],
                    custom_print_option: None,
                }
            }
            (Some(ModelEntry::Seq(_, model_entries)), Some(ty::TyKind::Adt(_, subst))) => {
                let typ = subst.type_at(0);
                let entries = model_entries
                    .iter()
                    .map(|entry| self.translate_snapshot_entry(Some(entry), Some(typ), model))
                    .collect();

                Entry::Seq(entries)
            }
            (Some(ModelEntry::Seq(_, model_entries)), Some(ty::TyKind::Array(typ, _))) => {
                let entries = model_entries
                    .iter()
                    .map(|entry| self.translate_snapshot_entry(Some(entry), Some(*typ), model))
                    .collect();

                Entry::Array(entries)
            }
            (Some(ModelEntry::DomainValue(domain_name, _)), _) => {
                //snapshot typ for primitive typ

                //this should never fail since a DomainValue can only exist if the corresponding domain exists
                let sil_domain = self
                    .silicon_counterexample
                    .domains
                    .entries
                    .get(domain_name)
                    .unwrap();
                let sil_fn_name = format!("destructor${domain_name}$$value");
                self.extract_field_value(&sil_fn_name, typ, model_entry, sil_domain, model)
            }
            _ => Entry::Unknown,
        }
    }

    fn translate_snapshot_adt_fields(
        &self,
        variant: &ty::VariantDef,
        model_entry: Option<&ModelEntry>,
        subst: ty::GenericArgsRef<'tcx>,
        model: bool, //if false, ignore models
    ) -> Vec<(String, Entry)> {
        match model_entry {
            Some(ModelEntry::DomainValue(domain_name, _)) => {
                //this should never fail since a DomainValue can only exist if the corresponding domain exists
                let sil_domain = self
                    .silicon_counterexample
                    .domains
                    .entries
                    .get(domain_name)
                    .unwrap();
                let mut fields = vec![];
                for f in &variant.fields {
                    let field_name = f.ident(self.tcx).name.to_ident_string();
                    let field_typ = f.ty(self.tcx, subst);
                    let sil_fn_name = format!("destructor${}$$f${}", domain_name, &field_name);
                    let field_entry = self.extract_field_value(
                        &sil_fn_name,
                        Some(field_typ),
                        model_entry,
                        sil_domain,
                        model,
                    );

                    fields.push((field_name, field_entry));
                }
                fields
            }
            _ => iter::zip(
                variant
                    .fields
                    .iter()
                    .map(|x| x.ident(self.tcx).name.to_ident_string()),
                iter::repeat(Entry::Unknown),
            )
            .collect(),
        }
    }

    fn extract_field_value(
        &self,
        sil_fn_name: &String,
        field_typ: Option<Ty<'tcx>>,
        model_entry: Option<&ModelEntry>,
        sil_domain: &DomainEntry,
        model: bool, //if false, ignore models
    ) -> Entry {
        let sil_fn_param = vec![model_entry.cloned()];
        let field_value = if let Some(function) = sil_domain.functions.entries.get(sil_fn_name) {
            function.get_function_value(&sil_fn_param)
        } else {
            &None
        };
        self.translate_snapshot_entry(field_value.as_ref(), field_typ, model)
    }

    fn extract_model(
        &self,
        model_entry: Option<&ModelEntry>,
        domain_name: &str,
        to_model: String,
        model_id: LocalDefId,
    ) -> Entry {
        let domain_name_wo_snap = domain_name.trim_start_matches("Snap");
        let ref_to_model_domain_name = format!("Snap$ref$Shared{domain_name_wo_snap}");
        let ref_to_model_function_name = format!("constructor${ref_to_model_domain_name}$no_alloc");
        if let Some(sil_domain) = self
            .silicon_counterexample
            .domains
            .entries
            .get(&ref_to_model_domain_name)
        {
            let sil_fn_param = vec![model_entry.cloned()];
            if let Some(ref_to_model_function) = sil_domain
                .functions
                .entries
                .get(&ref_to_model_function_name)
            {
                let sil_ref_domain = ref_to_model_function.get_function_value(&sil_fn_param);
                let sil_ref_fn_param = vec![sil_ref_domain.clone()];
                let sil_to_model_fn_name =
                    format!("caller_for$m_{to_model}$$model{domain_name_wo_snap}$");
                if let Some(sil_to_model_fn) = self
                    .silicon_counterexample
                    .functions
                    .entries
                    .get(&sil_to_model_fn_name)
                {
                    let sil_model = sil_to_model_fn.get_function_value(&sil_ref_fn_param);
                    let model_typ = self.tcx.type_of(model_id).instantiate_identity();
                    let entry =
                        self.translate_snapshot_entry(sil_model.as_ref(), Some(model_typ), false);
                    return entry;
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
