// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use ::log::{info, debug, trace};
use crate::encoder::borrows::{compute_procedure_contract, ProcedureContract, ProcedureContractMirDef};
use crate::encoder::builtin_encoder::BuiltinEncoder;
use crate::encoder::builtin_encoder::BuiltinFunctionKind;
use crate::encoder::builtin_encoder::BuiltinMethodKind;
use crate::encoder::errors::{ErrorCtxt, ErrorManager, SpannedEncodingError, EncodingError, WithSpan, RunIfErr};
use crate::encoder::foldunfold;
use crate::encoder::places;
use crate::encoder::procedure_encoder::ProcedureEncoder;
use crate::encoder::pure_function_encoder::PureFunctionEncoder;
use crate::encoder::stub_function_encoder::StubFunctionEncoder;
use crate::encoder::spec_encoder::encode_spec_assertion;
use crate::encoder::snapshot_encoder::{Snapshot, SnapshotEncoder};
use crate::encoder::type_encoder::{
    compute_discriminant_values, compute_discriminant_bounds, TypeEncoder};
use crate::encoder::SpecFunctionKind;
use crate::encoder::spec_function_encoder::SpecFunctionEncoder;
use prusti_common::vir;
use prusti_common::vir::WithIdentifier;
use prusti_common::config;
use prusti_common::report::log;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::Environment;
use prusti_interface::specs::typed;
use prusti_interface::specs::typed::SpecificationId;
use prusti_interface::utils::{has_spec_only_attr, read_prusti_attrs};
use prusti_interface::PrustiError;
use prusti_specs::specifications::common::SpecIdRef;
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
// use rustc::middle::const_val::ConstVal;
use rustc_middle::mir;
// use rustc::mir::interpret::GlobalId;
use rustc_middle::ty;
use std::cell::{RefCell, RefMut};
use std::collections::HashMap;
use std::io::Write;
use std::mem;
// use syntax::ast;
use rustc_ast::ast;
// use viper;
use crate::encoder::stub_procedure_encoder::StubProcedureEncoder;
use std::ops::AddAssign;
use std::convert::TryInto;
use std::borrow::Borrow;
use crate::encoder::specs_closures_collector::SpecsClosuresCollector;
use crate::encoder::memory_eq_encoder::MemoryEqEncoder;
use rustc_span::MultiSpan;
use crate::encoder::name_interner::NameInterner;
use crate::encoder::utils::transpose;
use crate::encoder::errors::EncodingResult;
use crate::encoder::errors::SpannedEncodingResult;

const SNAPSHOT_MIRROR_DOMAIN: &str = "$SnapshotMirrors$";

pub struct Encoder<'v, 'tcx: 'v> {
    env: &'v Environment<'tcx>,
    def_spec: &'v typed::DefSpecificationMap<'tcx>,
    error_manager: RefCell<ErrorManager<'tcx>>,
    procedure_contracts: RefCell<HashMap<
        ProcedureDefId,
        EncodingResult<ProcedureContractMirDef<'tcx>>
    >>,
    builtin_methods: RefCell<HashMap<BuiltinMethodKind, vir::BodylessMethod>>,
    builtin_functions: RefCell<HashMap<BuiltinFunctionKind, vir::Function>>,
    procedures: RefCell<HashMap<ProcedureDefId, vir::CfgMethod>>,
    pure_function_bodies: RefCell<HashMap<(ProcedureDefId, String), vir::Expr>>,
    pure_functions: RefCell<HashMap<(ProcedureDefId, String), vir::Function>>,
    /// Stub pure functions. Generated when an impure Rust function is invoked
    /// where a pure function is required.
    stub_pure_functions: RefCell<HashMap<(ProcedureDefId, String), vir::Function>>,
    spec_functions: RefCell<HashMap<ProcedureDefId, Vec<vir::Function>>>,
    type_predicate_names: RefCell<HashMap<ty::TyKind<'tcx>, String>>,
    type_invariant_names: RefCell<HashMap<ty::TyKind<'tcx>, String>>,
    type_tag_names: RefCell<HashMap<ty::TyKind<'tcx>, String>>,
    predicate_types: RefCell<HashMap<String, ty::Ty<'tcx>>>,
    type_predicates: RefCell<HashMap<String, vir::Predicate>>,
    type_invariants: RefCell<HashMap<String, vir::Function>>,
    type_tags: RefCell<HashMap<String, vir::Function>>,
    type_discriminant_funcs: RefCell<HashMap<String, vir::Function>>,
    type_cast_functions: RefCell<HashMap<(ty::Ty<'tcx>, ty::Ty<'tcx>), vir::Function>>,
    memory_eq_encoder: RefCell<MemoryEqEncoder>,
    fields: RefCell<HashMap<String, vir::Field>>,
    snapshots: RefCell<HashMap<String, Box<Snapshot>>>, // maps predicate names to snapshots
    type_snapshots: RefCell<HashMap<String, String>>, // maps snapshot names to predicate names
    snap_mirror_funcs: RefCell<HashMap<String, Option<vir::DomainFunc>>>,
    closures_collector: RefCell<SpecsClosuresCollector<'tcx>>,
    encoding_queue: RefCell<Vec<(ProcedureDefId, Vec<(ty::Ty<'tcx>, ty::Ty<'tcx>)>)>>,
    vir_program_before_foldunfold_writer: RefCell<Box<Write>>,
    vir_program_before_viper_writer: RefCell<Box<Write>>,
    pub typaram_repl: RefCell<Vec<HashMap<ty::Ty<'tcx>, ty::Ty<'tcx>>>>,
    encoding_errors_counter: RefCell<usize>,
    name_interner: RefCell<NameInterner>,
    axiomatized_function_domain: RefCell<vir::Domain>,
}

impl<'v, 'tcx> Encoder<'v, 'tcx> {
    pub fn new(
        env: &'v Environment<'tcx>,
        def_spec: &'v typed::DefSpecificationMap<'tcx>,
    ) -> Self {
        let source_path = env.source_path();
        let source_filename = source_path.file_name().unwrap().to_str().unwrap();
        let vir_program_before_foldunfold_writer = RefCell::new(
            log::build_writer(
                "vir_program_before_foldunfold",
                format!("{}.vir", source_filename),
            )
            .ok()
            .unwrap(),
        );
        let vir_program_before_viper_writer = RefCell::new(
            log::build_writer(
                "vir_program_before_viper",
                format!("{}.vir", source_filename),
            )
            .ok()
            .unwrap(),
        );

        let mut axiomatized_functions_domain = vir::Domain {
            name: "domainThatContainsTheAxiomatizedPureFunctions".to_owned(), //TODO
            functions: vec![],
            axioms: vec![],
            type_vars: vec![],
        };

        Encoder {
            env,
            def_spec,
            error_manager: RefCell::new(ErrorManager::new(env.codemap())),
            procedure_contracts: RefCell::new(HashMap::new()),
            builtin_methods: RefCell::new(HashMap::new()),
            builtin_functions: RefCell::new(HashMap::new()),
            procedures: RefCell::new(HashMap::new()),
            pure_function_bodies: RefCell::new(HashMap::new()),
            pure_functions: RefCell::new(HashMap::new()),
            stub_pure_functions: RefCell::new(HashMap::new()),
            spec_functions: RefCell::new(HashMap::new()),
            type_predicate_names: RefCell::new(HashMap::new()),
            type_invariant_names: RefCell::new(HashMap::new()),
            type_tag_names: RefCell::new(HashMap::new()),
            predicate_types: RefCell::new(HashMap::new()),
            type_predicates: RefCell::new(HashMap::new()),
            type_invariants: RefCell::new(HashMap::new()),
            type_tags: RefCell::new(HashMap::new()),
            type_discriminant_funcs: RefCell::new(HashMap::new()),
            type_cast_functions: RefCell::new(HashMap::new()),
            memory_eq_encoder: RefCell::new(MemoryEqEncoder::new()),
            fields: RefCell::new(HashMap::new()),
            closures_collector: RefCell::new(SpecsClosuresCollector::new()),
            encoding_queue: RefCell::new(vec![]),
            vir_program_before_foldunfold_writer,
            vir_program_before_viper_writer,
            typaram_repl: RefCell::new(Vec::new()),
            snapshots: RefCell::new(HashMap::new()),
            type_snapshots: RefCell::new(HashMap::new()),
            snap_mirror_funcs: RefCell::new(HashMap::new()),
            encoding_errors_counter: RefCell::new(0),
            name_interner: RefCell::new(NameInterner::new()),
            axiomatized_function_domain: RefCell::new(axiomatized_functions_domain),
        }
    }

    pub fn log_vir_program_before_foldunfold<S: ToString>(&self, program: S) {
        let mut writer = self.vir_program_before_foldunfold_writer.borrow_mut();
        writer
            .write_all(program.to_string().as_bytes())
            .ok()
            .unwrap();
        writer
            .write_all("\n\n".to_string().as_bytes())
            .ok()
            .unwrap();
        writer.flush().ok().unwrap();
    }

    pub fn log_vir_program_before_viper<S: ToString>(&self, program: S) {
        let mut writer = self.vir_program_before_viper_writer.borrow_mut();
        writer
            .write_all(program.to_string().as_bytes())
            .ok()
            .unwrap();
        writer
            .write_all("\n\n".to_string().as_bytes())
            .ok()
            .unwrap();
        writer.flush().ok().unwrap();
    }

    fn initialize(&mut self) {
        self.closures_collector.borrow_mut().collect_from_all_spec_items(self.env);
        // These are used in optimization passes
        self.encode_builtin_method_def(BuiltinMethodKind::HavocBool);
        self.encode_builtin_method_def(BuiltinMethodKind::HavocInt);
        self.encode_builtin_method_def(BuiltinMethodKind::HavocRef);
    }

    pub fn env(&self) -> &'v Environment<'tcx> {
        self.env
    }

    pub fn def_spec(&self) -> &'v typed::DefSpecificationMap<'tcx> {
        self.def_spec
    }

    pub fn error_manager(&self) -> RefMut<ErrorManager<'tcx>> {
        self.error_manager.borrow_mut()
    }

    pub fn get_viper_program(&self) -> vir::Program {
        vir::Program {
            domains: self.get_used_viper_domains(),
            fields: self.get_used_viper_fields(),
            builtin_methods: self.get_used_builtin_methods(),
            methods: self.get_used_viper_methods(),
            functions: self.get_used_viper_functions(),
            viper_predicates: self.get_used_viper_predicates(),
        }
    }

    pub(in crate::encoder) fn register_encoding_error(&self, encoding_error: SpannedEncodingError) {
        debug!("Encoding error: {:?}", encoding_error);
        let prusti_error: PrustiError = encoding_error.into();
        if prusti_error.is_error() {
            self.encoding_errors_counter.borrow_mut().add_assign(1);
        }
        prusti_error.emit(self.env);
    }

    pub fn count_encoding_errors(&self) -> usize {
        *self.encoding_errors_counter.borrow()
    }

    pub fn get_used_viper_domains(&self) -> Vec<vir::Domain> {
        let mirrors: Vec<_> = self
            .snap_mirror_funcs
            .borrow()
            .values()
            .filter_map(|f| f.clone())
            .collect();

        let mut domains: Vec<vir::Domain> = self
            .snapshots
            .borrow()
            .values()
            .into_iter()
            .filter_map(|s| s.domain())
            .collect();
        if !mirrors.is_empty() {
            domains.push(vir::Domain {
                name: SNAPSHOT_MIRROR_DOMAIN.to_string(),
                functions: mirrors,
                axioms: vec![],
                type_vars: vec![],
            });
        }

        if config::enable_purification_optimization() {
            domains.push(self.axiomatized_function_domain.borrow().clone());
            domains.push(self.get_nat_domain());
        }

        domains.sort_by_key(|d| d.get_identifier());
        domains
    }

    fn get_nat_domain(&self) -> vir::Domain {
        let nat_domain_name = "Nat";
        let zero = vir::DomainFunc {
            name: "zero".to_owned(),
            formal_args: vec![],
            return_type: vir::Type::Domain(nat_domain_name.to_owned()),
            unique: false,
            domain_name: nat_domain_name.to_owned(),
        };
        let succ = vir::DomainFunc {
            name: "succ".to_owned(),
            formal_args: vec![vir::LocalVar {
                name: "val".to_owned(),
                typ: vir::Type::Domain(nat_domain_name.to_owned()),
            }],
            return_type: vir::Type::Domain(nat_domain_name.to_owned()),
            unique: false,
            domain_name: nat_domain_name.to_owned(),
        };
        let functions = vec![zero, succ];

        vir::Domain {
            name: nat_domain_name.to_owned(),
            functions,
            axioms: vec![],
            type_vars: vec![],
        }
    }

    fn encode_axiomatized_pure_function(&self, f: &vir::Function) {
        let snapshots_info: HashMap<String, Box<Snapshot>> = self.snapshots.borrow().clone();
        let domain_name = self.axiomatized_function_domain.borrow().name.clone();

       

        let formal_args_without_nat: Vec<vir::LocalVar> = f
            .formal_args
            .iter()
            .map(|e| {
                let old_type = e.typ.clone();
                let new_type = snapshot::transalte_type(old_type, &snapshots_info);

                vir::LocalVar {
                    name: e.name.clone(),
                    typ: new_type,
                }
            })
            .collect();

        let mut formal_args = formal_args_without_nat.clone();
        formal_args.push(vir::LocalVar {
            name: "count".to_string(),
            typ: vir::Type::Domain("Nat".to_owned()),
        });

        let return_type = f.return_type.clone();
        let name = format!("domainVersionOf{}", f.name);

        let df = vir::DomainFunc {
            name,
            formal_args: formal_args.clone(),
            return_type,
            unique: false,
            domain_name: domain_name.to_string(),
        };

        let args: Vec<vir::Expr> = formal_args
        .clone()
        .into_iter()
        .map(vir::Expr::local)
        .collect();
        let function_call = vir::Expr::domain_func_app(df.clone(), args);

        let mut purifier = snapshot::ExprPurifier {
            snapshots: snapshots_info.clone(),
            self_function: function_call.clone()
        };



        let pre_conds: vir::Expr = f.pres
            .iter()
            .cloned()
            .map(|p| vir::ExprFolder::fold(&mut purifier, p))
            .fold(true.into(),  vir::Expr::and);
        let post_conds: vir::Expr = f.posts
            .iter()
            .cloned()
            .enumerate()
            .filter_map(|(i,p)|  {
                if i == f.posts.len() -1 {
                    // Skip the last post condition as it is only there to clarify the relation between the result of this function and snapshots
                    None
                }
                else {
                 Some(vir::ExprFolder::fold(&mut purifier, p))
                }
            })
            .fold(true.into(),  vir::Expr::and);

        let function_body = vir::ExprFolder::fold(&mut purifier, f.body.clone().unwrap());


        let function_identiry = vir::Expr::eq_cmp(function_call, function_body);

        let rhs: vir::Expr = vir::Expr::and(post_conds, function_identiry);

        let valids_anded : vir::Expr = formal_args_without_nat
            .into_iter()
            .map(|e| {
                let var_domain_name : String = match e.typ.clone() {
                    vir::Type::Domain(name) => name,
                    vir::Type::Bool => "Bool".to_string(),
                    vir::Type::Int => "Int".to_string(),
                    vir::Type::TypedRef(_) => unreachable!()
                };
                let valid_function = snapshot::encode_valid_function(var_domain_name);

                let self_arg = vir::Expr::local(e.clone());
                vir::Expr::domain_func_app(valid_function, vec![self_arg])

            })
            .fold(true.into(),  vir::Expr::and);
        

        let pre_conds_and_valid = vir::Expr::and(pre_conds, valids_anded );
        let axiom_body = vir::Expr::implies(pre_conds_and_valid, rhs);
        let triggers = vec![]; //TODO
        let da = vir::DomainAxiom {
            name: format!("axioms_for_{}", f.name), //TODO
            expr: vir::Expr::forall(formal_args, triggers, axiom_body),
            domain_name: domain_name.to_string(),
        };

        self.axiomatized_function_domain
            .borrow_mut()
            .functions
            .push(df);
        self.axiomatized_function_domain
            .borrow_mut()
            .axioms
            .push(da);
    }

    fn get_used_viper_fields(&self) -> Vec<vir::Field> {
        let mut fields: Vec<_> = self.fields.borrow().values().cloned().collect();
        fields.sort_by_key(|f| f.get_identifier());
        fields
    }

    fn get_used_viper_functions(&self) -> Vec<vir::Function> {
        let mut functions: Vec<_> = vec![];
        for function in self.builtin_functions.borrow().values() {
            functions.push(function.clone());
        }
        for function in self.pure_functions.borrow().values() {
            functions.push(function.clone());
        }
        for function in self.stub_pure_functions.borrow().values() {
            functions.push(function.clone());
        }
        for function in self.type_invariants.borrow().values() {
            functions.push(function.clone());
        }
        for function in self.type_tags.borrow().values() {
            functions.push(function.clone());
        }
        for function in self.type_discriminant_funcs.borrow().values() {
            functions.push(function.clone());
        }
        for function in self.type_cast_functions.borrow().values() {
            functions.push(function.clone());
        }
        functions.extend(
            self.memory_eq_encoder.borrow().get_encoded_functions()
        );
        for snap in self.snapshots.borrow().values() {
            for function in snap.functions() {
                functions.push(function);
            }
        }
        for sfs in self.spec_functions.borrow().values() {
            for sf in sfs {
                functions.push(sf.clone());
            }
        }
        functions.sort_by_key(|f| f.get_identifier());
        functions
    }

    fn get_used_viper_predicates(&self) -> Vec<vir::Predicate> {
        let mut predicates: Vec<_> = self.type_predicates.borrow().values().cloned().collect();

        // Add a predicate that represents the dead loan token.
        predicates.push(vir::Predicate::Bodyless(
            "DeadBorrowToken$".to_string(),
            vir::LocalVar {
                name: "borrow".to_string(),
                typ: vir::Type::Int,
            },
        ));

        predicates.sort_by_key(|f| f.get_identifier());
        predicates
    }

    pub fn get_used_viper_predicates_map(&self) -> HashMap<String, vir::Predicate> {
        self.type_predicates.borrow().clone()
    }

    fn get_used_builtin_methods(&self) -> Vec<vir::BodylessMethod> {
        self.builtin_methods.borrow().values().cloned().collect()
    }

    fn get_used_viper_methods(&self) -> Vec<vir::CfgMethod> {
        self.procedures.borrow().values().cloned().collect()
    }

    pub fn get_single_closure_instantiation(
        &self,
        closure_def_id: DefId,
    ) -> Option<(
        ProcedureDefId,
        mir::Location,
        Vec<mir::Operand<'tcx>>,
        Vec<ty::Ty<'tcx>>,
    )> {
        self.closures_collector.borrow().get_single_instantiation(closure_def_id)
    }

    /// Is the closure specified with the `def_id` is spec only?
    pub fn is_spec_closure(&self, def_id: DefId) -> bool {
        use rustc_ast::ast;
        has_spec_only_attr(self.env().tcx().get_attrs(def_id))
    }

    /// Get the loop invariant attached to a function with a
    /// `prusti::loop_body_invariant_spec` attribute.
    pub fn get_loop_specs(&self, def_id: DefId) -> Option<typed::LoopSpecification<'tcx>> {
        let spec = self.def_spec.get(&def_id)?;
        Some(spec.expect_loop().clone())
    }

    /// Get the specifications attached to the `def_id` function.
    pub fn get_procedure_specs(&self, def_id: DefId) -> Option<typed::ProcedureSpecification<'tcx>> {
        let spec = self.def_spec.get(&def_id)?;
        Some(spec.expect_procedure().clone())
    }

    /// Get a local wrapper `DefId` for functions that have external specs.
    /// Return the original `DefId` for everything else.
    fn get_wrapper_def_id(&self, def_id: DefId) -> DefId {
        self.def_spec.extern_specs.get(&def_id)
            .map(|local_id| local_id.to_def_id())
            .unwrap_or(def_id)
    }

    fn get_procedure_contract(&self, proc_def_id: ProcedureDefId)
        -> EncodingResult<ProcedureContractMirDef<'tcx>>
    {
        let spec = typed::SpecificationSet::Procedure(
            self.get_procedure_specs(proc_def_id)
                .unwrap_or_else(|| typed::ProcedureSpecification::empty())
        );
        compute_procedure_contract(proc_def_id, self.env().tcx(), spec, None)
    }

    pub fn get_procedure_contract_for_def(
        &self,
        proc_def_id: ProcedureDefId,
    ) -> EncodingResult<ProcedureContract<'tcx>> {
        self.procedure_contracts
            .borrow_mut()
            .entry(proc_def_id)
            .or_insert_with(|| self.get_procedure_contract(proc_def_id)).as_ref()
            .map(|contract| contract.to_def_site_contract())
            .map_err(|err| err.clone())
    }

    pub fn get_procedure_contract_for_call(
        &self,
        self_ty: Option<&'tcx ty::TyS<'tcx>>,
        proc_def_id: ProcedureDefId,
        args: &Vec<places::Local>,
        target: places::Local,
    ) -> EncodingResult<ProcedureContract<'tcx>> {
        // get specification on trait declaration method or inherent impl
        let trait_spec = self.get_procedure_specs(proc_def_id)
            .unwrap_or_else(|| {
                debug!("Procedure {:?} has no specification", proc_def_id);
                typed::ProcedureSpecification::empty()
            });

        let tymap = self.typaram_repl.borrow();

        if tymap.len() != 1 {
            return Err(EncodingError::internal(
                format!("tymap.len() = {}, but should be 1", tymap.len())
            ));
        }

        // get receiver object base type
        let mut impl_spec = typed::ProcedureSpecification::empty();

        // let mut self_ty = None;

        // for (key, val) in tymap[0].iter() {
        //     if key.is_self() {   // FIXME: This check does not work anymore.
        //         self_ty = Some(val.clone());
        //     }
        // }

        if let Some(ty) = self_ty {
            if let Some(id) = self.env().tcx().trait_of_item(proc_def_id) {
                let proc_name = self.env().tcx().item_name(proc_def_id);
                let procs = self.env().get_trait_method_decl_for_type(ty, id, proc_name);
                if procs.len() == 1 {
                    // FIXME(@jakob): if several methods are found, we currently don't know which
                    // one to pick.
                    let item = procs[0];
                    if let Some(spec) = self.get_procedure_specs(item.def_id) {
                        impl_spec = spec;
                    } else {
                        debug!("Procedure {:?} has no specification", item.def_id);
                    }
                }
            }
        }

        // merge specifications
        let final_spec = trait_spec.refine(&impl_spec);

        let contract = compute_procedure_contract(
            proc_def_id,
            self.env().tcx(),
            typed::SpecificationSet::Procedure(final_spec),
            Some(&tymap[0])
        )?;
        Ok(contract.to_call_site_contract(args, target))
    }

    /// Encodes a value in a field if the base expression is a reference or
    /// a primitive types.
    /// For composed data structures, the base expression is returned.
    pub fn encode_value_expr(&self, base: vir::Expr, ty: ty::Ty<'tcx>) -> vir::Expr {
        match ty.kind() {
            ty::TyKind::Adt(_, _)
            | ty::TyKind::Tuple(_) => {
                base // don't use a field for tuples and ADTs
            }
            _ => {
                let value_field = self.encode_value_field(ty);
                base.field(value_field)
            }
        }
    }

    pub fn encode_value_field(&self, ty: ty::Ty<'tcx>) -> vir::Field {
        let type_encoder = TypeEncoder::new(self, ty);
        let field = type_encoder.encode_value_field()
            .expect("failed to encode unsupported type");
        self.fields
            .borrow_mut()
            .entry(field.name.clone())
            .or_insert_with(|| field.clone());
        field
    }

    pub fn encode_raw_ref_field(
        &self,
        viper_field_name: String,
        ty: ty::Ty<'tcx>
    ) -> EncodingResult<vir::Field> {
        let type_name = self.encode_type_predicate_use(ty)?;
        self.fields
            .borrow_mut()
            .entry(viper_field_name.clone())
            .or_insert_with(|| {
                // Do not store the name of the type in self.fields
                vir::Field::new(
                    viper_field_name.clone(),
                    vir::Type::TypedRef("".to_string()),
                )
            });
        Ok(vir::Field::new(viper_field_name, vir::Type::TypedRef(type_name)))
    }

    pub fn encode_dereference_field(&self, ty: ty::Ty<'tcx>)
        -> EncodingResult<vir::Field>
    {
        self.encode_raw_ref_field("val_ref".to_string(), ty)
    }

    pub fn encode_struct_field(&self, field_name: &str, ty: ty::Ty<'tcx>)
        -> EncodingResult<vir::Field>
    {
        let viper_field_name = format!("f${}", field_name);
        self.encode_raw_ref_field(viper_field_name, ty)
    }

    /// Creates a field that corresponds to the enum variant ``index``.
    pub fn encode_enum_variant_field(&self, index: &str) {
        let name = format!("enum_{}", index);
        let mut fields = self.fields.borrow_mut();
        if !fields.contains_key(&name) {
            let field = vir::Field::new(name.clone(), vir::Type::TypedRef("".to_string()));
            fields.insert(name, field);
        }
    }

    pub fn encode_discriminant_field(&self) -> vir::Field {
        let name = "discriminant";
        let field = vir::Field::new(name, vir::Type::Int);
        self.fields
            .borrow_mut()
            .entry(name.to_string())
            .or_insert_with(|| field.clone());
        field
    }

    pub fn encode_discriminant_func_app(
        &self,
        place: vir::Expr,
        adt_def: &'tcx ty::AdtDef,
    ) -> vir::Expr {
        let typ = place.get_type().clone();
        let mut name = typ.name();
        name.push_str("$$discriminant$$");
        let self_local_var = vir::LocalVar::new("self", typ);
        self.type_discriminant_funcs
            .borrow_mut()
            .entry(name.clone())
            .or_insert_with(|| {
                let predicate_name = place.get_type().name();
                let precondition = vir::Expr::predicate_access_predicate(
                    predicate_name,
                    self_local_var.clone().into(),
                    vir::PermAmount::Read,
                );
                let result = vir::LocalVar::new("__result", vir::Type::Int);
                let postcondition = compute_discriminant_bounds(
                    adt_def, self.env.tcx(), &result.into());
                let discr_field = self.encode_discriminant_field();
                let self_local_var_expr: vir::Expr = self_local_var.clone().into();
                let function = vir::Function {
                    name: name.clone(),
                    formal_args: vec![self_local_var.clone()],
                    return_type: vir::Type::Int,
                    pres: vec![precondition],
                    posts: vec![postcondition],
                    body: Some(self_local_var_expr.field(discr_field)),
                };
                let final_function = foldunfold::add_folding_unfolding_to_function(
                    function,
                    self.get_used_viper_predicates_map(),
                );
                final_function.unwrap()
            });
        vir::Expr::FuncApp(
            name,
            vec![place],
            vec![self_local_var],
            vir::Type::Int,
            vir::Position::default(),
        )
    }

    pub fn encode_memory_eq_func_app(
        &self,
        first: vir::Expr,
        second: vir::Expr,
        self_ty: ty::Ty<'tcx>,
        position: vir::Position,
        span: MultiSpan,
    ) -> vir::Expr {
        let encoding_result = self.memory_eq_encoder
            .borrow_mut()
            .encode_memory_eq_func_app(
                self,
                first,
                second,
                self_ty,
                position,
            ).with_span(span);
        match encoding_result {
            Ok(expr) => expr,
            Err(err) => {
                self.register_encoding_error(err);
                // Stub encoding of the memory eq function application
                true.into()
            }
        }
    }

    pub fn encode_builtin_method_def(&self, method_kind: BuiltinMethodKind) -> vir::BodylessMethod {
        trace!("encode_builtin_method_def({:?})", method_kind);
        if !self.builtin_methods.borrow().contains_key(&method_kind) {
            let builtin_encoder = BuiltinEncoder::new();
            let method = builtin_encoder.encode_builtin_method_def(method_kind);
            self.log_vir_program_before_viper(method.to_string());
            self.builtin_methods
                .borrow_mut()
                .insert(method_kind.clone(), method);
        }
        self.builtin_methods.borrow()[&method_kind].clone()
    }

    pub fn encode_builtin_method_use(&self, method_kind: BuiltinMethodKind) -> String {
        trace!("encode_builtin_method_use({:?})", method_kind);
        // Trigger encoding of definition
        self.encode_builtin_method_def(method_kind);
        let builtin_encoder = BuiltinEncoder::new();
        builtin_encoder.encode_builtin_method_name(method_kind)
    }

    pub fn encode_builtin_function_def(&self, function_kind: BuiltinFunctionKind) {
        trace!("encode_builtin_function_def({:?})", function_kind);
        if !self.builtin_functions.borrow().contains_key(&function_kind) {
            let builtin_encoder = BuiltinEncoder::new();
            let function = builtin_encoder.encode_builtin_function_def(function_kind.clone());
            self.log_vir_program_before_viper(function.to_string());
            self.builtin_functions
                .borrow_mut()
                .insert(function_kind.clone(), function);
        }
    }

    pub fn encode_builtin_function_use(&self, function_kind: BuiltinFunctionKind) -> String {
        trace!("encode_builtin_function_use({:?})", function_kind);
        if !self.builtin_functions.borrow().contains_key(&function_kind) {
            // Trigger encoding of definition
            self.encode_builtin_function_def(function_kind.clone());
        }
        let builtin_encoder = BuiltinEncoder::new();
        builtin_encoder.encode_builtin_function_name(&function_kind)
    }

    pub fn encode_cast_function_use(&self, src_ty: ty::Ty<'tcx>, dst_ty: ty::Ty<'tcx>)
        -> EncodingResult<String>
    {
        trace!("encode_cast_function_use(src_ty={:?}, dst_ty={:?})", src_ty, dst_ty);
        let function_name = format!("builtin$cast${}${}", src_ty, dst_ty);
        if !self.type_cast_functions.borrow().contains_key(&(src_ty, dst_ty)) {
            let arg = vir::LocalVar::new(
                String::from("number"),
                self.encode_value_type(src_ty)?,
            );
            let result = vir::LocalVar::new("__result", self.encode_value_type(dst_ty)?);
            let mut precondition = self.encode_type_bounds(&arg.clone().into(), src_ty);
            precondition.extend(self.encode_type_bounds(&arg.clone().into(), dst_ty));
            let postcondition = self.encode_type_bounds(&result.into(), dst_ty);
            let function = vir::Function {
                name: function_name.clone(),
                formal_args: vec![arg.clone()],
                return_type: self.encode_value_type(dst_ty)?,
                pres: precondition,
                posts: postcondition,
                body: Some(arg.into()),
            };
            self.type_cast_functions.borrow_mut().insert((src_ty, dst_ty), function);
        }
        Ok(function_name)
    }

    pub fn encode_procedure(&self, def_id: ProcedureDefId) -> SpannedEncodingResult<vir::CfgMethod> {
        debug!("encode_procedure({:?})", def_id);
        assert!(
            !self.is_pure(def_id),
            "procedure is marked as pure: {:?}",
            def_id
        );
        assert!(
            !self.is_trusted(def_id),
            "procedure is marked as trusted: {:?}",
            def_id
        );
        if !self.procedures.borrow().contains_key(&def_id) {
            self.closures_collector.borrow_mut().collect(self.env, def_id.expect_local());
            let procedure = self.env.get_procedure(def_id);
            let proc_encoder = ProcedureEncoder::new(self, &procedure)?;
            let method = match proc_encoder.encode() {
                Ok(result) => result,
                Err(error) => {
                    self.register_encoding_error(error);
                    StubProcedureEncoder::new(self, &procedure).encode()
                },
            };
            self.log_vir_program_before_viper(method.to_string());
            self.procedures.borrow_mut().insert(def_id, method);
        }

        // TODO: specification functions are currently only encoded for closures
        // but we want them (on demand) for all functions when they are passed
        // as a function pointer; likewise we want them for function *signatures*,
        // when Fn* values are passed dynamically in boxes.
        // This is not the correct place to trigger the encoding, it should be
        // moved to where the spec function is used. `encode_spec_funcs` already
        // ensures that spec functions for a particular `DefId` are encoded only
        // once.
        if self.env.tcx().is_closure(def_id) {
            self.encode_spec_funcs(def_id)?;
        }

        Ok(self.procedures.borrow()[&def_id].clone())
    }

    pub fn encode_value_or_ref_type(&self, ty: ty::Ty<'tcx>)
        -> EncodingResult<vir::Type>
    {
        let type_encoder = TypeEncoder::new(self, ty);
        type_encoder.encode_value_or_ref_type()
    }

    /// Encodes the specification functions for the function/closure def_id.
    pub fn encode_spec_funcs(&self, def_id: ProcedureDefId)
        -> SpannedEncodingResult<Vec<vir::Function>>
    {
        if !self.spec_functions.borrow().contains_key(&def_id) {
            let procedure = self.env.get_procedure(def_id);
            let spec_func_encoder = SpecFunctionEncoder::new(self, &procedure);
            let result = spec_func_encoder.encode()?;
            self.spec_functions.borrow_mut().insert(def_id, result);
        }
        Ok(self.spec_functions.borrow()[&def_id].clone())
    }

    pub fn encode_value_type(&self, ty: ty::Ty<'tcx>)
        -> EncodingResult<vir::Type>
    {
        let type_encoder = TypeEncoder::new(self, ty);
        type_encoder.encode_value_type()
    }

    pub fn encode_type(&self, ty: ty::Ty<'tcx>)
        -> EncodingResult<vir::Type>
    {
        let type_encoder = TypeEncoder::new(self, ty);
        type_encoder.encode_type()
    }

    pub fn encode_type_bounds(&self, var: &vir::Expr, ty: ty::Ty<'tcx>) -> Vec<vir::Expr> {
        let type_encoder = TypeEncoder::new(self, ty);
        type_encoder.encode_bounds(var)
    }

    pub fn encode_assertion(
        &self,
        assertion: &typed::Assertion<'tcx>,
        mir: &mir::Body<'tcx>,
        pre_label: Option<&str>,
        target_args: &[vir::Expr],
        target_return: Option<&vir::Expr>,
        targets_are_values: bool,
        assertion_location: Option<mir::BasicBlock>,
        error: ErrorCtxt,
    ) -> SpannedEncodingResult<vir::Expr> {
        trace!("encode_assertion {:?}", assertion);
        let encoded_assertion = encode_spec_assertion(
            self,
            assertion,
            pre_label,
            target_args,
            target_return,
            targets_are_values,
            assertion_location,
        )?;
        Ok(encoded_assertion.set_default_pos(
            self.error_manager()
                .register(typed::Spanned::get_spans(assertion, mir, self.env().tcx()), error),
        ))
    }

    pub fn encode_type_predicate_use(&self, ty: ty::Ty<'tcx>)
        -> EncodingResult<String>
    {
        if !self.type_predicate_names.borrow().contains_key(ty.kind()) {
            let type_encoder = TypeEncoder::new(self, ty);
            let name = type_encoder.encode_predicate_use()?;
            self.type_predicate_names
                .borrow_mut()
                .insert(ty.kind().clone(), name.clone());
            self.predicate_types
                .borrow_mut()
                .insert(name, ty);
            // Trigger encoding of definition
            self.encode_type_predicate_def(ty)?;
        }
        let predicate_name = self.type_predicate_names.borrow()[&ty.kind()].clone();
        Ok(predicate_name)
    }

    pub fn encode_type_predicate_def(&self, ty: ty::Ty<'tcx>)
        -> EncodingResult<vir::Predicate>
    {
        let predicate_name = self.encode_type_predicate_use(ty).unwrap();
        if !self.type_predicates.borrow().contains_key(&predicate_name) {
            let type_encoder = TypeEncoder::new(self, ty);
            let predicates = type_encoder.encode_predicate_def()?;
            for predicate in predicates {
                self.log_vir_program_before_viper(predicate.to_string());
                let predicate_name = predicate.name();
                self.type_predicates
                    .borrow_mut()
                    .insert(predicate_name.to_string(), predicate);
            }
        }
        Ok(self.type_predicates.borrow()[&predicate_name].clone())
    }

    pub fn encode_snapshot(&self, ty: ty::Ty<'tcx>)
        -> EncodingResult<Box<Snapshot>>
    {
        let ty = self.dereference_ty(ty);
        let predicate_name = self.encode_type_predicate_use(ty)
            .expect("failed to encode unsupported type");
        if !self.snapshots.borrow().contains_key(&predicate_name) {
            let encoder = SnapshotEncoder::new(
                self, ty,
                predicate_name.to_string()
            );
            let snapshot = encoder.encode()?;
            self.type_snapshots
                .borrow_mut()
                .insert(
                    snapshot.get_type().name().to_string(),
                    predicate_name.to_string()
                );
            self.snapshots
                .borrow_mut()
                .insert(predicate_name.to_string(), box snapshot);
        }
        Ok(self.snapshots.borrow()[&predicate_name].clone())
    }

    fn dereference_ty(&self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        match ty.kind() {
            ty::TyKind::Ref(_, ref val_ty, _) => self.dereference_ty(val_ty),
            _ => ty,
        }
    }

    /// Checks whether the given type implements structural equality
    /// by either being a primitive type or by deriving the Eq trait.
    pub fn has_structural_eq_impl(&self, ty: ty::Ty<'tcx>) -> bool {
        let ty = self.dereference_ty(ty);
        match ty.kind() {
            ty::TyKind::Bool
            | ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Char
            | ty::TyKind::Tuple(_)
            | ty::TyKind::Never
            | ty::TyKind::Param(_) => true,
            ty::TyKind::Adt(_, _) => {
                self.env().tcx().has_structural_eq_impls(ty)
            }
            _ => false,
        }
    }

    pub fn encode_snapshot_use(&self, predicate_name: String)
        -> EncodingResult<Box<Snapshot>>
    {
        if !self.snapshots.borrow().contains_key(&predicate_name) {
            if !self.predicate_types.borrow().contains_key(&predicate_name) {
                unreachable!(); // some type has not been encoded before.
            }
            let ty = self.predicate_types.borrow()[&predicate_name];
            return self.encode_snapshot(&ty);
        }
        Ok(self.snapshots.borrow()[&predicate_name].clone())
    }

    pub fn get_snapshot(&self, snapshot_name: String) -> Box<Snapshot> {
        // fails if we have not encoded a snapshot with that name before
        // should be safe as we should never construct a snapshot name outside
        // of the snapshot encoder.
        let predicate_name = self.type_snapshots.borrow()[&snapshot_name].to_string();
        self.snapshots.borrow()[&predicate_name].clone()
    }

    pub fn encode_type_invariant_use(&self, ty: ty::Ty<'tcx>)
        -> EncodingResult<String>
    {
        // TODO we could use type_predicate_names instead (see TypeEncoder::encode_invariant_use)
        if !self.type_invariant_names.borrow().contains_key(ty.kind()) {
            let type_encoder = TypeEncoder::new(self, ty);
            let invariant_name = type_encoder.encode_invariant_use()
                .expect("failed to encode unsupported type");
            self.type_invariant_names
                .borrow_mut()
                .insert(ty.kind().clone(), invariant_name);
            // Trigger encoding of definition
            self.encode_type_invariant_def(ty)?;
        }
        let invariant_name = self.type_invariant_names.borrow()[&ty.kind()].clone();
        Ok(invariant_name)
    }

    pub fn encode_type_invariant_def(&self, ty: ty::Ty<'tcx>)
        -> EncodingResult<vir::Function>
    {
        let invariant_name = self.encode_type_invariant_use(ty)?;
        if !self.type_invariants.borrow().contains_key(&invariant_name) {
            let type_encoder = TypeEncoder::new(self, ty);
            let invariant = type_encoder.encode_invariant_def()?;
            self.type_invariants
                .borrow_mut()
                .insert(invariant_name.clone(), invariant);
        }
        Ok(self.type_invariants.borrow()[&invariant_name].clone())
    }

    pub fn encode_type_tag_use(&self, ty: ty::Ty<'tcx>) -> String {
        if !self.type_tag_names.borrow().contains_key(&ty.kind()) {
            let type_encoder = TypeEncoder::new(self, ty);
            let tag_name = type_encoder.encode_tag_use()
                .expect("failed to encode unsupported type");
            self.type_tag_names
                .borrow_mut()
                .insert(ty.kind().clone(), tag_name);
            // Trigger encoding of definition
            self.encode_type_tag_def(ty);
        }
        let tag_name = self.type_tag_names.borrow()[&ty.kind()].clone();
        tag_name
    }

    pub fn encode_type_tag_def(&self, ty: ty::Ty<'tcx>) -> vir::Function {
        let tag_name = self.encode_type_tag_use(ty);
        if !self.type_tags.borrow().contains_key(&tag_name) {
            let type_encoder = TypeEncoder::new(self, ty);
            let tag = type_encoder.encode_tag_def();
            self.type_tags.borrow_mut().insert(tag_name.clone(), tag);
        }
        self.type_tags.borrow()[&tag_name].clone()
    }

    pub fn encode_const_expr(
        &self,
        ty: &ty::TyS<'tcx>,
        value: &ty::ConstKind<'tcx>
    ) -> EncodingResult<vir::Expr> {
        trace!("encode_const_expr {:?}", value);
        let opt_scalar_value = match value {
            ty::ConstKind::Value(ref const_value) => {
                const_value
                    .try_to_scalar()
            }
            ty::ConstKind::Unevaluated(def, substs, promoted) => {
                let tcx = self.env().tcx();
                let param_env = tcx.param_env(def.did);
                tcx.const_eval_resolve(param_env, *def, substs, *promoted, None)
                    .ok()
                    .and_then(|const_value| const_value.try_to_scalar())
            }
            _ => unimplemented!("{:?}", value),
        };

        let scalar_value = if let Some(v) = opt_scalar_value {
            v
        } else {
            return Err(EncodingError::unsupported(
                format!("unsupported constant value: {:?}", value)
            ));
        };

        let expr = match ty.kind() {
            ty::TyKind::Bool => scalar_value.to_bool().unwrap().into(),
            ty::TyKind::Char => scalar_value.to_char().unwrap().into(),
            ty::TyKind::Int(ast::IntTy::I8) => scalar_value.to_i8().unwrap().into(),
            ty::TyKind::Int(ast::IntTy::I16) => scalar_value.to_i16().unwrap().into(),
            ty::TyKind::Int(ast::IntTy::I32) => scalar_value.to_i32().unwrap().into(),
            ty::TyKind::Int(ast::IntTy::I64) => scalar_value.to_i64().unwrap().into(),
            ty::TyKind::Int(ast::IntTy::I128) => scalar_value.to_i128().unwrap().into(),
            ty::TyKind::Int(ast::IntTy::Isize) => scalar_value.to_machine_isize(&self.env().tcx()).unwrap().into(),
            ty::TyKind::Uint(ast::UintTy::U8) => scalar_value.to_u8().unwrap().into(),
            ty::TyKind::Uint(ast::UintTy::U16) => scalar_value.to_u16().unwrap().into(),
            ty::TyKind::Uint(ast::UintTy::U32) => scalar_value.to_u32().unwrap().into(),
            ty::TyKind::Uint(ast::UintTy::U64) => scalar_value.to_u64().unwrap().into(),
            ty::TyKind::Uint(ast::UintTy::U128) => scalar_value.to_u128().unwrap().into(),
            ty::TyKind::Uint(ast::UintTy::Usize) => scalar_value.to_machine_usize(&self.env().tcx()).unwrap().into(),
            ty::TyKind::FnDef(def_id, _) => {
                self.encode_spec_funcs(*def_id)?;
                vir::Expr::Const(vir::Const::FnPtr, vir::Position::default())
            }
            ref x => unimplemented!("{:?}", x),
        };
        debug!("encode_const_expr {:?} --> {:?}", value, expr);
        Ok(expr)
    }

    pub fn encode_int_cast(&self, value: u128, ty: ty::Ty<'tcx>) -> vir::Expr {
        trace!("encode_int_cast {:?} as {:?}", value, ty);

        let expr = match ty.kind() {
            ty::TyKind::Bool => (value != 0).into(),
            ty::TyKind::Int(ast::IntTy::I8) => (value as i8).into(),
            ty::TyKind::Int(ast::IntTy::I16) => (value as i16).into(),
            ty::TyKind::Int(ast::IntTy::I32) => (value as i32).into(),
            ty::TyKind::Int(ast::IntTy::I64) => (value as i64).into(),
            ty::TyKind::Int(ast::IntTy::I128) => (value as i128).into(),
            ty::TyKind::Int(ast::IntTy::Isize) => (value as isize).into(),
            ty::TyKind::Uint(ast::UintTy::U8) => (value as u8).into(),
            ty::TyKind::Uint(ast::UintTy::U16) => (value as u16).into(),
            ty::TyKind::Uint(ast::UintTy::U32) => (value as u32).into(),
            ty::TyKind::Uint(ast::UintTy::U64) => (value as u64).into(),
            ty::TyKind::Uint(ast::UintTy::U128) => (value as u128).into(),
            ty::TyKind::Uint(ast::UintTy::Usize) => (value as usize).into(),
            ty::TyKind::Char => value.into(),
            ref x => unimplemented!("{:?}", x),
        };
        debug!("encode_int_cast {:?} as {:?} --> {:?}", value, ty, expr);
        expr
    }

    pub fn encode_item_name(&self, def_id: DefId) -> String {
        let full_name = format!("m_{}", encode_identifier(self.env.get_item_def_path(def_id)));
        let short_name = format!("m_{}", encode_identifier(
            self.env.tcx().opt_item_name(def_id)
                .map(|s| s.name.to_ident_string())
                .unwrap_or(self.env.get_item_name(def_id))
        ));
        self.intern_viper_identifier(full_name, short_name)
    }

    pub fn encode_invariant_func_app(
        &self,
        ty: ty::Ty<'tcx>,
        encoded_arg: vir::Expr
    ) -> EncodingResult<vir::Expr> {
        let type_pred = self.encode_type_predicate_use(ty)
            .expect("failed to encode unsupported type");
        Ok(vir::Expr::FuncApp(
            self.encode_type_invariant_use(ty)?,
            vec![encoded_arg],
            // TODO ?
            vec![vir::LocalVar::new("self", vir::Type::TypedRef(type_pred))],
            vir::Type::Bool,
            // TODO
            vir::Position::default(),
        ))
    }

    pub fn encode_tag_func_app(&self, ty: ty::Ty<'tcx>) -> vir::Expr {
        vir::Expr::FuncApp(
            self.encode_type_tag_use(ty),
            vec![],
            // TODO ?
            vec![],
            vir::Type::Int,
            // TODO
            vir::Position::default(),
        )
    }

    /// Encode either a pure function body or a specification assertion (stored in the given MIR).
    pub fn encode_pure_function_body(&self, proc_def_id: ProcedureDefId)
        -> SpannedEncodingResult<vir::Expr>
    {
        let mir_span = self.env.tcx().def_span(proc_def_id);
        let substs_key = self.type_substitution_key().with_span(mir_span)?;
        let key = (proc_def_id, substs_key);
        if !self.pure_function_bodies.borrow().contains_key(&key) {
            let procedure = self.env.get_procedure(proc_def_id);
            let pure_function_encoder = PureFunctionEncoder::new(
                self,
                proc_def_id,
                procedure.get_mir(),
                true,
            );
            let body = pure_function_encoder.encode_body()?;
            self.pure_function_bodies
                .borrow_mut()
                .insert(key.clone(), body);
        }
        Ok(self.pure_function_bodies.borrow()[&key].clone())
    }

    pub fn encode_pure_function_def(
        &self,
        proc_def_id: ProcedureDefId,
        substs: Vec<(ty::Ty<'tcx>, ty::Ty<'tcx>)>,
    ) -> SpannedEncodingResult<()> {
        trace!("[enter] encode_pure_function_def({:?})", proc_def_id);
        assert!(
            self.is_pure(proc_def_id),
            "procedure is not marked as pure: {:?}",
            proc_def_id
        );

        {
            // FIXME: this is a hack to support generics. See issue #187.
            let mut tymap_stack = self.typaram_repl.borrow_mut();
            assert!(tymap_stack.is_empty());
            let mut tymap = HashMap::new();
            for (typ, subst) in substs {
                tymap.insert(typ, subst);
            }
            tymap_stack.push(tymap);
        }
        let cleanup = || {
            // FIXME: this is a hack to support generics. See issue #187.
            let mut tymap_stack = self.typaram_repl.borrow_mut();
            tymap_stack.pop();
        };

        // FIXME: Using substitutions as a key is most likely wrong.
        let mir_span = self.env.tcx().def_span(proc_def_id);
        let substs_key = self.type_substitution_key().with_span(mir_span).run_if_err(cleanup)?;
        let key = (proc_def_id, substs_key);

        if !self.pure_functions.borrow().contains_key(&key) {
            trace!("not encoded: {:?}", key);
            let wrapper_def_id = self.get_wrapper_def_id(proc_def_id);
            let procedure = self.env.get_procedure(wrapper_def_id);
            let pure_function_encoder =
                PureFunctionEncoder::new(self, proc_def_id, procedure.get_mir(), false);
            let function = if self.is_trusted(proc_def_id) {
                pure_function_encoder.encode_bodyless_function()
                    .run_if_err(cleanup)?
            } else {
                let pure_function = pure_function_encoder.encode_function()
                    .run_if_err(cleanup)?;
                self.patch_pure_post_with_mirror_call(pure_function)
                    .with_span(procedure.get_span())
                    .run_if_err(cleanup)?
            };

            if config::enable_purification_optimization() {
                self.encode_axiomatized_pure_function(&function);
            }

            self.log_vir_program_before_viper(function.to_string());
            self.pure_functions.borrow_mut().insert(key, function);
        }

        trace!("[exit] encode_pure_function_def({:?})", proc_def_id);
        cleanup();
        Ok(())
    }

    fn patch_pure_post_with_mirror_call(&self, function: vir::Function)
        -> EncodingResult<vir::Function>
    {
        // use function identifier to be more robust in the presence of generics
        let mirror = self.encode_pure_snapshot_mirror(
            function.get_identifier().to_string(),
            &function.formal_args,
            &function.return_type,
        )?;
        if mirror.is_none() {
            return Ok(function);
        }
        let mirror = mirror.unwrap();

        let mut mirror_args = vec![];
        for func_arg in &function.formal_args {
            let arg = vir::Expr::Local(func_arg.clone(), vir::Position::default());
            match &func_arg.typ {
                vir::Type::TypedRef(name) => {
                    mirror_args.push(
                        self.encode_snapshot_use(name.to_string())?
                            .snap_call(arg),
                    );
                }
                _ => mirror_args.push(arg),
            }
        }

        let mut posts = function.posts.clone();
        posts.push(vir::Expr::InhaleExhale(
            box vir::Expr::BinOp(
                vir::BinOpKind::EqCmp,
                box vir::Expr::Local(
                    vir::LocalVar::new("__result", function.return_type.clone()),
                    vir::Position::default(),
                ),
                box vir::Expr::DomainFuncApp(
                    mirror.clone(),
                    mirror_args,
                    vir::Position::default(),
                ),
                    /* TODO
                    vir::Expr::DomainFuncApp(
                        mirror.name,
                        mirror_args,
                        mirror.formal_args,
                        mirror.return_type,
                        mirror.domain_name,
                        vir::Position::default(),
                    )
                     */
                vir::Position::default(),
            ),
            box vir::Expr::Const(vir::Const::Bool(true), vir::Position::default()),
            vir::Position::default()
        ));
        Ok(vir::Function { posts, ..function })
    }

    pub fn encode_pure_snapshot_mirror(
        &self,
        pure_func_name: String,
        pure_formal_args: &Vec<vir::LocalVar>,
        pure_return_type: &vir::Type
    ) -> EncodingResult<Option<vir::DomainFunc>> {
        if !self.snap_mirror_funcs
            .borrow()
            .contains_key(&pure_func_name)
        {
            if !pure_formal_args.iter().map(
                |a| match &a.typ {
                    vir::Type::TypedRef(name) => {
                        self.encode_snapshot_use(name.to_string()).map(
                            |snap| snap.supports_equality()
                        )
                    }
                    _ => Ok(true),
                }
            ).collect::<Result<Vec<_>, _>>()?.iter().all(|x| *x) {
                self.snap_mirror_funcs
                    .borrow_mut()
                    .insert(pure_func_name.to_string(), None);
            } else {
                let formal_args = pure_formal_args
                    .iter()
                    .map(|a| {
                       match &a.typ {
                            vir::Type::TypedRef(name) => {
                                self.encode_snapshot_use(name.to_string()).map(
                                    |snap| snap.get_type()
                                )
                            }
                            t => Ok(t.clone()),
                       }.map(
                           |t|  vir::LocalVar::new(a.name.to_string(), t)
                       )
                    })
                    .collect::<Result<_, _>>()?;

                let mirror_function = vir::DomainFunc {
                    name: format!("mirror${}", pure_func_name.to_string()),
                    formal_args,
                    return_type: pure_return_type.clone(),
                    unique: false,
                    domain_name: SNAPSHOT_MIRROR_DOMAIN.to_string(),
                };
                self.snap_mirror_funcs
                    .borrow_mut()
                    .insert(pure_func_name.to_string(), Some(mirror_function));
            }
        }
        Ok(self.snap_mirror_funcs.borrow()[&pure_func_name].clone())
    }

    pub fn get_item_name(&self, proc_def_id: ProcedureDefId) -> String {
        self.env.get_item_name(proc_def_id)
    }

    /// Encode the use (call) of a pure function, returning the name of the
    /// function and its type.
    ///
    /// The called function must be marked as pure. It should be local unless
    /// there is an external specification defined.
    pub fn encode_pure_function_use(
        &self,
        proc_def_id: ProcedureDefId,
    ) -> SpannedEncodingResult<(String, vir::Type)> {
        let wrapper_def_id = self.get_wrapper_def_id(proc_def_id);
        let procedure = self.env.get_procedure(wrapper_def_id);

        assert!(
            self.is_pure(proc_def_id),
            "procedure is not marked as pure: {:?}",
            proc_def_id
        );

        let pure_function_encoder =
            PureFunctionEncoder::new(self, proc_def_id, procedure.get_mir(), false);

        self.queue_pure_function_encoding(proc_def_id);

        Ok((
            pure_function_encoder.encode_function_name(),
            pure_function_encoder.encode_function_return_type()?,
        ))
    }

    /// Encode the use (call) of either a comparison (equality or disequality)
    /// returning the name of the encoded function and its type.
    /// If the comparison is not supported, a stub function will be encoded
    pub fn encode_cmp_pure_function_use(
        &self,
        proc_def_id: ProcedureDefId,
        arg_ty: ty::Ty<'tcx>, // type arguments
        is_equality: bool // true = equality, false = disequality
    ) -> SpannedEncodingResult<(String, vir::Type)> {
        let snapshot_res = self.encode_snapshot(&arg_ty);
        if snapshot_res.is_ok() && snapshot_res.as_ref().unwrap().supports_equality() {
            let snapshot = snapshot_res.unwrap();
            Ok((
                if is_equality {
                    snapshot.equals_func_name()
                } else {
                    snapshot.not_equals_func_name()
                },
                vir::Type::Bool
            ))
        } else {
            // TODO: Use the error message from `encode_snapshot`.
            self.encode_stub_pure_function_use(proc_def_id)
        }
    }

    /// Encode the use (call) of a stub pure function, returning the name of the
    /// function and its type.
    ///
    /// The stub function is a bodyless function with `false` precondition. It's meant to be used
    /// when the user tries to call an impure function in a context that requires a pure function.
    pub fn encode_stub_pure_function_use(
        &self,
        proc_def_id: ProcedureDefId,
    ) -> SpannedEncodingResult<(String, vir::Type)> {
        // The stub function may come from an external module.
        let body = self.env.external_mir(proc_def_id);
        let stub_encoder = StubFunctionEncoder::new(self, proc_def_id, &body);

        let substs_key = self.type_substitution_key().with_span(body.span)?;
        let key = (proc_def_id, substs_key);

        // If we haven't seen this particular stub before, generate and insert it.
        if !self.pure_functions.borrow().contains_key(&key) {
            let function = stub_encoder.encode_function()?;

            self.log_vir_program_before_viper(function.to_string());

            self.stub_pure_functions.borrow_mut().insert(key, function);
        }
        Ok((
            stub_encoder.encode_function_name(),
            stub_encoder.encode_function_return_type()?,
        ))
    }

    pub fn queue_procedure_encoding(&self, proc_def_id: ProcedureDefId) {
        self.encoding_queue
            .borrow_mut()
            .push((proc_def_id, Vec::new()));
    }

    pub fn queue_pure_function_encoding(&self, proc_def_id: ProcedureDefId) {
        let substs = self.current_tymap().into_iter().collect();
        self.encoding_queue.borrow_mut().push((proc_def_id, substs));
    }

    pub fn process_encoding_queue(&mut self) {
        self.initialize();
        while !self.encoding_queue.borrow().is_empty() {
            let (proc_def_id, substs) = self.encoding_queue.borrow_mut().pop().unwrap();
            let proc_name = self.env.get_absolute_item_name(proc_def_id);
            let proc_def_path = self.env.get_item_def_path(proc_def_id);
            let wrapper_def_id = self.get_wrapper_def_id(proc_def_id);
            let proc_span = self.env.get_item_span(wrapper_def_id);
            info!(
                "Encoding: {} from {:?} ({})",
                proc_name, proc_span, proc_def_path
            );
            let is_pure_function = self.is_pure(proc_def_id);
            if is_pure_function {
                self.encode_pure_function_def(proc_def_id, substs);
            } else {
                assert!(substs.is_empty());
                if self.is_trusted(proc_def_id) {
                    debug!(
                        "Trusted procedure will not be encoded or verified: {:?}",
                        proc_def_id
                    );
                } else {
                    if let Err(error) = self.encode_procedure(proc_def_id) {
                        self.register_encoding_error(error);
                        debug!("Error encoding function: {:?}", proc_def_id);
                    }
                }
            }
        }
    }

    pub fn is_trusted(&self, def_id: ProcedureDefId) -> bool {
        let result = self.def_spec.get(&def_id).map_or(false, |spec| spec.expect_procedure().trusted);
        trace!("is_trusted {:?} = {}", def_id, result);
        result
    }

    pub fn is_pure(&self, def_id: ProcedureDefId) -> bool {
        let result = self.def_spec.get(&def_id).map_or(false, |spec| spec.expect_procedure().pure);
        trace!("is_pure {:?} = {}", def_id, result);
        result
    }

    pub fn has_extern_spec(&self, def_id: ProcedureDefId) -> bool {
        // FIXME: eventually, procedure specs (the entries in def_spec) should
        // have an `is_extern_spec` field. For now, due to the way we handle
        // MIR, extern specs create a wrapper function with a different DefId,
        // so since we already have this remapping, it is enough to check if
        // there is a wrapper present for the given external DefId.
        let result = self.def_spec.extern_specs.contains_key(&def_id);
        trace!("has_extern_spec {:?} = {}", def_id, result);
        result
    }

    /// Convert a potential type parameter to a concrete type.
    pub fn resolve_typaram(&self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        // TODO: creating each time a current_tymap might be slow. This can be optimized.
        if let Some(replaced_ty) = self.current_tymap().get(&ty) {
            trace!("resolve_typaram({:?}) ==> {:?}", ty, replaced_ty);
            return replaced_ty
        }
        ty
    }

    /// Merges the stack of type maps into a single map.
    pub fn current_tymap(&self) -> HashMap<ty::Ty<'tcx>, ty::Ty<'tcx>> {
        let mut map = HashMap::new();
        for map_frame in self.typaram_repl.borrow().iter().rev() {
            for (typ, subst) in map_frame {
                map.insert(typ.clone(), subst.clone());
                let additional_substs: Vec<_> = map
                    .iter()
                    .filter(|(_typ1, typ2)| typ2 == &typ)
                    .map(|(typ1, typ2)| (typ1.clone(), typ2.clone()))
                    .collect();
                for (typ, subst) in additional_substs {
                    map.insert(typ, subst);
                }
            }
        }
        map
    }

    /// TODO: This is a hack, it generates strings that can be used to instantiate generic pure
    /// functions.
    pub fn type_substitution_strings(&self)
        -> EncodingResult<HashMap<String, String>>
    {
        self.current_tymap()
            .iter()
            .map(|(typ, subst)| {
                let encoded_typ = self.encode_type(typ).map(|t| match t {
                    vir::Type::TypedRef(s) => s.clone(),
                    x => unreachable!("{:?}", x),
                });
                let encoded_subst = self.encode_type(subst).map(|s| match s {
                    vir::Type::TypedRef(s) => s.clone(),
                    x => unreachable!("{:?}", x),
                });
                transpose((encoded_typ, encoded_subst))
            })
            .collect::<Result<_, _>>()
    }

    /// TODO: This is a hack, it generates a String that can be used for uniquely identifying this
    /// type substitution.
    pub fn type_substitution_key(&self) -> EncodingResult<String> {
        let mut substs: Vec<_> = self
            .type_substitution_strings()?
            .into_iter()
            .filter(|(typ, subst)| typ != subst)
            .map(|(typ, subst)| format!("({},{})", typ, subst))
            .collect();
        substs.sort();
        Ok(substs.join(";"))
    }

    pub fn encode_spec_func_name(&self, def_id: ProcedureDefId, kind: SpecFunctionKind) -> String {
        let kind_name = match kind {
            SpecFunctionKind::Pre => "pre",
            SpecFunctionKind::Post => "post",
            SpecFunctionKind::HistInv => "histinv",
        };
        let full_name = format!(
            "sf_{}_{}",
            kind_name,
            encode_identifier(self.env.get_item_def_path(def_id))
        );
        let short_name = format!(
            "sf_{}_{}",
            kind_name,
            encode_identifier(
                self.env.tcx().opt_item_name(def_id)
                    .map(|s| s.name.to_ident_string())
                    .unwrap_or(self.env.get_item_name(def_id))
            )
        );
        self.intern_viper_identifier(full_name, short_name)
    }

    pub fn intern_viper_identifier<S: AsRef<str>>(&self, full_name: S, short_name: S) -> String {
        let result = if config::disable_name_mangling() {
            short_name.as_ref().to_string()
        } else {
            if config::intern_names() {
                self.name_interner.borrow_mut().intern(full_name, &[short_name])
            } else {
                full_name.as_ref().to_string()
            }
        };
        result
    }
}

fn encode_identifier(ident: String) -> String {
    // Rule: the rhs must always have an even number of "$"
    ident
        .replace("::", "$$")
        .replace("#", "$sharp$")
        .replace("<", "$openang$")
        .replace(">", "$closeang$")
        .replace("(", "$openrou$")
        .replace(")", "$closerou$")
        .replace("[", "$opensqu$")
        .replace("]", "$closesqu$")
        .replace("{", "$opencur$")
        .replace("}", "$closecur$")
        .replace(",", "$comma$")
        .replace(";", "$semic$")
        .replace(" ", "$space$")
}

