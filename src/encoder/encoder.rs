// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::{Domain, Function};
use rustc::hir::def_id::DefId;
use rustc::ty;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::EnvironmentImpl;
use prusti_interface::environment::Environment;
use std::collections::HashMap;
use rustc::middle::const_val::ConstVal;
use encoder::places;
use encoder::borrows::{ProcedureContractMirDef, ProcedureContract, compute_procedure_contract};
use encoder::procedure_encoder::ProcedureEncoder;
use encoder::type_encoder::TypeEncoder;
use std::cell::RefCell;
use encoder::vir;
use report::Log;

pub struct Encoder<'v, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    env: &'v EnvironmentImpl<'r, 'a, 'tcx>,
    procedure_contracts: RefCell<HashMap<ProcedureDefId, ProcedureContractMirDef<'tcx>>>,
    procedures: RefCell<HashMap<ProcedureDefId, vir::CfgMethod>>,
    type_predicate_names: RefCell<HashMap<ty::TypeVariants<'tcx>, String>>,
    predicate_types: RefCell<HashMap<String, ty::Ty<'tcx>>>,
    type_predicates: RefCell<HashMap<String, vir::Predicate>>,
    fields: RefCell<HashMap<String, vir::Field>>,
}

impl<'v, 'r, 'a, 'tcx> Encoder<'v, 'r, 'a, 'tcx> {
    pub fn new(env: &'v EnvironmentImpl<'r, 'a, 'tcx>) -> Self {
        Encoder {
            env,
            procedure_contracts: RefCell::new(HashMap::new()),
            procedures: RefCell::new(HashMap::new()),
            type_predicate_names: RefCell::new(HashMap::new()),
            predicate_types: RefCell::new(HashMap::new()),
            type_predicates: RefCell::new(HashMap::new()),
            fields: RefCell::new(HashMap::new()),
        }
    }

    pub fn env(&self) -> &'v EnvironmentImpl<'r, 'a, 'tcx> {
        self.env
    }

    pub fn get_used_viper_domains(&self) -> Vec<Domain<'v>> {
        // TODO
        vec![]
    }

    pub fn get_used_viper_fields(&self) -> Vec<vir::Field> {
        self.fields.borrow().values().cloned().collect()
    }

    pub fn get_used_viper_functions(&self) -> Vec<Function<'v>> {
        // TODO
        vec![]
    }

    pub fn get_used_viper_predicates(&self) -> Vec<vir::Predicate> {
        self.type_predicates.borrow().values().cloned().collect()
    }

    pub fn get_used_viper_predicates_map(&self) -> HashMap<String, vir::Predicate> {
        self.type_predicates.borrow().clone()
    }

    pub fn get_used_viper_methods(&self) -> Vec<vir::CfgMethod> {
        self.procedures.borrow().values().cloned().collect()
    }

    pub fn get_procedure_contract_for_def(&self, proc_def_id: ProcedureDefId
                                          ) -> ProcedureContract<'tcx> {
        let mut map = self.procedure_contracts.borrow_mut();
        map.entry(proc_def_id).or_insert_with(|| {
            compute_procedure_contract(proc_def_id, self.env().tcx())
        }).to_def_site_contract()
    }

    pub fn get_procedure_contract_for_call(&self, proc_def_id: ProcedureDefId,
                                           args: &Vec<places::Local>, target: places::Local
                                           ) -> ProcedureContract<'tcx> {
        let mut map = self.procedure_contracts.borrow_mut();
        map.entry(proc_def_id).or_insert_with(|| {
            compute_procedure_contract(proc_def_id, self.env().tcx())
        }).to_call_site_contract(args, target)
    }

    pub fn encode_value_field_name(&self, ty: ty::Ty<'tcx>) -> String {
        let type_encoder = TypeEncoder::new(self, ty);
        let field_name = type_encoder.encode_value_field_name();
        // Trigger encoding of definition
        self.encode_value_field_with_name(&field_name, ty);
        field_name
    }

    pub fn encode_value_field(&self, ty: ty::Ty<'tcx>) -> vir::Field {
        let field_name = self.encode_value_field_name(ty);
        self.encode_value_field_with_name(&field_name, ty)
    }

    fn encode_value_field_with_name(&self, field_name: &str, ty: ty::Ty<'tcx>) -> vir::Field {
        self.fields.borrow_mut().entry(field_name.to_string()).or_insert_with(|| {
            let type_encoder = TypeEncoder::new(self, ty);
            type_encoder.encode_value_field()
        }).clone()
    }

    pub fn encode_ref_field(&self, field_name: &str, ty: ty::Ty<'tcx>) -> vir::Field {
        let type_name = self.encode_type_predicate_use(ty);
        self.fields.borrow_mut().entry(field_name.to_string()).or_insert_with(|| {
            vir::Field::new(field_name, vir::Type::TypedRef(type_name))
        }).clone()
    }

    pub fn encode_discriminant_field(&self) -> vir::Field {
        let name = "discriminant";
        let field = self.fields.borrow_mut().entry(name.to_string()).or_insert_with(|| {
            vir::Field::new(name, vir::Type::Int)
        }).clone();
        field
    }

    pub fn encode_procedure(&self, proc_def_id: ProcedureDefId) -> vir::CfgMethod {
        if !self.procedures.borrow().contains_key(&proc_def_id) {
            let procedure = self.env.get_procedure(proc_def_id);
            let procedure_encoder = ProcedureEncoder::new(self, &procedure);
            let method = procedure_encoder.encode();
            Log::report("vir_method", method.name(), method.to_string());
            self.procedures.borrow_mut().insert(proc_def_id, method);
        }
        self.procedures.borrow()[&proc_def_id].clone()
    }

    pub fn encode_type_fields(&self, ty: ty::Ty<'tcx>) -> Vec<vir::Field> {
        let type_encoder = TypeEncoder::new(self, ty);
        let fields = type_encoder.encode_fields();
        for field in &fields {
            self.fields.borrow_mut().entry(field.name.to_string()).or_insert(field.clone());
        }
        fields
    }

    pub fn encode_type_predicate_use(&self, ty: ty::Ty<'tcx>) -> String {
        if !self.type_predicate_names.borrow().contains_key(&ty.sty) {
            let type_encoder = TypeEncoder::new(self, ty);
            let result = type_encoder.encode_predicate_use();
            self.type_predicate_names.borrow_mut().insert(ty.sty.clone(), result);
            // Trigger encoding of definition
            self.encode_type_predicate_def(ty);
        }
        let predicate_name = self.type_predicate_names.borrow()[&ty.sty].clone();
        self.predicate_types.borrow_mut().insert(predicate_name.clone(), ty);
        predicate_name
    }

    pub fn get_predicate_type(&self, predicate_name: String) -> Option<ty::Ty<'tcx>> {
        self.predicate_types.borrow().get(&predicate_name).cloned()
    }

    pub fn encode_type_predicate_def(&self, ty: ty::Ty<'tcx>) -> vir::Predicate {
        let predicate_name = self.encode_type_predicate_use(ty);
        if !self.type_predicates.borrow().contains_key(&predicate_name) {
            let type_encoder = TypeEncoder::new(self, ty);
            let predicate = type_encoder.encode_predicate_def();
            Log::report("vir_predicate", &predicate_name, format!("{}", &predicate));
            self.type_predicates.borrow_mut().insert(predicate_name.clone(), predicate);
        }
        self.type_predicates.borrow()[&predicate_name].clone()
    }

    pub fn eval_const_val(&self, const_val: &ConstVal<'tcx>, as_bool: bool) -> vir::Expr {
        match const_val {
            ConstVal::Value(ref const_value) => {
                if as_bool {
                    vir::Expr::eq_cmp(
                        const_value.to_primval().unwrap().to_bool().ok().unwrap().into(),
                        true.into()
                    )
                } else {
                    const_value.to_primval().unwrap().to_i64().ok().unwrap().into()
                }
            },
            _ => unimplemented!()
        }
    }

    pub fn encode_type_name(&self, def_id: DefId) -> String {
        self.env.get_item_name(def_id).replace("::", "$")
    }

    pub fn encode_procedure_name(&self, proc_def_id: ProcedureDefId) -> String {
        self.env.get_item_name(proc_def_id).replace("::", "$")
    }
}
