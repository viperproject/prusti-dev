// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::{self, Viper, Expr, VerificationError};
use viper::{Domain, Field, Function, Predicate, Method};
use viper::AstFactory;
use rustc::mir;
use rustc::hir::def_id::DefId;
use rustc::ty;
use prusti_interface::environment::Procedure;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::EnvironmentImpl;
use prusti_interface::environment::BasicBlockIndex;
use prusti_interface::environment::Environment;
use std::collections::HashMap;
use std::collections::HashSet;
use viper::CfgBlockIndex;
use rustc::mir::TerminatorKind;
use syntax::ast;
use viper::Successor;
use rustc::middle::const_val::{ConstInt, ConstVal};
use encoder::borrows::{ProcedureContractMirDef, ProcedureContract, compute_procedure_contract};
use encoder::procedure_encoder::ProcedureEncoder;
use encoder::type_encoder::TypeEncoder;
use std::cell::RefCell;
use encoder::utils::*;

pub struct Encoder<'v, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    ast_factory: viper::AstFactory<'v>,
    cfg_factory: viper::CfgFactory<'v>,
    env: &'v EnvironmentImpl<'r, 'a, 'tcx>,
    procedure_contracts: RefCell<HashMap<ProcedureDefId, ProcedureContractMirDef<'tcx>>>,
    procedures: RefCell<HashMap<ProcedureDefId, Method<'v>>>,
    type_predicate_names: RefCell<HashMap<ty::TypeVariants<'tcx>, String>>,
    type_predicates: RefCell<HashMap<String, Predicate<'v>>>,
    fields: RefCell<HashMap<String, Field<'v>>>,
}

impl<'v, 'r, 'a, 'tcx> Encoder<'v, 'r, 'a, 'tcx> {
    pub fn new(ast_factory: viper::AstFactory<'v>,
               cfg_factory: viper::CfgFactory<'v>,
               env: &'v EnvironmentImpl<'r, 'a, 'tcx>) -> Self {
        Encoder {
            ast_factory,
            cfg_factory,
            env,
            procedure_contracts: RefCell::new(HashMap::new()),
            procedures: RefCell::new(HashMap::new()),
            type_predicate_names: RefCell::new(HashMap::new()),
            type_predicates: RefCell::new(HashMap::new()),
            fields: RefCell::new(HashMap::new()),
        }
    }

    pub fn ast_factory(&self) -> &viper::AstFactory<'v> {
        &self.ast_factory
    }

    pub fn cfg_factory(&self) -> &viper::CfgFactory<'v> {
        &self.cfg_factory
    }

    pub fn env(&self) -> &'v EnvironmentImpl<'r, 'a, 'tcx> {
        self.env
    }

    pub fn get_used_viper_domains(&self) -> Vec<Domain<'v>> {
        // TODO
        vec![]
    }

    pub fn get_used_viper_fields(&self) -> Vec<Field<'v>> {
        self.fields.borrow().values().cloned().collect()
    }

    pub fn get_used_viper_functions(&self) -> Vec<Function<'v>> {
        // TODO
        vec![]
    }

    pub fn get_used_viper_predicates(&self) -> Vec<Predicate<'v>> {
        self.type_predicates.borrow().values().cloned().collect()
    }

    pub fn get_used_viper_methods(&self) -> Vec<Method<'v>> {
        self.procedures.borrow().values().cloned().collect()
    }

    pub fn get_procedure_contract_for_def(&self, proc_def_id: ProcedureDefId
                                          ) -> ProcedureContract<'tcx> {
        let mut map = self.procedure_contracts.borrow_mut();
        map.entry(proc_def_id).or_insert_with(|| {
            compute_procedure_contract(proc_def_id, self.env().tcx())
        }).to_def_site_contract()
    }

    pub fn encode_value_field_name(&self, ty: ty::Ty<'tcx>) -> String {
        let mut type_encoder = TypeEncoder::new(self, ty);
        let field_name = type_encoder.encode_value_field_name();
        // Trigger encoding of definition
        self.encode_value_field_with_name(&field_name, ty);
        field_name
    }

    pub fn encode_value_field(&self, ty: ty::Ty<'tcx>) -> Field<'v> {
        let field_name = self.encode_value_field_name(ty);
        self.encode_value_field_with_name(&field_name, ty)
    }

    fn encode_value_field_with_name(&self, field_name: &str, ty: ty::Ty<'tcx>) -> Field<'v> {
        *self.fields.borrow_mut().entry(field_name.to_string()).or_insert_with(|| {
            let mut type_encoder = TypeEncoder::new(self, ty);
            type_encoder.encode_value_field()
        })
    }

    pub fn encode_ref_field(&self, field_name: &str) -> Field<'v> {
        *self.fields.borrow_mut().entry(field_name.to_string()).or_insert_with(|| {
            self.ast_factory.field(field_name, self.ast_factory.ref_type())
        })
    }

    pub fn encode_discriminant_field(&self) -> (String, Field<'v>) {
        let name = "discriminant";
        let field = *self.fields.borrow_mut().entry(name.to_string()).or_insert_with(|| {
            self.ast_factory.field(name, self.ast_factory.int_type())
        });
        (name.to_string(), field)
    }

    pub fn encode_procedure(&self, proc_def_id: ProcedureDefId) -> Method<'v> {
        if !self.procedures.borrow().contains_key(&proc_def_id) {
            let procedure = self.env.get_procedure(proc_def_id);
            let mut procedure_encoder = ProcedureEncoder::new(self, &procedure);
            let result = procedure_encoder.encode();
            self.procedures.borrow_mut().insert(proc_def_id, result);
        }
        self.procedures.borrow()[&proc_def_id].clone()
    }

    pub fn encode_type_fields(&self, ty: ty::Ty<'tcx>) -> Vec<(String, Field<'v>, Option<ty::Ty<'tcx>>)> {
        let mut type_encoder = TypeEncoder::new(self, ty);
        let fields = type_encoder.encode_fields();
        for &(ref field_name, field, opt_field_ty) in &fields {
            self.fields.borrow_mut().entry(field_name.to_string()).or_insert(field);
        }
        fields
    }

    pub fn encode_type_predicate_use(&self, ty: ty::Ty<'tcx>) -> String {
        if !self.type_predicate_names.borrow().contains_key(&ty.sty) {
            let mut type_encoder = TypeEncoder::new(self, ty);
            let result = type_encoder.encode_predicate_use();
            self.type_predicate_names.borrow_mut().insert(ty.sty.clone(), result);
            // Trigger encoding of definition
            self.encode_type_predicate_def(ty);
        }
        self.type_predicate_names.borrow()[&ty.sty].clone()
    }

    pub fn encode_type_predicate_def(&self, ty: ty::Ty<'tcx>) -> Predicate<'v> {
        let predicate_name = self.encode_type_predicate_use(ty);
        if !self.type_predicates.borrow().contains_key(&predicate_name) {
            let mut type_encoder = TypeEncoder::new(self, ty);
            let result = type_encoder.encode_predicate_def();
            self.type_predicates.borrow_mut().insert(predicate_name.clone(), result);
        }
        self.type_predicates.borrow()[&predicate_name].clone()
    }

    pub fn eval_const_int(&self, const_int: &ConstInt) -> Expr<'v> {
        match const_int {
            &ConstInt::U32(ref val) => self.ast_factory.int_lit_from_ref(val),
            &ConstInt::I32(ref val) => self.ast_factory.int_lit_from_ref(val),
            &ConstInt::U8(ref val) => self.ast_factory.int_lit_from_ref(val),
            &ConstInt::Isize(ref val) => self.ast_factory.int_lit_from_ref(&val.as_i64()),
            &ConstInt::Usize(ref val) => self.ast_factory.int_lit_from_ref(&val.as_u64()),
            x => unimplemented!("{:?}", x),
        }
    }

    pub fn eval_bool(&self, val: bool) -> Expr<'v> {
        if val {
            self.ast_factory.true_lit()
        } else {
            self.ast_factory.false_lit()
        }
    }

    pub fn eval_const_val(&self, const_val: &ConstVal<'tcx>) -> Expr<'v> {
        match const_val {
            &ConstVal::Integral(ref const_int) => self.eval_const_int(const_int),
            &ConstVal::Bool(val) => self.eval_bool(val),
            x => unimplemented!("{:?}", x)
        }
    }

    pub fn encode_type_name(&self, def_id: DefId) -> String {
        self.env.get_item_name(def_id).replace("::", "$")
    }

    pub fn encode_procedure_name(&self, proc_def_id: ProcedureDefId) -> String {
        self.env.get_item_name(proc_def_id).replace("::", "$")
    }
}
