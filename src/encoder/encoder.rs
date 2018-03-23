// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::{self, Viper, Expr, VerificationError};
use viper::{Domain, Field, Function, Predicate, Method};
use viper::AstFactory;
use rustc::mir;
use rustc::ty;
use prusti_interface::environment::Procedure;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::Environment;
use std::collections::HashMap;
use viper::CfgBlockIndex;
use prusti_interface::environment::BasicBlockIndex;
use rustc::mir::TerminatorKind;
use viper::Successor;
use rustc::middle::const_val::{ConstInt, ConstVal};
use encoder::procedure_encoder::ProcedureEncoder;
use encoder::viper_type::ViperType;
use std::cell::RefCell;

pub struct Encoder<'v, 'tcx: 'v, P: 'v + Procedure<'tcx>> {
    ast_factory: viper::AstFactory<'v>,
    cfg_factory: viper::CfgFactory<'v>,
    env: &'v Environment<'tcx, ProcedureImpl=P>,
    procedures: RefCell<HashMap<ProcedureDefId, Method<'v>>>,
    value_fields: RefCell<HashMap<ViperType, Field<'v>>>,
}

impl<'v, 'tcx, P: Procedure<'tcx>> Encoder<'v, 'tcx, P> {
    pub fn new(ast_factory: viper::AstFactory<'v>,
               cfg_factory: viper::CfgFactory<'v>,
               env: &'v Environment<'tcx, ProcedureImpl=P>) -> Self {
        Encoder {
            ast_factory,
            cfg_factory,
            env,
            procedures: RefCell::new(HashMap::new()),
            value_fields: RefCell::new(HashMap::new()),
        }
    }

    pub fn ast_factory(&self) -> &viper::AstFactory<'v> {
        &self.ast_factory
    }

    pub fn cfg_factory(&self) -> &viper::CfgFactory<'v> {
        &self.cfg_factory
    }

    pub fn env(&self) -> &'v Environment<'tcx, ProcedureImpl=P> {
        self.env
    }

    pub fn get_used_viper_domains(&self) -> Vec<Domain<'v>> {
        // TODO
        vec![]
    }

    pub fn get_used_viper_fields(&self) -> Vec<Field<'v>> {
        self.value_fields.borrow().values().cloned().collect()
    }

    pub fn get_used_viper_functions(&self) -> Vec<Function<'v>> {
        // TODO
        vec![]
    }

    pub fn get_used_viper_predicates(&self) -> Vec<Predicate<'v>> {
        // TODO
        vec![]
    }

    pub fn get_used_viper_methods(&self) -> Vec<Method<'v>> {
        self.procedures.borrow().values().cloned().collect()
    }

    pub fn encode_value_field(&self, viper_type: ViperType) -> Field<'v> {
        *self.value_fields.borrow_mut().entry(viper_type).or_insert_with(|| match viper_type {
            ViperType::Int => self.ast_factory.field("val_int", self.ast_factory.int_type()),
            ViperType::Bool => self.ast_factory.field("val_bool", self.ast_factory.bool_type()),
            ViperType::Ref => self.ast_factory.field("val_ref", self.ast_factory.ref_type())
        })
    }

    pub fn encode_procedure(&self, proc_def_id: ProcedureDefId) -> Method<'v> {
        let method = *self.procedures.borrow_mut().entry(proc_def_id).or_insert_with(|| {
            let procedure = self.env.get_procedure(proc_def_id);
            let mut procedure_encoder = ProcedureEncoder::new(self, &procedure);
            procedure_encoder.encode()
        });
        method
    }

    pub(super) fn const_int_is_zero(&self, const_int: &ConstInt) -> bool {
        match const_int {
            &ConstInt::I32(val) => val == (0 as i32),
            &ConstInt::U8(val) => val == (0 as u8),
            &ConstInt::Isize(val) => val.as_i64() == (0 as i64),
            x => unimplemented!("{:?}", x),
        }
    }

    pub(super) fn eval_const_int(&self, const_int: &ConstInt) -> Expr<'v> {
        match const_int {
            &ConstInt::I32(ref val) => self.ast_factory.int_lit_from_ref(val),
            &ConstInt::U8(ref val) => self.ast_factory.int_lit_from_ref(val),
            &ConstInt::Isize(ref val) => self.ast_factory.int_lit_from_ref(&val.as_i64()),
            x => unimplemented!("{:?}", x),
        }
    }

    pub(super) fn viper_field_type(&self, ty: ty::Ty<'tcx>) -> ViperType {
        match ty.sty {
            ty::TypeVariants::TyBool => ViperType::Bool,

            ty::TypeVariants::TyInt(_) |
            ty::TypeVariants::TyUint(_) => ViperType::Int,

            ty::TypeVariants::TyRawPtr(_) |
            ty::TypeVariants::TyRef(_, _) => ViperType::Ref,

            ty::TypeVariants::TyAdt(_, _) |
            ty::TypeVariants::TyTuple(_, _) => ViperType::Ref,

            ref x => unimplemented!("{:?}", x),
        }
    }

    pub(super) fn eval_bool(&self, val: bool) -> Expr<'v> {
        if val {
            self.ast_factory.true_lit()
        } else {
            self.ast_factory.false_lit()
        }
    }

    pub(super) fn eval_const_val(&self, const_val: &ConstVal<'tcx>) -> Expr<'v> {
        match const_val {
            &ConstVal::Integral(ref const_int) => self.eval_const_int(const_int),
            &ConstVal::Bool(val) => self.eval_bool(val),
            x => unimplemented!("{:?}", x)
        }
    }

    pub(super) fn encode_procedure_name(&self, proc_def_id: ProcedureDefId) -> String {
        self.env.get_procedure_name(proc_def_id).replace("::", "$")
    }
}
