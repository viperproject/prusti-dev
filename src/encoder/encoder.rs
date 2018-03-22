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

pub struct Encoder<'v, 'tcx: 'v, P: 'v + Procedure<'tcx>> {
    pub(super) ast_factory: viper::AstFactory<'v>,
    pub(super) cfg_factory: viper::CfgFactory<'v>,
    pub(super) env: &'v Environment<'tcx, ProcedureImpl=P>,
    pub(super) procedures: HashMap<ProcedureDefId, Method<'v>>,
}

impl<'v, 'tcx, P: Procedure<'tcx>> Encoder<'v, 'tcx, P> {
    pub fn new(ast_factory: viper::AstFactory<'v>,
               cfg_factory: viper::CfgFactory<'v>,
               env: &'v Environment<'tcx, ProcedureImpl=P>) -> Self {
        Encoder {
            ast_factory,
            cfg_factory,
            env,
            procedures: HashMap::new()
        }
    }

    pub fn get_used_viper_domains(&self) -> Vec<Domain<'v>> {
        // TODO
        vec![]
    }

    pub fn get_used_viper_fields(&self) -> Vec<Field<'v>> {
        // TODO
        vec![]
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
        self.procedures.values().cloned().collect()
    }

    pub fn use_rust_procedure(&mut self, proc_def_id: ProcedureDefId) {
        let procedure = self.env.get_procedure(proc_def_id);
        let mut procedure_encoder = ProcedureEncoder::new(self, &procedure);
        procedure_encoder.set_used();
    }

    pub(super) fn encode_const_int(&self, const_int: &ConstInt) -> Expr<'v> {
        match const_int {
            &ConstInt::U8(ref val) => self.ast_factory.int_lit_from_ref(val),
            &ConstInt::Isize(ref val) => self.ast_factory.int_lit_from_ref(&val.as_i64()),
            x => unimplemented!("{:?}", x),
        }
    }

    pub(super) fn encode_type(&self, ty: ty::Ty<'tcx>) -> viper::Type<'v> {
        match ty.sty {
            ty::TypeVariants::TyBool => self.ast_factory.bool_type(),

            ty::TypeVariants::TyInt(_) |
            ty::TypeVariants::TyUint(_) => self.ast_factory.int_type(),

            ty::TypeVariants::TyRawPtr(_) |
            ty::TypeVariants::TyRef(_, _) => self.ast_factory.ref_type(),

            ref x => unimplemented!("{:?}", x),
        }
    }

    pub(super) fn encode_bool(&self, val: bool) -> Expr<'v> {
        if val {
            self.ast_factory.true_lit()
        } else {
            self.ast_factory.false_lit()
        }
    }

    pub(super) fn encode_const_val(&self, const_val: &ConstVal<'tcx>) -> Expr<'v> {
        match const_val {
            &ConstVal::Integral(ref const_int) => self.encode_const_int(const_int),
            &ConstVal::Bool(val) => self.encode_bool(val),
            x => unimplemented!("{:?}", x)
        }
    }
}
