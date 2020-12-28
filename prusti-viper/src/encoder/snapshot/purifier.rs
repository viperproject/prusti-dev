use ::log::{info, debug, trace};
use crate::encoder::borrows::{compute_procedure_contract, ProcedureContract, ProcedureContractMirDef};
use crate::encoder::builtin_encoder::BuiltinEncoder;
use crate::encoder::builtin_encoder::BuiltinFunctionKind;
use crate::encoder::builtin_encoder::BuiltinMethodKind;
use crate::encoder::errors::{ErrorCtxt, ErrorManager, EncodingError, PositionlessEncodingError, WithSpan, RunIfErr};
use crate::encoder::foldunfold;
use crate::encoder::places;
use crate::encoder::procedure_encoder::ProcedureEncoder;
use crate::encoder::pure_function_encoder::PureFunctionEncoder;
use crate::encoder::stub_function_encoder::StubFunctionEncoder;
use crate::encoder::spec_encoder::encode_spec_assertion;
use crate::encoder::snapshot_encoder::{Snapshot, SnapshotEncoder};
use crate::encoder::type_encoder::{
    compute_discriminant_values, compute_discriminant_bounds, TypeEncoder};
use prusti_common::vir;
use prusti_common::vir::WithIdentifier;
use prusti_common::config;
use prusti_common::report::log;
// use prusti_interface::constants::PRUSTI_SPEC_ATTR;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::Environment;
use prusti_interface::specs::typed;
use prusti_interface::specs::typed::SpecificationId;
use prusti_interface::utils::{has_spec_only_attr, read_prusti_attrs, has_prusti_attr};
use prusti_interface::PrustiError;
// use prusti_interface::specs::{
//     SpecID, SpecificationSet, TypedAssertion,
//     TypedSpecificationMap, TypedSpecificationSet,
// };
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

use super::super::snapshot_encoder::SnapshotAdtEncoder;

pub struct ExprPurifier {
    pub old_formal_args: Vec<vir::LocalVar>,
    pub snapshots: HashMap<String, Box<Snapshot>>,
}

 impl ExprPurifier {
    pub fn transalte_type(&self, t: vir::Type) -> vir::Type {
        match t {
            vir::Type::TypedRef(name) => match name.as_str() {
                "i32" => vir::Type::Int,
                _ => {
                    let domain_name = self
                        .snapshots
                        .get(&name)
                        .and_then(|snap| snap.domain())
                        .map(|domain| domain.name)
                        .expect(&format!("No matching domain for {}", name));

                    vir::Type::Domain(domain_name)
                }
            },
            o @ _ => o,
        }
    }
}

impl vir::ExprFolder for ExprPurifier {
    fn fold_unfolding(
        &mut self,
        name: String,
        args: Vec<vir::Expr>,
        expr: Box<vir::Expr>,
        perm: vir::PermAmount,
        variant: vir::MaybeEnumVariantIndex,
        pos: vir::Position,
    ) -> vir::Expr {
        *self.fold_boxed(expr)
    }

    fn fold_field(
        &mut self,
        receiver: Box<vir::Expr>,
        field: vir::Field,
        pos: vir::Position,
    ) -> vir::Expr {
        let receiver_type: vir::Type = receiver.get_type().clone();
        if let vir::Type::TypedRef(receiver_domain) = receiver_type {
            let receiver_domain = format!("Snap${}", receiver_domain);
            let inner = self.fold_boxed(receiver);
            let field_name = field.name.to_string();
            info!("translating field {}", field_name);
            match field_name.as_str() {
                "val_bool" | "val_int" => *inner,
                _ => {
                    let field_name: String = field_name.chars().skip(2).collect();
                    let field_type = field.typ.clone();
                    let purified_field_type = self.transalte_type(field_type);
                   
                    info!("found domain {} ", receiver_domain);

                    let domain_func = SnapshotAdtEncoder::encode_field_domain_func_from_snapshot(
                        purified_field_type,
                        field_name,
                        receiver_domain,
                    )
                    .unwrap();
                    vir::Expr::DomainFuncApp(domain_func, vec![*inner], pos)
                }
            }
        }
        else {
            unreachable!();
        }
    }

    fn fold_local(&mut self, v: vir::LocalVar, p: vir::Position) -> vir::Expr {
        vir::Expr::Local(
            vir::LocalVar {
                name: v.name,
                typ: self.transalte_type(v.typ),
            },
            p,
        )
    }
}

