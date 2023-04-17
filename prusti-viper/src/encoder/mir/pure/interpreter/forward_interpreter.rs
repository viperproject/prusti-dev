// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! A MIR interpreter that translates MIR into vir_poly expressions.

use crate::encoder::errors::EncodingResult;
use log::trace;
use prusti_common::vir::RETURN_LABEL;
use prusti_rustc_interface::middle::{mir, ty};
use rustc_hash::FxHashMap;
use mir::StatementKind;
use std::{fmt::Debug, iter::FromIterator, marker::Sized};

pub trait ExprFactory<'tcx, Expr, Var> {
    fn local(&self, local: mir::Local) -> EncodingResult<Var>;
    fn var(&self, v: Var) -> EncodingResult<Expr>;
    fn bin_op_expr(&self, op: mir::BinOp, left: Expr, right: Expr, ty: ty::Ty<'tcx>) -> EncodingResult<Expr>;
    fn operand_expr(&self, operand: &mir::Operand<'tcx>) -> EncodingResult<Expr>;
    fn let_expr(&self, binder: Var, value: Expr, body: Expr) -> Expr;
    fn switch_int(&self, cond: Expr, then_expr: Expr, else_expr: Expr) -> Expr;
    fn gt(&self, lhs: Expr, rhs:Expr) -> Expr;
}

fn interpret_rvalue<'tcx, F, Expr, Var>(
    operand_ty: ty::Ty<'tcx>, 
    rvalue: &mir::Rvalue<'tcx>, 
    interpreter: &F
) -> EncodingResult<Expr> where F: ExprFactory<'tcx, Expr, Var> {
    match rvalue {
        &mir::Rvalue::BinaryOp(op, box (ref left, ref right)) => {
            let lhs = interpreter.operand_expr(left)?;
            let rhs = interpreter.operand_expr(right)?;
            interpreter.bin_op_expr(op, lhs, rhs, operand_ty)
        },
        &mir::Rvalue::CheckedBinaryOp(op, box (ref left, ref right)) => {
            let lhs = interpreter.operand_expr(left)?;
            let rhs = interpreter.operand_expr(right)?;
            interpreter.bin_op_expr(op, lhs, rhs, operand_ty)
        },
        other => { 
            unimplemented!("How to interpret {:?}", other) 
        }
    }
}

pub fn run_forward_interpreter<'tcx, F, Expr, Var>(
    mir: &mir::Body<'tcx>,
    interpreter: &F
) -> EncodingResult<Expr> where F: ExprFactory<'tcx, Expr, Var> {
    let mut cur_block = &mir.basic_blocks[mir::START_BLOCK];
    let mut assns: Vec<(Var, Expr)> = vec![];
    println!("{:#?}", mir);
    for stmt in cur_block.statements.iter() {
        match &stmt.kind {
            StatementKind::Assign(box (lhs, rhs)) => {
                let lhs = lhs.as_local().unwrap();
                let ty = mir.local_decls[lhs].ty;
                let rhs_expr = interpret_rvalue(ty, rhs, interpreter)?;
                let lhs = interpreter.local(lhs)?;
                assns.push((lhs, rhs_expr));
            }
            _ => { unimplemented!() }
        }
        println!("{:?}", stmt);
    }
    let mut result: Expr = interpreter.var(
        interpreter.local(mir::RETURN_PLACE)?
    )?;
    for assn in assns {
        result = interpreter.let_expr(assn.0, assn.1, result)
    }
    Ok(result)
}