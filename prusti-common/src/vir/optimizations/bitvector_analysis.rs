// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Perform a static analysis to determine all integer variables tainted bit a bitwise operation.

use std::collections::HashSet;
use std::env::vars;
use std::fs::File;
use std::io::prelude::*;
use std::boxed::Box;

use ast::Expr;
use ast::Field;
use ast::LocalVar;
use ast::Stmt;
use ast::Type;
use ast::BVSize;
use ast::WithIdentifier;
use viper::BvSize;

use super::super::ast;
use super::super::cfg::*;

#[derive(Debug, Clone)]
pub struct BVAnalysis {
    method: CfgMethod,
    tainted_vars: HashSet<LocalVar>,
    continue_analysis: bool
}



impl BVAnalysis {

    pub fn new(method: CfgMethod) -> Self {
        BVAnalysis {
            method: method.clone(),
            tainted_vars: HashSet::with_capacity(method.local_vars.len()),
            continue_analysis: true,
        }
    }

    pub fn get_new_method(&mut self) -> CfgMethod {
        self.run();
        return self.method.clone()
    }

    pub fn run(&mut self) -> () {

        println!("\nBV-Analyis \"{}\"\n---------------------", self.method.get_identifier());
        
        // Analysis
        let basic_blocks = self.method.basic_blocks.clone();

        let mut it: u32 = 1;
        while self.continue_analysis {    
            
            self.continue_analysis = false;    
            for blk in &basic_blocks { 
                for stmt in &blk.stmts {
                    self.check_stmt(&stmt);
                }
            }
            println!("It. {}; Tainted vars: {:?}", it, self.tainted_vars); it+=1;
        }

        println!("----------");
        println!("Vars: {:?}", self.method.local_vars);
        println!("Tainted Vars: {:?}", self.tainted_vars);
        println!("----------");

        let f1_name = format!("/tmp/{}_before_replacement.vpr", self.method.get_identifier());
        let mut w1 = File::create(f1_name.clone()).unwrap();
        for blk in &self.method.basic_blocks { 
            for stmt in &blk.stmts {
                writeln!(&mut w1, "{}", stmt).unwrap();
            }
        }
        println!("Dumped method to {}", f1_name.clone());

        // Change types of tainted variables
        self.replace_tainted_vars();

        let f2_name = format!("/tmp/{}_after_replacement.vpr", self.method.get_identifier());
        let mut w2 = File::create(f2_name.clone()).unwrap();
        for blk in &self.method.basic_blocks { 
            for stmt in &blk.stmts {
                writeln!(&mut w2, "{}", stmt).unwrap();
            }
        }
        println!("Dumped method to {}", f2_name.clone());
        
        // for blk in &method.basic_blocks { 
        //     for stmt in &blk.stmts {
        //         println!("Statement: {}\nVars of Stmt: {:?}", stmt, vars_of_stmt(stmt));
                
        //     }
        //  }
    
    }

    fn replace_tainted_vars(&mut self) {
        let mut new_method: Vec<CfgBlock> = Vec::new();        

        for blk in &self.method.basic_blocks {
            let mut new_stmts: Vec<Stmt> = Vec::new();
            for stmt in &blk.stmts {
                new_stmts.push(replace_tainted_vars_of_stmt(&self.tainted_vars, stmt));
            }

            let new_block = CfgBlock { stmts: new_stmts, successor: blk.successor.clone() };
            new_method.push(new_block);
        }

        self.method.basic_blocks = new_method;


        let mut new_vars: Vec<LocalVar> = Vec::new();
        for var in &self.method.local_vars {
            if self.tainted_vars.contains(var) {
                new_vars.push(LocalVar {name: var.name.clone(), typ: Type::Bitvector(BVSize::BV8)});
            } else {
                new_vars.push(var.clone());
            }
        }
        self.method.local_vars = new_vars;
    }

    fn check_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Assert(e, _) => self.check_expr(e),
            Stmt::Assign(e1, e2, _) => {
                if self.expr_contains_taint(e1) || self.expr_contains_taint(e2) {
                    let pre_size = self.tainted_vars.len();
                    self.tainted_vars.extend(vars_of_expr(e1));
                    self.tainted_vars.extend(vars_of_expr(e2));
                    self.continue_analysis = pre_size < self.tainted_vars.len();
                } else {
                    self.check_expr(e1); self.check_expr(e2);
                }
            },
            Stmt::If(e, P, Q) => todo!(),
            Stmt::MethodCall(_, args, _) => {
                for arg in args{ self.check_expr(arg); }
            },
            
            _ => ()
        }
    }

    fn check_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::BinOp(op, e1, e2, _) => {
                match op {                
                    ast::BinOpKind::BitAnd |
                    ast::BinOpKind::BitOr |
                    ast::BinOpKind::BitXor |
                    ast::BinOpKind::Shl |
                    ast::BinOpKind::Shr =>{
                        let pre_size = self.tainted_vars.len();
                        self.tainted_vars.extend(vars_of_expr(e1));
                        self.tainted_vars.extend(vars_of_expr(e2));
                        self.continue_analysis = pre_size < self.tainted_vars.len();
                    }
                    _ => { self.check_expr(e1); self.check_expr(e2); }
                }   
            }
            _ => ()
        }

    }

    fn expr_contains_taint(&self, e: &Expr) -> bool {
        let vars = vars_of_expr(e);
        for v in vars {
            if self.tainted_vars.contains(&v) {
                return true
            }
        }
        return false
    }

}

// helper functions
fn vars_of_stmt(s: &Stmt) -> HashSet<LocalVar> {
    let mut vars: HashSet<LocalVar> = HashSet::new();
    match s {
        Stmt::Assign(e1, e2, _) => {
            let mut acc = vars_of_expr(e1);
            acc.extend(vars_of_expr(e2));
            vars.extend(acc);

        },
        _ => () 
    }
    return vars
}

fn vars_of_expr(e: &Expr) -> HashSet<LocalVar> {
    let mut vars: HashSet<LocalVar> = HashSet::new();

    match e {
        Expr::Local(var, _) => {
            vars.insert(var.clone());
        }
        Expr::UnaryOp(_, e, _) => {
            vars_of_expr(e);
        }
        Expr::BinOp(_, e1, e2, _) => {            
            let mut acc = vars_of_expr(e1);
            acc.extend(vars_of_expr(e2));
            vars.extend(acc);
        }
        Expr::Variant(e, _, _) |
        Expr::Field(e, _, _) => {
            vars.extend(vars_of_expr(e))
        },
        _ => ()
    }
    return vars
}

fn replace_tainted_vars_of_stmt(tainted_vars: &HashSet<LocalVar>, stmt: &Stmt) -> Stmt {
    match stmt {
        Stmt::Inhale(e) => Stmt::Inhale(replace_tainted_vars_of_expr(tainted_vars, e)),
        Stmt::Exhale(e, p) => Stmt::Exhale(replace_tainted_vars_of_expr(tainted_vars, e), *p),
        Stmt::Assert(e, p) => Stmt::Assert(replace_tainted_vars_of_expr(tainted_vars, e), *p),
        Stmt::Obtain(e, p) => Stmt::Obtain(replace_tainted_vars_of_expr(tainted_vars, e), *p),
        Stmt::Downcast(e, f) => Stmt::Downcast(replace_tainted_vars_of_expr(tainted_vars, e), f.clone()),
        Stmt::ApplyMagicWand(e, p) => Stmt::ApplyMagicWand(replace_tainted_vars_of_expr(tainted_vars, e), *p),
        
        Stmt::Assign(e1, e2, ak) => 
            Stmt::Assign(
                replace_tainted_vars_of_expr(tainted_vars, e1),
                replace_tainted_vars_of_expr(tainted_vars, e2),
                ak.clone()
            ),

        Stmt::TransferPerm(e1, e2, b) => 
            Stmt::TransferPerm(
                replace_tainted_vars_of_expr(tainted_vars, e1),
                replace_tainted_vars_of_expr(tainted_vars, e2),
                *b
            ),

        Stmt::MethodCall(name, args, targets) => {
            let mut new_args: Vec<Expr> = Vec::new();
            for arg in args { new_args.push(replace_tainted_vars_of_expr(tainted_vars, arg))}
            return Stmt::MethodCall(name.clone(), new_args, targets.clone())
        }

        Stmt::Fold(name, args, perm, me, p) => {
            let mut new_args: Vec<Expr> = Vec::new();
            for arg in args { new_args.push(replace_tainted_vars_of_expr(tainted_vars, arg))}
            return Stmt::Fold(name.clone(), new_args, perm.clone(), me.clone(), p.clone())
        }

        Stmt::Unfold(name, args, perm, me) => {
            let mut new_args: Vec<Expr> = Vec::new();
            for arg in args { new_args.push(replace_tainted_vars_of_expr(tainted_vars, arg))}
            return Stmt::Unfold(name.clone(), new_args, perm.clone(), me.clone())
        }
        
        Stmt::PackageMagicWand(e, stmts, lab, gv, p) => {
            let mut new_stmts: Vec<Stmt> = Vec::new();
            for s in stmts {new_stmts.push(replace_tainted_vars_of_stmt(tainted_vars, s))}
            return Stmt::PackageMagicWand(
                replace_tainted_vars_of_expr(tainted_vars, e),
                new_stmts,
                lab.clone(),
                gv.clone(),
                p.clone()
            )
        }
        
        Stmt::If(e, p, q) => {
            let mut new_p: Vec<Stmt> = Vec::new();
            for s in p {new_p.push(replace_tainted_vars_of_stmt(tainted_vars, s))}
            let mut new_q: Vec<Stmt> = Vec::new();
            for s in q {new_q.push(replace_tainted_vars_of_stmt(tainted_vars, s))}
            return Stmt::If(
                replace_tainted_vars_of_expr(tainted_vars, e),
                new_p,
                new_q
            )
        },        
        s => s.clone()
    }
}

fn replace_tainted_vars_of_expr(tainted_vars: &HashSet<LocalVar>, e: &Expr) -> Expr {
    match e {
        Expr::Local(var, p) => {
            if tainted_vars.contains(var) {
                Expr::Local(
                    LocalVar { name: var.name.clone(), typ: Type::Bitvector(BVSize::BV8) },
                    p.clone()
                )
            } else {
                e.clone()
            }        
        }
        Expr::Field(e, f ,p) => {
            match &**e {
                Expr::Local(lv, p) => {
                    if tainted_vars.contains(&lv) {                        
                        let new_e = replace_tainted_vars_of_expr(tainted_vars, e);
                        let new_f = Field {name : "val_bv8".to_string(), typ: Type::Bitvector(BVSize::BV8) };
                        Expr::Field(Box::from(new_e), new_f, p.clone())
                    } else { Expr::Field(e.clone(), f.clone(), p.clone()) }
                }
                _ => Expr::Field(e.clone(), f.clone(), p.clone())
            }
        }

        Expr::FieldAccessPredicate(e, perm, p) => {
            let new_e = Box::from(replace_tainted_vars_of_expr(tainted_vars, e));
            Expr::FieldAccessPredicate(new_e, perm.clone(), p.clone())
        }

        Expr::BinOp(kind, left, right, p) => {
            let new_left = Box::from(replace_tainted_vars_of_expr(tainted_vars, left));
            let new_right = Box::from(replace_tainted_vars_of_expr(tainted_vars, right));
            Expr::BinOp(kind.clone(), new_left, new_right, p.clone())            
        }

        e => e.clone(),
        
    }
}