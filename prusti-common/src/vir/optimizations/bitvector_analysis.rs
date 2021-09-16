// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! Perform a static analysis to determine all integer variables tainted bit a bitwise operation.

use std::{any::Any, boxed::Box, collections::{HashSet, HashMap}, env::{var, vars}, fs::File, io::prelude::*, iter::FromIterator};
use ast::{BVConst, BVSize, Const, Expr, Field, LocalVar, PermAmount, Position, Predicate, Stmt, StructPredicate, Type, WithIdentifier, BinOpKind};
use itertools::concat;
use uuid::Variant;
use viper::{BvSize};
use crate::{itertools::Itertools, vir};

use super::super::ast;
use super::super::cfg::*;

#[derive(Debug, Clone)]
pub struct BVAnalysis {
    method: CfgMethod, // Method to be analyzed
    replacements: HashMap<Expr, Expr>, // Set of all tainted fields
    pub new_fields: HashSet<Field>,
    pub new_predicates: HashSet<String>,
    continue_analysis: bool
}



impl BVAnalysis {

    pub fn new() -> Self {
        let empty_cfg_method = CfgMethod::new(
            "empty_method".to_string(),
            0,
            vec![],
            vec![],
            vec![],
        );
        BVAnalysis {
            method: empty_cfg_method,
            replacements: HashMap::new(),
            new_fields: HashSet::new(),
            new_predicates: HashSet::new(),
            continue_analysis: true,
        }
    }

    pub fn method_contains_bitwise_op(m:CfgMethod) -> bool {
        let mut res = false;
        for blk in m.basic_blocks {
            for stmt in blk.stmts {
                res = res || stmt_contains_bw_op(stmt)
            }
        }
        res        
    }

    pub fn print_tainted_expressions(&self) {
        for (old, new) in &self.replacements {
            println!("{} --> {}", old, new);
        }
    }

    pub fn get_new_method(&mut self, method: CfgMethod, debug: bool) -> CfgMethod {
        self.method = method;
        self.run(debug);
        return self.method.clone()
    }

    fn run(&mut self, debug: bool) {
        if debug {
            println!("\nBV-Analyis \"{}\"\n---------------------", self.method.get_identifier());
            self.dump_method("before");
        }
        
        // Analysis
        let basic_blocks = self.method.basic_blocks.clone();

        let mut it: u32 = 1;
        while self.continue_analysis {
            let pre_size = self.replacements.len();
            self.continue_analysis = false;    
            for blk in &basic_blocks { 
                for stmt in &blk.stmts {
                    self.check_stmt(&stmt);
                }
            }
            if debug { println!("\nIt. {}; Tainted expressions: ", it); it+=1; self.print_tainted_expressions(); }

            self.continue_analysis = pre_size < self.replacements.len();
        }

        // Change types of tainted variables and constants
        self.replace_tainted_fields();
        self.replace_tainted_constants();

        // update method local variables
        self.replace_method_vars();

        // update return variables
        self.replace_tainted_formal_returns();

        // get new fields to be added
        self.get_used_bitvector_fields();

        if debug {
            println!("\nREPLACEMENTS\n-------------");
            for (old, new) in &self.replacements {
                println!("{:?} \n->\n {:?}\n---", old , new);
            }
            println!("New predicates: {:?}", self.new_predicates);
            self.dump_method("after");
        }
    }

    fn replace_tainted_formal_returns(&mut self) {

        let mut new_returns : Vec<LocalVar> = Vec::new();
        for lv in &self.method.formal_returns {

            let lv_expr = Expr::Local(lv.clone(), Position::default());
            let new_var = match self.replacements.get(&lv_expr) {
                Some(e) => {
                    match e {
                        Expr::Local(new_lv, _) => new_lv.clone(),
                        _ => unreachable!()
                    }
                },
                None => lv.clone(),
            };
            new_returns.push(new_var);
        }
        self.method.formal_returns = new_returns;
    }

    fn replace_tainted_fields(&mut self) {
        let mut new_method: Vec<CfgBlock> = Vec::new();
        let basic_blks = self.method.basic_blocks.clone();
        for blk in  basic_blks {
            let mut new_stmts: Vec<Stmt> = Vec::new();
            for stmt in &blk.stmts {
                let new_stmt = self.replace_tainted_expressions_of_stmt(stmt);
                new_stmts.push(new_stmt);
            }

            let new_block = CfgBlock { stmts: new_stmts, successor: blk.successor.clone() };
            new_method.push(new_block);
        }
        self.method.basic_blocks = new_method;

    }

    fn replace_tainted_constants(&mut self) {
        let mut new_method: Vec<CfgBlock> = Vec::new();
        for blk in &self.method.basic_blocks {
            let mut new_stmts: Vec<Stmt> = Vec::new();
            for stmt in &blk.stmts {
                new_stmts.push(self.replace_tainted_consts_of_stmt(stmt));
            }

            let new_block = CfgBlock { stmts: new_stmts, successor: blk.successor.clone() };
            new_method.push(new_block);
        }

        self.method.basic_blocks = new_method;

    }

    fn check_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Assert(e, _) => self.check_expr(e),
            Stmt::Assign(e1, e2, _) => {
                self.check_expr(&e1.clone()); self.check_expr(&e2.clone());
                match e2 {
                    Expr::BinOp(ast::BinOpKind::EqCmp, _, _ , _)
                    | Expr::BinOp(ast::BinOpKind::NeCmp, _, _ , _)
                    | Expr::BinOp(ast::BinOpKind::GeCmp, _, _, _)
                    | Expr::BinOp(ast::BinOpKind::GtCmp, _, _, _)
                    | Expr::BinOp(ast::BinOpKind::LeCmp, _, _, _)
                    | Expr::BinOp(ast::BinOpKind::LtCmp, _, _, _)
                    | Expr::BinOp(ast::BinOpKind::And, _, _ , _)
                    | Expr::BinOp(ast::BinOpKind::Or, _, _, _) => (),
                    
                    | Expr::BinOp(ast::BinOpKind::BitAnd, _, _, _)
                    | Expr::BinOp(ast::BinOpKind::BitOr, _, _, _)
                    | Expr::BinOp(ast::BinOpKind::BitXor, _, _, _)
                    | Expr::BinOp(ast::BinOpKind::Shl, _, _, _)
                    | Expr::BinOp(ast::BinOpKind::LShr, _, _, _)
                    | Expr::BinOp(ast::BinOpKind::AShr, _, _, _) => {
                        self.field_replacements(e1.clone());
                    }

                    Expr::UnaryOp(ast::UnaryOpKind::Not, e, _) => {
                        if self.replacements.keys().contains(&*e.clone()) {
                            self.field_replacements(e1.clone());
                        }
                    }

                    Expr::BinOp(ast::BinOpKind::Add, se1, se2, _)
                    | Expr::BinOp(ast::BinOpKind::Mul, se1, se2, _)
                    | Expr::BinOp(ast::BinOpKind::Sub, se1, se2, _)
                    | Expr::BinOp(ast::BinOpKind::Div, se1, se2, _)  => {
                        if self.replacements.keys().contains(&*se1.clone()) || self.replacements.keys().contains(&*se2.clone()) {
                            self.field_replacements(e1.clone());
                            
                        }
                    }
                    _ => {
                        if self.replacements.keys().contains(&e1.clone()) {
                            self.field_replacements(e2.clone());
                        } else if self.replacements.keys().contains(&e2.clone()) {
                            self.field_replacements(e1.clone());
                        }
                    }
                };
            },
            Stmt::If(_e, _p, _q) => todo!(),
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
                    ast::BinOpKind::LShr |
                    ast::BinOpKind::AShr =>{
                        self.field_replacements(*e1.clone());
                        self.field_replacements(*e2.clone());
                    }
                    _ => { self.check_expr(e1); self.check_expr(e2); }
                }   
            }
            _ => ()
        }
    }

    // Adds field and local variable replacements of an expression to the replacement map
    fn field_replacements(&mut self, field: Expr) {        
        let old = field.clone();
        if !self.replacements.keys().contains(&field.clone()) {
            match field {
                Expr::Local(local_var, _) => {

                    let ref_typ_str = match local_var.typ {
                        Type::TypedRef(s) => s,
                        _ => unreachable!()
                    };

                    // Create new LocalVar replacement
                    let (new_ref_type, new_type) = convert_ref_type_string(ref_typ_str);
                    let new_local_var = LocalVar {
                        name: local_var.name.clone(),
                        typ: Type::TypedRef(new_ref_type.clone())
                    };
                    let new_local = Expr::Local(
                        new_local_var,
                        Position::default()
                    );

                    // Create potential field access replacements
                    let old_local_field = Field { name: "val_int".into(), typ: Type::Int };
                    let old_field_of_local_var = Expr::Field(
                        box old.clone(),
                        old_local_field,
                        Position::default()
                    );
                    let local_field = Field {name: format!("val_{}", new_ref_type), typ: new_type};
                    let field_of_local_var = Expr::Field(
                        box new_local.clone(),
                        local_field,
                        Position::default()
                    );

                    self.replacements.insert(old_field_of_local_var, field_of_local_var);
                    self.replacements.insert(old, new_local);

                }
                Expr::Field(f_expr, _, _) => {
                    let (new_f_expr, new_f_field) = match *f_expr {
                        Expr::Local(_, _) => self.get_new_local(*f_expr.clone()),
                        Expr::Field(_, _, _) => self.get_new_field(*f_expr.clone()),
                        _ => unimplemented!()
                    };

                    let new_field = Expr::Field(
                        box new_f_expr,
                        new_f_field,
                        Position::default()    
                    );
                    self.replacements.insert(old, new_field);

                }
                _ => ()
            }
        }
    }

    fn get_new_field(&mut self, field:Expr) -> (Expr, Field) {
        let old_field = field.clone();
        match field {
            Expr::Field(f_expr, f_field, _) => {
                
                if f_field.name.contains("tuple") {
                    let (ret_name, ret_type) = match f_field.typ {
                        Type::TypedRef(s) => {
                            convert_ref_type_string(s)
                        }
                        _ => unreachable!()                   
                    };

                    let (new_f_expr, _) = match *f_expr {
                        Expr::Local(ref lv, _) => {

                            let replacement_pos: u8 = f_field.name.clone().split('_').last().unwrap().parse().unwrap();
                            
                            match &lv.typ {
                                Type::TypedRef(s) => {
                                    let new_ref_ty =replace_tuple_field_type(s.clone(), replacement_pos, ret_name.clone());
                                    self.get_new_local_tuple_ref(*f_expr.clone(), new_ref_ty)
                                }
                                _ => unreachable!()
                            }
                        }
                        Expr::Field(_, _, _) => self.get_new_field(*f_expr.clone()),
                        _ => unreachable!()
                    };
                                  
                    let new_f_field = Field {name: f_field.name.clone(), typ: Type::TypedRef(ret_name.clone())};
                    
                    let new_field = Expr::Field(
                        box new_f_expr,
                        new_f_field,
                        Position::default()
                    );                    
                    
                    let return_field = Field {name: format!("val_{}", ret_name), typ: ret_type.clone()};
                    self.replacements.insert(old_field,new_field.clone());  
                    (new_field, return_field)
                } else {
                    let (new_f_expr, new_f_field) = match *f_expr {
                        Expr::Local(..) => self.get_new_local(*f_expr.clone()),
                        Expr::Field(..) => self.get_new_field(*f_expr.clone()),
                        _ => unreachable!()
                    };

                    if new_f_field.name.contains("_beg_$_end_") {
                        
                        let (struct_f_field, return_field) = match f_field.typ {
                            Type::TypedRef(s) => {
                                let (ret_name, ret_type) = convert_ref_type_string(s);
                                (Field {name: f_field.name.clone(), typ: Type::TypedRef(ret_name.clone())},
                                Field {name: format!("val_{}", ret_name), typ: ret_type})
                            }
                            _=> unreachable!()
                        };
                        
                        let new_field =
                        Expr::Field(
                            box new_f_expr,
                            struct_f_field.clone(),
                            Position::default()
                        );
                        

                        self.replacements.insert(old_field, new_field.clone());
                        (new_field, return_field)



                    } else {
                        let return_field = match f_field.typ {
                            Type::TypedRef(s) => {
                                let (ret_name, _) = convert_ref_type_string(s);
                                Field {name: format!("val_{}", ret_name), typ: Type::TypedRef(ret_name)}
                            }
                            _=> unreachable!()
                        };
                        let new_field =
                        Expr::Field(
                            box new_f_expr,
                            new_f_field,
                            Position::default()
                        );
                    
                        self.replacements.insert(old_field, new_field.clone());
                        (new_field, return_field)
                    }
                } 
            }
            _ => unreachable!()
        }
    }

    fn get_new_local_tuple_ref(&mut self, local:Expr, new_ty: String) -> (Expr, Field) {
        let old_local = local.clone();
        match local {
            Expr::Local(local_var, _) => {
                let new_local = Expr::Local(
                    LocalVar {
                        name: local_var.name.clone(),
                        typ: Type::TypedRef(new_ty)
                    },
                    Position::default()
                );
                self.replacements.insert(old_local, new_local.clone());
                (new_local, Field {name:"dummyfield".into(), typ: Type::Int})
            }
            _ => unreachable!("Expr {} is not a Expr::Local(..)", local)
        }
    }

    fn get_new_local(&mut self, local:Expr) -> (Expr, Field) {
        
        let old_local = local.clone();
        match local {
            Expr::Local(local_var, _) => {

                match local_var.typ {
                    Type::TypedRef(s) => {
                        let (field_suffix, new_type) = convert_ref_type_string(s);

                        let new_local_var = LocalVar {
                            name: local_var.name.clone(),
                            typ: Type::TypedRef(field_suffix.clone()),
                        };

                        let new_local = Expr::Local(new_local_var, Position::default());

                        let new_field = Field {
                            name: format!("val_{}", field_suffix),
                            typ: new_type.clone(),
                        };

                        self.replacements.insert(old_local, new_local.clone());
                        return (new_local, new_field)
                    }
                    _ => unreachable!()
                }
            }
            _ => unreachable!()
        }
    }

    fn replace_method_vars(&mut self) {
        let mut local_var_replacements:HashMap<LocalVar, LocalVar> = HashMap::new();
        for (old, new) in &self.replacements {
            match old {
                Expr::Local(old_lv, _) => 
                match new {
                    Expr::Local(new_lv, _) => {local_var_replacements.insert(old_lv.clone(), new_lv.clone());},
                    _ => unreachable!()
                }
                _ => ()
            }
        }

        let mut new_vars:Vec<LocalVar> = Vec::new();

        for var in &self.method.local_vars {
            if local_var_replacements.contains_key(&var) {
                new_vars.push(local_var_replacements.get(&var).unwrap().clone())
            } else {
                new_vars.push(var.clone())
            }
        }
        self.method.local_vars = new_vars

    }

    fn replace_tainted_expressions_of_stmt(&mut self, stmt: &Stmt) -> Stmt {
        match stmt {
            Stmt::Inhale(e) => Stmt::Inhale(self.replace_tainted_fields_of_expr(e)),
            Stmt::Exhale(e, p) => Stmt::Exhale(self.replace_tainted_fields_of_expr( e), *p),
            Stmt::Assert(e, p) => Stmt::Assert(self.replace_tainted_fields_of_expr(e), *p),
            Stmt::Obtain(e, p) => Stmt::Obtain(self.replace_tainted_fields_of_expr(e), *p),
            Stmt::Downcast(e, f) => Stmt::Downcast(self.replace_tainted_fields_of_expr(e), f.clone()),
            Stmt::ApplyMagicWand(e, p) => Stmt::ApplyMagicWand(self.replace_tainted_fields_of_expr(e), *p),
            
            Stmt::Assign(e1, e2, ak) => 
                Stmt::Assign(
                    self.replace_tainted_fields_of_expr(e1),
                    self.replace_tainted_fields_of_expr(e2),
                    ak.clone()
                ),
    
            Stmt::TransferPerm(e1, e2, b) => 
                Stmt::TransferPerm(
                    self.replace_tainted_fields_of_expr(e1),
                    self.replace_tainted_fields_of_expr(e2),
                    *b
                ),
    
            Stmt::MethodCall(name, args, targets) => {
                let mut new_args: Vec<Expr> = Vec::new();
                for arg in args { new_args.push(self.replace_tainted_fields_of_expr(arg)) }
                //let mut new_targets: Vec<LocalVar> = Vec::new();
                return Stmt::MethodCall(name.clone(), new_args, targets.clone())
            }
    
            Stmt::Fold(name, args, perm, me, p) => {
                let mut new_args: Vec<Expr> = Vec::new();
                let mut new_name = String::from("");
                for arg in args {
                    if self.replacements.keys().contains(arg) {
                        new_name = convert_ref_type_string(name.clone()).0;
                    } else {
                        new_name = name.clone();
                    }
                    new_args.push(self.replace_tainted_fields_of_expr(arg)) 
                }
                return Stmt::Fold(new_name, new_args, perm.clone(), me.clone(), p.clone())
            }
    
            Stmt::Unfold(name, args, perm, me) => {
                let mut new_args: Vec<Expr> = Vec::new();
                for arg in args { new_args.push(self.replace_tainted_fields_of_expr(arg)) }
                let (new_name, _) = convert_ref_type_string(name.clone());
                return Stmt::Unfold(new_name, new_args, perm.clone(), me.clone())
            }
            
            Stmt::PackageMagicWand(e, stmts, lab, gv, p) => {
                let mut new_stmts: Vec<Stmt> = Vec::new();
                for s in stmts {new_stmts.push(self.replace_tainted_expressions_of_stmt(s))}
                return Stmt::PackageMagicWand(
                    self.replace_tainted_fields_of_expr(e),
                    new_stmts,
                    lab.clone(),
                    gv.clone(),
                    p.clone()
                )
            }
            
            Stmt::If(e, p, q) => {
                let mut new_p: Vec<Stmt> = Vec::new();
                for s in p {new_p.push(self.replace_tainted_expressions_of_stmt(s))}
                let mut new_q: Vec<Stmt> = Vec::new();
                for s in q {new_q.push(self.replace_tainted_expressions_of_stmt(s))}
                return Stmt::If(
                    self.replace_tainted_fields_of_expr(e),
                    new_p,
                    new_q
                )
            },
            s => s.clone()
        }
    }
    
    fn replace_tainted_fields_of_expr(&mut self, e: &Expr) -> Expr {
        
        if self.replacements.keys().contains(&e.clone()) {
            self.replacements.get(&e.clone()).unwrap().clone()
        } else {
            match e {
                Expr::FieldAccessPredicate(e, perm, p) => {
                    let new_e = Box::from(self.replace_tainted_fields_of_expr(e));
                    Expr::FieldAccessPredicate(new_e, perm.clone(), p.clone())
                }

                Expr::PredicateAccessPredicate(pred_name, local, perm, p) => {
                    if self.replacements.keys().contains(&*local.clone()) {
                        self.replace_pred_access_pred(pred_name.clone(), *local.clone(), perm.clone(), p.clone())
                    } else {
                        e.clone()
                    }
                }
        
                Expr::BinOp(kind, left, right, p) => {
                    let new_left = Box::from(self.replace_tainted_fields_of_expr(left));
                    let new_right = Box::from(self.replace_tainted_fields_of_expr(right));
                    Expr::BinOp(kind.clone(), new_left, new_right, p.clone())
                }
        
                Expr::UnaryOp(op_kind, e, p) => {
                    let new_e = self.replace_tainted_fields_of_expr(e);
                    Expr::UnaryOp(op_kind.clone(), box new_e, p.clone())
                }
                e => e.clone()
            }
        }
    }

    fn replace_pred_access_pred(&mut self, name: String, local: Expr, perm: PermAmount, p: Position) -> Expr {
        let (new_name, _) = convert_ref_type_string(name);
        let new_local = self.replacements.get(&local).unwrap();       
        self.new_predicates.insert(new_name.clone());
        Expr::PredicateAccessPredicate(
            new_name,
            box new_local.clone(),
            perm.clone(),
            p.clone()
        )
    }

    fn replace_tainted_consts_of_stmt(&self, stmt: &Stmt) -> Stmt {
    
        let fields = fields_of_stmt(stmt);
        let is_tainted = fields.iter().fold(false, |is_tainted, f| is_tainted || self.replacements.values().contains(f));
        if is_tainted {            
            let target_type = get_target_type(fields.clone());

            match stmt {
                Stmt::Inhale(e) => Stmt::Inhale(self.replace_tainted_consts_of_expr(e, target_type)),
                Stmt::Exhale(e, p) => Stmt::Exhale(self.replace_tainted_consts_of_expr(e, target_type), *p),
                Stmt::Assert(e, p) => Stmt::Assert(self.replace_tainted_consts_of_expr(e, target_type), *p),
                Stmt::Obtain(e, p) => Stmt::Obtain(self.replace_tainted_consts_of_expr(e, target_type), *p),
                Stmt::Downcast(e, f) => Stmt::Downcast(self.replace_tainted_consts_of_expr(e, target_type), f.clone()),
                Stmt::ApplyMagicWand(e, p) => Stmt::ApplyMagicWand(self.replace_tainted_consts_of_expr(e, target_type), *p),
                
                Stmt::Assign(e1, e2, ak) =>
                    Stmt::Assign(
                        self.replace_tainted_consts_of_expr(e1, target_type.clone()),
                        self.replace_tainted_consts_of_expr(e2, target_type),
                        ak.clone()
                    ),
    
                Stmt::TransferPerm(e1, e2, b) =>
                    Stmt::TransferPerm(
                        self.replace_tainted_consts_of_expr(e1, target_type.clone()),
                        self.replace_tainted_consts_of_expr(e2, target_type),
                        *b
                    ),
    
                Stmt::MethodCall(name, args, targets) => {
                    let mut new_args: Vec<Expr> = Vec::new();
                    for arg in args { new_args.push(self.replace_tainted_consts_of_expr(arg, target_type.clone())) }
                    return Stmt::MethodCall(name.clone(), new_args, targets.clone())
                }
    
                Stmt::Fold(name, args, perm, me, p) => {
                    println!("{:?}", stmt);
                    let mut new_args: Vec<Expr> = Vec::new();
                    for arg in args { new_args.push(self.replace_tainted_consts_of_expr(arg, target_type.clone())) }
                    return Stmt::Fold(name.clone(), new_args, perm.clone(), me.clone(), p.clone())
                }
    
                Stmt::Unfold(name, args, perm, me) => {
                    let mut new_args: Vec<Expr> = Vec::new();
                    for arg in args { new_args.push(self.replace_tainted_consts_of_expr(arg, target_type.clone())) }
                    return Stmt::Unfold(name.clone(), new_args, perm.clone(), me.clone())
                }
                
                Stmt::PackageMagicWand(e, stmts, lab, gv, p) => {
                    let mut new_stmts: Vec<Stmt> = Vec::new();
                    for s in stmts {new_stmts.push(self.replace_tainted_consts_of_stmt(s))}
                    return Stmt::PackageMagicWand(
                        self.replace_tainted_consts_of_expr(e, target_type),
                        new_stmts,
                        lab.clone(),
                        gv.clone(),
                        p.clone()
                    )
                }
                
                Stmt::If(e, p, q) => {
                    let mut new_p: Vec<Stmt> = Vec::new();
                    for s in p {new_p.push(self.replace_tainted_consts_of_stmt(s))}
                    let mut new_q: Vec<Stmt> = Vec::new();
                    for s in q {new_q.push(self.replace_tainted_consts_of_stmt(s))}
                    return Stmt::If(
                        self.replace_tainted_consts_of_expr(e, target_type),
                        new_p,
                        new_q
                    )
                }        
                s => s.clone()
            }
        } else {
            return stmt.clone()
        }
    }
    
    fn replace_tainted_consts_of_expr(&self, e: &Expr, target_type: Type) -> Expr {
        match e {
            Expr::Const(Const::Int(val), p) => match target_type {                
                Type::Bitvector(bv_size) => {
                    match bv_size {
                        BVSize::BV8 => Expr::Const(Const::Bitvector(BVConst::BV8(*val as u8)), p.clone()),
                        BVSize::BV16 => Expr::Const(Const::Bitvector(BVConst::BV16(*val as u16)), p.clone()),
                        BVSize::BV32 => Expr::Const(Const::Bitvector(BVConst::BV32(*val as u32)), p.clone()),
                        BVSize::BV64 => Expr::Const(Const::Bitvector(BVConst::BV64(*val as u64)), p.clone()),
                        BVSize::BV128 => Expr::Const(Const::Bitvector(BVConst::BV128(*val as u128)), p.clone()),
                    }
                },
                _=> unreachable!("{:?}", target_type)
            },
            Expr::Const(Const::BigInt(val_as_str), p) => match target_type {                
                Type::Bitvector(bv_size) => {
                    match bv_size {
                        BVSize::BV8 => {
                            let val= val_as_str.parse::<u8>().unwrap();
                            Expr::Const(Const::Bitvector(BVConst::BV8(val)), p.clone())
                        }
                        BVSize::BV16 => {
                            let val= val_as_str.parse::<u16>().unwrap();
                            Expr::Const(Const::Bitvector(BVConst::BV16(val)), p.clone())
                        }
                        BVSize::BV32 => {
                            let val= val_as_str.parse::<u32>().unwrap();
                            Expr::Const(Const::Bitvector(BVConst::BV32(val)), p.clone())
                        }
                        BVSize::BV64 => {
                            let val= val_as_str.parse::<u64>().unwrap();
                            Expr::Const(Const::Bitvector(BVConst::BV64(val)), p.clone())
                        }
                        BVSize::BV128 => {
                            println!("{}", val_as_str);
                            let val_i= val_as_str.parse::<i128>().unwrap();
                            let val: u128 = unsafe { std::mem::transmute(val_i) };
                            Expr::Const(Const::Bitvector(BVConst::BV128(val)), p.clone())
                        }
                    }
                },
                _=> unreachable!()
            },
            Expr::BinOp(kind, left, right, p) => {
                let new_left = Box::from(self.replace_tainted_consts_of_expr(left, target_type.clone()));
                let new_right = Box::from(self.replace_tainted_consts_of_expr(right, target_type));
                Expr::BinOp(kind.clone(), new_left, new_right, p.clone())            
            }
            e => e.clone()
        }
    }
    
    pub fn get_used_bitvector_fields(&mut self) {
        for rep in self.replacements.values() {
            match rep {
                Expr::Field(_, f, _) => { self.new_fields.insert(f.clone()); },
                _ => ()              
            }
        }
    }

    pub fn used_predicates(&self) -> HashSet<vir::Predicate> {
        let mut predicates: HashSet<vir::Predicate> = HashSet::new();
        let pred_names = self.new_predicates.clone();
        for p_name in pred_names {
            let typ = bv_str_to_typ(p_name.clone()); 
            let this = LocalVar {
                name: "self".to_string(),
                typ: Type::TypedRef(p_name.clone()),
            };
            let body = Some(
                Expr::BinOp(
                    BinOpKind::And,
                    box Expr::FieldAccessPredicate(
                        box Expr::Field(
                            box Expr::Local(
                                this.clone(),
                                Position::default()
                            ),
                            Field {
                                name: format!("val_{}", p_name),
                                typ: typ.clone()
                            },
                            Position::default()
                        ),
                        PermAmount::Write,
                        Position::default()
                    ),
                    box Expr::Const(Const::Bool(true), Position::default()),
                    Position::default()
                )
            );
            let new_pred_def = 
                vir::Predicate::Struct(
                    StructPredicate {
                        name: p_name,
                        this: this,
                        body: body,
                    }
                );
            predicates.insert(new_pred_def);
        }
        predicates
    }

    fn dump_method(&self, label: &str) {
        let f_name = format!("/tmp/{}_{}_replacement.vpr", self.method.get_identifier(), label);
        let mut w = File::create(f_name.clone()).unwrap();
        for blk in &self.method.basic_blocks { 
            for stmt in &blk.stmts {
                writeln!(&mut w, "{}", stmt).unwrap();
            }
        }
        println!("Dumped method to {}", f_name.clone());
    }

}

pub fn add_bitvector_fields(_methods: Vec<CfgMethod>) -> Vec<Field> {
    let mut new_fields: HashSet<Field> = HashSet::new();
    
    new_fields.insert(Field { name: "val_bv8".to_string(), typ: Type::Bitvector(BVSize::BV8) });

    Vec::from_iter(new_fields)
}

fn convert_ref_type_string(s:String) -> (String, Type) {
    if s.eq(&String::from("u8")) || s.eq(&String::from("i8")) {
        (String::from("bv8"), Type::Bitvector(BVSize::BV8))
    } else if s.eq(&String::from("u16")) || s.eq(&String::from("i16")) {
        (String::from("bv16"), Type::Bitvector(BVSize::BV16))
    } else if s.eq(&String::from("u32")) || s.eq(&String::from("i32")) {
        (String::from("bv32"), Type::Bitvector(BVSize::BV32))
    } else if s.eq(&String::from("u64")) || s.eq(&String::from("i64")) {
        (String::from("bv64"), Type::Bitvector(BVSize::BV64))
    } else if s.eq(&String::from("u128")) || s.eq(&String::from("i128")) {
        (String::from("bv128"), Type::Bitvector(BVSize::BV128))
    } else {
        convert_tuple_ref_type_string(s)
    }
}

fn convert_tuple_ref_type_string(s:String) -> (String, Type) {
    let parts = s.split('$');
    for p in parts {
        if p.eq(&String::from("u8")) || p.eq(&String::from("i8")) {
            return (String::from("bv8"), Type::Bitvector(BVSize::BV8))
        } else if p.eq(&String::from("u16")) || p.eq(&String::from("i16")) {
            return (String::from("bv16"), Type::Bitvector(BVSize::BV16))
        } else if p.eq(&String::from("u32")) || p.eq(&String::from("i32")) {
            return (String::from("bv32"), Type::Bitvector(BVSize::BV32))
        } else if p.eq(&String::from("u64")) || p.eq(&String::from("i64")) {
            return (String::from("bv64"), Type::Bitvector(BVSize::BV64))
        } else if p.eq(&String::from("u128")) || p.eq(&String::from("i128")) {
            return (String::from("bv128"), Type::Bitvector(BVSize::BV128))
        }
    }
    (s.clone(), Type::Bitvector(BVSize::BV8))
}

fn bv_str_to_typ(s:String) -> Type {
    if s.eq(&String::from("bv8")) { Type::Bitvector(BVSize::BV8) } 
    else if s.eq(&String::from("bv16")) { Type::Bitvector(BVSize::BV16) }
    else if s.eq(&String::from("bv32")) { Type::Bitvector(BVSize::BV32) }
    else if s.eq(&String::from("bv64")) { Type::Bitvector(BVSize::BV64) } 
    else if s.eq(&String::from("bv128")) { Type::Bitvector(BVSize::BV128) }
    else { unreachable!("invalid bitvector type str: {}", s) }
}

fn stmt_contains_bw_op(s:Stmt) -> bool {
    match s {
        Stmt::Inhale(e)
        |Stmt::Exhale(e, _)
        |Stmt::Assert(e, _)
        |Stmt::ApplyMagicWand(e, _)
        |Stmt::Obtain(e, _)
        |Stmt::Downcast(e, _) => expr_contains_bw_op(e),
        
        Stmt::Assign(e1, e2, _)
        |Stmt::TransferPerm(e1, e2, _) => expr_contains_bw_op(e1) || expr_contains_bw_op(e2),

        Stmt::Fold(_, es, _, _, _) 
        |Stmt::Unfold(_, es, _, _)
        |Stmt::MethodCall(_, es, _) => es.iter().fold(false, |x, e| x || expr_contains_bw_op(e.clone())),
                
        Stmt::PackageMagicWand(e, stmts, _, _, _) => {
            expr_contains_bw_op(e) || stmts.iter().fold(false, |x, s| x || stmt_contains_bw_op(s.clone()))
        }        
        Stmt::If(e, stmts1, stmts2) => {
            expr_contains_bw_op(e)
            || stmts1.iter().fold(false, |x, s| x || stmt_contains_bw_op(s.clone()))
            || stmts2.iter().fold(false, |x, s| x || stmt_contains_bw_op(s.clone()))
        }   
        _ => false,
    }
}

fn expr_contains_bw_op(e:Expr) -> bool {
    match e {
        Expr::BinOp(op_kind, e1, e2, _) => {
            match op_kind {
                ast::BinOpKind::BitAnd
                |ast::BinOpKind::BitOr
                |ast::BinOpKind::BitXor
                |ast::BinOpKind::Shl
                |ast::BinOpKind::LShr
                |ast::BinOpKind::AShr => true,
                _ => expr_contains_bw_op(*e1) || expr_contains_bw_op(*e2)
            }
        }

        Expr::Variant(e, _, _)
        |Expr::Field(e, _, _)
        |Expr::AddrOf(e, _, _)
        |Expr::LabelledOld(_, e, _)
        |Expr::PredicateAccessPredicate(_, e, _, _)
        |Expr::FieldAccessPredicate(e, _, _)
        |Expr::UnaryOp(_, e, _)
        |Expr::SnapApp(e, _)
        |Expr::ForAll(_, _, e, _) => expr_contains_bw_op(*e),

        Expr::MagicWand(e1, e2, _, _)
        |Expr::ContainerOp(_, e1, e2, _)
        |Expr::LetExpr(_, e1, e2, _)
        |Expr::InhaleExhale(e1, e2, _)
        |Expr::Downcast(e1, e2, _) => expr_contains_bw_op(*e1) || expr_contains_bw_op(*e2),        
        
        Expr::Seq(_, es, _)
        |Expr::FuncApp(_, es, _, _, _)
        |Expr::DomainFuncApp(_, es, _) => es.iter().fold(false, |x, e| x || expr_contains_bw_op(e.clone())),

        Expr::Unfolding(_, es, e, _, _, _) => {
            es.iter().fold(false, |x, ex| x || expr_contains_bw_op(ex.clone())) || expr_contains_bw_op(*e)
        }

        Expr::Cond(e1, e2, e3, _) => {
            expr_contains_bw_op(*e1) || expr_contains_bw_op(*e2) || expr_contains_bw_op(*e3)
        }
        _ => false
    }
}

// helper functions
fn fields_of_stmt(s: &Stmt) -> HashSet<Expr> {
    let mut fields: HashSet<Expr> = HashSet::new();
    match s {
        Stmt::Assign(e1, e2, _) => {
            let mut acc = fields_of_expr(e1);
            acc.extend(fields_of_expr(e2));
            fields.extend(acc);

        },
        _ => () 
    }
    return fields
}

fn fields_of_expr(e: &Expr) -> HashSet<Expr> {
    let mut fields: HashSet<Expr> = HashSet::new();

    match e {
        Expr::UnaryOp(_, e, _) => {
            fields.extend(fields_of_expr(e));
        }
        Expr::BinOp(_, e1, e2, _) => {            
            let mut acc = fields_of_expr(e1);
            acc.extend(fields_of_expr(e2));
            fields.extend(acc);
        }
        Expr::Variant(e, f, p) |
        Expr::Field(e, f, p) => {
            match &**e {
                Expr::Field(fe, ff, fp) => {
                    fields.insert(Expr::Field(fe.clone(), ff.clone(), fp.clone()));
                }
                _ => ()
            }

            fields.insert(Expr::Field(e.clone(), f.clone(), p.clone()));
        }
        Expr::Local(lv, p) => {
            fields.insert(
                Expr::Field(
                    box Expr::Local(lv.clone(), p.clone()),
                    Field {name:"val_int".to_string(), typ: Type::Int},
                    p.clone()
                )
            );
        }
        _ => ()
    }
    return fields
}

fn replace_tuple_field_type(t_ref: String, pos: u8, new_ty: String) -> String {

    let pos_in_str = (pos as usize) + 1;
    let tuple_types:Vec<&str> = t_ref.split('$').collect::<Vec<_>>();
    assert!((pos as usize) < tuple_types.len());

    let mut new_ref_types: String = "".into();
    for i in 0..(tuple_types.len()) {
        if i == 0 {
            new_ref_types.push_str(&tuple_types.get(i).unwrap())
        } else if i == pos_in_str {
            new_ref_types.push_str("$");
            new_ref_types.push_str(&new_ty)
        } else {
            new_ref_types.push_str("$");
            new_ref_types.push_str(&tuple_types.get(i).unwrap())
        }
    }
    new_ref_types
}

fn get_target_type(fields: HashSet<Expr>) -> Type {        
    let mut cand_types: Vec<Type> = Vec::new();
    for f in fields {
        match f {
            Expr::Field(_, f_field, _) => {
                match f_field.typ {
                    Type::TypedRef(name) => {
                        let (_, typ) = convert_ref_type_string(name);
                        cand_types.push(typ);
                    },
                    Type::Bitvector(_) => cand_types.push(f_field.typ),
                    _ => ()
                }
            },
            _ => ()
        }
    }    
    for t in cand_types.clone() {
        match t {
            Type::Bitvector(_) => return t,
            _ => ()
        }
    }
    unreachable!("Could not find a valid target type in {:?}", cand_types);
}