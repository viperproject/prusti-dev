// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use viper::{self, Viper, Stmt, Expr, VerificationError, CfgMethod};
use viper::{Domain, Field, Function, Predicate, Method};
use viper::AstFactory;
use rustc::mir;
use rustc::ty;
use prusti_interface::environment::ProcedureImpl;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::Environment;
use prusti_interface::environment::Procedure;
use std::collections::HashMap;
use viper::CfgBlockIndex;
use prusti_interface::environment::BasicBlockIndex;
use rustc::mir::TerminatorKind;
use viper::Successor;
use rustc::middle::const_val::{ConstInt, ConstVal};
use encoder::Encoder;
use encoder::borrows::compute_borrow_infos;
use encoder::utils::*;
use rustc_data_structures::indexed_vec::Idx;
use rustc::ty::layout::LayoutOf;

pub struct ProcedureEncoder<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
    proc_def_id: ProcedureDefId,
    procedure: &'p ProcedureImpl<'a, 'tcx>,
    mir: &'p mir::Mir<'tcx>,
    cfg_method: CfgMethod<'v, 'p>
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> ProcedureEncoder<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>, procedure: &'p ProcedureImpl<'a, 'tcx>) -> Self {
        let mut cfg_method = encoder.cfg_factory().new_cfg_method(
            // method name
            encoder.encode_procedure_name(procedure.get_id()),
            // formal args
            vec![],
            // formal returns
            vec![],
            // local vars
            vec![],
        );

        ProcedureEncoder {
            encoder,
            proc_def_id: procedure.get_id(),
            procedure,
            mir: procedure.get_mir(),
            cfg_method
        }
    }

    fn encode_statement(&mut self, stmt: &mir::Statement<'tcx>) -> Vec<Stmt<'v>> {
        trace!("Encode statement '{:?}'", stmt);

        match stmt.kind {
            mir::StatementKind::StorageDead(_) |
            mir::StatementKind::StorageLive(_) => vec![],

            mir::StatementKind::Assign(ref lhs, ref rhs) => {
                let (encoded_lhs, _, _) = self.encode_place(lhs);
                let (encoded_value, side_effects) = match rhs {
                    &mir::Rvalue::Use(ref operand) => {
                        self.encode_operand(operand)
                    },

                    ref x => unimplemented!("{:?}", x)
                };
                let mut stmts = side_effects.clone();
                if (self.is_place_encoded_as_local_var(lhs)) {
                    stmts.push(
                        self.encoder.ast_factory().local_var_assign(
                            encoded_lhs,
                            encoded_value
                        )
                    );
                } else {
                    stmts.push(
                        self.encoder.ast_factory().field_assign(
                            encoded_lhs,
                            encoded_value
                        )
                    );
                }
                stmts
            },

            ref x => unimplemented!("{:?}", x)
        }
    }

    fn encode_terminator(&mut self, term: &mir::Terminator<'tcx>,
                         cfg_blocks: &HashMap<BasicBlockIndex, CfgBlockIndex>,
                         spec_cfg_block: CfgBlockIndex,
                         abort_cfg_block: CfgBlockIndex,
                         return_cfg_block: CfgBlockIndex) -> (Vec<Stmt<'v>>, Successor<'v>) {
        trace!("Encode terminator '{:?}'", term);
        let ast = self.encoder.ast_factory();

        match term.kind {
            TerminatorKind::Return => (vec![], Successor::Goto(return_cfg_block)),

            TerminatorKind::Goto { target } => {
                let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                (vec![], Successor::Goto(*target_cfg_block))
            },

            TerminatorKind::SwitchInt { ref targets, ref discr, ref values, switch_ty } => {
                trace!("SwitchInt ty '{:?}', discr '{:?}', values '{:?}'", switch_ty, discr, values);
                let mut stmts: Vec<Stmt> = vec![];
                let mut cfg_targets: Vec<(Expr, CfgBlockIndex)> = vec![];
                for (i, value) in values.iter().enumerate() {
                    let target = targets[i as usize];
                    // Convert int to bool, if required
                    let viper_guard = if (switch_ty.sty == ty::TypeVariants::TyBool) {
                        if const_int_is_zero(value) {
                            // If discr is 0 (false)
                            ast.not(self.eval_operand(discr))
                        } else {
                            // If discr is not 0 (true)
                            self.eval_operand(discr)
                        }
                    } else {
                        ast.eq_cmp(
                            self.eval_operand(discr),
                            self.encoder.eval_const_int(value)
                        )
                    };
                    let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                    cfg_targets.push((viper_guard, *target_cfg_block))
                }
                let default_target = targets[values.len()];
                let cfg_default_target = cfg_blocks.get(&default_target).unwrap_or(&spec_cfg_block);
                (vec![], Successor::GotoSwitch(cfg_targets, *cfg_default_target))
            },

            TerminatorKind::Unreachable => (vec![], Successor::Unreachable),

            TerminatorKind::Abort => (vec![], Successor::Goto(abort_cfg_block)),

            TerminatorKind::Drop { ref target, unwind, .. } => {
                let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                (vec![], Successor::Goto(*target_cfg_block))
            },

            TerminatorKind::FalseEdges { ref real_target, ref imaginary_targets } => {
                let target_cfg_block = cfg_blocks.get(&real_target).unwrap_or(&spec_cfg_block);
                (vec![], Successor::Goto(*target_cfg_block))
            },

            TerminatorKind::FalseUnwind { real_target, unwind } => {
                let target_cfg_block = cfg_blocks.get(&real_target).unwrap_or(&spec_cfg_block);
                (vec![], Successor::Goto(*target_cfg_block))
            },

            TerminatorKind::DropAndReplace { ref target, unwind, ref location, ref value } => {
                let (encoded_loc, _, _) = self.encode_place(location);
                let (encoded_value, side_effects) = self.encode_operand(value);
                let mut stmts = vec![];
                stmts.extend(side_effects);
                if (self.is_place_encoded_as_local_var(location)) {
                    stmts.push(
                        ast.local_var_assign(encoded_loc, encoded_value)
                    );
                } else {
                    stmts.push(
                        ast.field_assign(encoded_loc, encoded_value)
                    );
                }
                let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                (stmts, Successor::Goto(*target_cfg_block))
            },

            TerminatorKind::Call {
                ref args,
                ref destination,
                func: mir::Operand::Constant(
                    box mir::Constant {
                        literal: mir::Literal::Value {
                            value: &ty::Const {
                                val: ConstVal::Function(def_id, _),
                                ..
                            }
                        },
                        ..
                    }
                ),
                ..
            } => {
                let ast = self.encoder.ast_factory();
                let func_proc_name = self.encoder.env().get_item_name(def_id);
                let mut stmts;
                if (func_proc_name == "prusti_contracts::internal::__assertion") {
                    // This is a Prusti loop invariant
                    panic!("Unreachable");
                } else if (func_proc_name == "std::rt::begin_panic") {
                    // This is called when a Rust assertion fails
                    stmts = vec![ast.assert_with_comment(
                        ast.false_lit(),
                        ast.no_position(),
                        &format!("Rust panic - {:?}: ", args[0])
                    )];
                } else {
                    stmts = vec![];
                    let mut encoded_args: Vec<Expr> = vec![];

                    for operand in args.iter() {
                        let (encoded, side_effects) = self.encode_operand(operand);
                        encoded_args.push(encoded);
                        stmts.extend(side_effects);
                    }

                    let encoded_target: Vec<Expr> = destination.iter().map(|d| self.encode_place(&d.0).0).collect();

                    stmts.push(ast.method_call(
                        &self.encoder.encode_procedure_name(def_id),
                        &encoded_args,
                        &encoded_target
                    ));
                }

                if let &Some((_, target)) = destination {
                    let target_cfg_block = cfg_blocks.get(&target).unwrap_or(&spec_cfg_block);
                    (stmts, Successor::Goto(*target_cfg_block))
                } else {
                    (stmts, Successor::Unreachable)
                }
            },

            TerminatorKind::Call { .. } => {
                // Other kind of calls?
                unimplemented!()
            },

            TerminatorKind::Assert { ref cond, expected, ref target, .. } => {
                trace!("Assert cond '{:?}', expected '{:?}'", cond, expected);
                let mut stmts: Vec<Stmt> = vec![];
                let viper_guard = if (expected) {
                    self.eval_operand(cond)
                } else {
                    ast.not(self.eval_operand(cond))
                };
                let target_cfg_block = *cfg_blocks.get(&target).unwrap();
                (vec![], Successor::GotoSwitch(vec![(viper_guard, target_cfg_block)], abort_cfg_block))
            }

            TerminatorKind::Call { .. } |
            TerminatorKind::Resume |
            TerminatorKind::Assert { .. } |
            TerminatorKind::Yield { .. } |
            TerminatorKind::GeneratorDrop => unimplemented!("{:?}", term.kind),
        }
    }

    pub fn encode(mut self) -> Method<'v> {
        compute_borrow_infos(self.procedure, self.encoder.env().tcx());
        let ast = self.encoder.ast_factory();

        // Formal args
        for local in self.mir.args_iter() {
            let name = self.encode_local_var_name(local);
            self.cfg_method.add_formal_arg(name, ast.ref_type())
        }

        // Formal return
        for local in self.mir.local_decls.indices().take(1) {
            let name = self.encode_local_var_name(local);
            self.cfg_method.add_formal_return(name, ast.ref_type())
        }

        // Local vars
        for local in self.mir.vars_and_temps_iter() {
            let name = self.encode_local_var_name(local);
            self.cfg_method.add_local_var(name, ast.ref_type())
        }

        let mut cfg_blocks: HashMap<BasicBlockIndex, CfgBlockIndex> = HashMap::new();

        // Initialize CFG blocks
        let start_cfg_block = self.cfg_method.add_block("start", vec![], vec![]);

        let mut first_cfg_block = true;
        self.procedure.walk_once_cfg(|bbi, _| {
            let cfg_block = self.cfg_method.add_block(&format!("{:?}", bbi), vec![], vec![]);
            if first_cfg_block {
                self.cfg_method.set_successor(start_cfg_block, Successor::Goto(cfg_block));
                first_cfg_block = false;
            }
            cfg_blocks.insert(bbi, cfg_block);
        });

        let spec_cfg_block = self.cfg_method.add_block("spec", vec![], vec![]);
        self.cfg_method.set_successor(spec_cfg_block, Successor::Unreachable);

        let abort_cfg_block = self.cfg_method.add_block("abort", vec![], vec![]);
        self.cfg_method.set_successor(abort_cfg_block, Successor::Unreachable);

        let return_cfg_block = self.cfg_method.add_block("return", vec![], vec![]);
        self.cfg_method.set_successor(return_cfg_block, Successor::Return);

        // Encode preconditions
        for local in self.mir.args_iter() {
            let ty = self.get_rust_local_ty(local);
            let predicate_name = self.encoder.encode_type_predicate_use(ty);
            let inhale_stmt = ast.inhale(
                ast.predicate_access_predicate(
                    ast.predicate_access(
                        &[
                            self.encode_local(local)
                        ],
                        &predicate_name
                    ),
                    ast.full_perm(),
                ),
                ast.no_position()
            );
            self.cfg_method.add_stmt(start_cfg_block, inhale_stmt);
        }
        self.cfg_method.add_stmt(start_cfg_block, ast.label("precondition", &[]));

        // Encode postcondition
        for local in self.mir.local_decls.indices().take(1) {
            let ty = self.get_rust_local_ty(local);
            let predicate_name = self.encoder.encode_type_predicate_use(ty);
            let exhale_stmt = ast.exhale(
                ast.predicate_access_predicate(
                    ast.predicate_access(
                        &[
                            self.encode_local(local)
                        ],
                        &predicate_name
                    ),
                    ast.full_perm(),
                ),
                ast.no_position()
            );
            self.cfg_method.add_stmt(return_cfg_block, exhale_stmt);
        }

        // Encode statements
        self.procedure.walk_once_cfg(|bbi, bb_data| {
            let statements: &Vec<mir::Statement<'tcx>> = &bb_data.statements;
            let mut viper_statements: Vec<Stmt> = vec![];

            // Encode statements
            for (stmt_index, stmt) in statements.iter().enumerate() {
                trace!("Encode statement {:?}:{}", bbi, stmt_index);
                let stmts = self.encode_statement(stmt);
                let cfg_block = *cfg_blocks.get(&bbi).unwrap();
                for stmt in stmts.into_iter() {
                    self.cfg_method.add_stmt(cfg_block, stmt);
                }
            }
        });

        // Encode terminators and set CFG edges
        self.procedure.walk_once_cfg(|bbi, bb_data| {
            if let Some(ref term) = bb_data.terminator {
                trace!("Encode terminator of {:?}", bbi);
                let (stmts, successor) = self.encode_terminator(
                    term,
                    &cfg_blocks,
                    spec_cfg_block,
                    abort_cfg_block,
                    return_cfg_block
                );
                let cfg_block = *cfg_blocks.get(&bbi).unwrap();
                for stmt in stmts.into_iter() {
                    self.cfg_method.add_stmt(cfg_block, stmt);
                }
                self.cfg_method.set_successor(cfg_block, successor);
            }
        });

        self.cfg_method.to_ast().ok().unwrap()
    }

    fn get_rust_local_decl(&self, local: mir::Local) -> &mir::LocalDecl<'tcx> {
        &self.mir.local_decls[local]
    }

    fn get_rust_local_ty(&self, local: mir::Local) -> ty::Ty<'tcx> {
        self.get_rust_local_decl(local).ty
    }

    fn encode_local_var_name(&self, local: mir::Local) -> String {
        let local_decl = self.get_rust_local_decl(local);
        match local_decl.name {
            Some(ref name) => format!("{:?}", name),
            None => format!("{:?}", local)
        }
    }

    fn encode_local(&self, local: mir::Local) -> Expr<'v> {
        let var_name = self.encode_local_var_name(local);
        let var_type = self.encoder.ast_factory().ref_type();
        self.encoder.ast_factory().local_var(&var_name, var_type)
    }

    fn encode_projection(&self, place_projection: &mir::PlaceProjection<'tcx>) -> (Expr<'v>, ty::Ty<'tcx>, Option<usize>) {
        let (encoded_base, base_ty, opt_variant_index) = self.encode_place(&place_projection.base);
        match &place_projection.elem {
            &mir::ProjectionElem::Field(ref field, ty) => {
                match base_ty.sty {
                    ty::TypeVariants::TyBool |
                    ty::TypeVariants::TyInt(_) |
                    ty::TypeVariants::TyUint(_) |
                    ty::TypeVariants::TyRawPtr(_) |
                    ty::TypeVariants::TyRef(_, _) => panic!("Type {:?} has no fields", base_ty),

                    ty::TypeVariants::TyTuple(elems, _) => {
                        let field_name = format!("pos_{}", field.index());
                        let field_ty = elems[field.index()];
                        let encoded_field = self.encoder.encode_field(&field_name, field_ty);
                        let encoded_projection = self.encoder.ast_factory().field_access(encoded_base, encoded_field);
                        (encoded_projection, field_ty, None)
                    },

                    ty::TypeVariants::TyAdt(ref adt_def, ref subst) => {
                        let variant_index = opt_variant_index.unwrap_or(0);
                        let tcx = self.encoder.env().tcx();
                        assert!(variant_index as u64 == adt_def.discriminant_for_variant(tcx, variant_index).to_u64().unwrap());
                        let field = &adt_def.variants[variant_index].fields[field.index()];
                        let num_variants = adt_def.variants.len();
                        let field_name = if (num_variants == 1) {
                            format!("struct_{}", field.name)
                        } else {
                            format!("enum_{}_{}", variant_index, field.name)
                        };
                        let field_ty = tcx.type_of(field.did);
                        let encoded_field = self.encoder.encode_field(&field_name, field_ty);
                        let encoded_projection = self.encoder.ast_factory().field_access(encoded_base, encoded_field);
                        (encoded_projection, field_ty, None)
                    },

                    ref x => unimplemented!("{:?}", x),
                }
            },
            x => unimplemented!("{:?}", x),
        }
    }

    fn encode_place(&self, place: &mir::Place<'tcx>) -> (Expr<'v>, ty::Ty<'tcx>, Option<usize>) {
        match place {
            &mir::Place::Local(local) => (
                self.encode_local(local),
                self.get_rust_local_ty(local),
                None
            ),
            &mir::Place::Projection(ref place_projection) =>
                self.encode_projection(place_projection),
            x => unimplemented!("{:?}", x),
        }
    }

    fn eval_place(&mut self, place: &mir::Place<'tcx>) -> Expr<'v> {
        let (encoded_place, place_ty, opt_variant_index) = self.encode_place(place);
        let value_field = self.encoder.encode_value_field(place_ty);

        self.encoder.ast_factory().field_access(
            encoded_place,
            value_field
        )
    }

    fn is_place_encoded_as_local_var(&self, place: &mir::Place<'tcx>) -> bool {
        match place {
            &mir::Place::Local(local) => true,
            &mir::Place::Projection(_) => false,
            x => unimplemented!("{:?}", x),
        }
    }

    fn eval_operand(&mut self, operand: &mir::Operand<'tcx>) -> Expr<'v> {
        match operand {
            &mir::Operand::Constant(box mir::Constant{ literal: mir::Literal::Value{ value: &ty::Const{ ref val, .. } }, ..}) =>
                self.encoder.eval_const_val(val),
            &mir::Operand::Move(ref place) =>
                self.eval_place(place),
            x => unimplemented!("{:?}", x)
        }
    }

    fn encode_operand(&mut self, operand: &mir::Operand<'tcx>) -> (Expr<'v>, Vec<Stmt<'v>>) {
        match operand {
            &mir::Operand::Move(ref place) => (self.encode_place(place).0, vec![]),
            &mir::Operand::Copy(ref place) =>
                // TODO allocate memory in Viper
                unimplemented!("{:?}", operand),
            &mir::Operand::Constant(box mir::Constant{ literal: mir::Literal::Value{ value: &ty::Const{ ref val, ty } }, ..}) => {
                let ast = self.encoder.ast_factory();
                let fresh_var_name = self.cfg_method.add_fresh_local_var(ast.ref_type());
                let fresh_var = ast.local_var(&fresh_var_name, ast.ref_type());
                let alloc = self.encode_allocation(fresh_var, ty);
                let const_val = self.encoder.eval_const_val(val);
                let field = self.encoder.encode_value_field(ty);
                let assign = ast.field_assign(ast.field_access(fresh_var, field), const_val);
                (fresh_var, vec![alloc, assign])
            },
            x => unimplemented!("{:?}", x)
        }
    }

    fn encode_allocation(&self, lhs: Expr<'v>, ty: ty::Ty<'tcx>) -> Stmt<'v> {
        let field_name_type = self.encoder.encode_type_fields(ty);
        let fields: Vec<Field<'v>> = field_name_type.iter().map(|x| self.encoder.encode_field(&x.0, x.1)).collect();
        self.encoder.ast_factory().new_stmt(
            lhs,
            &fields
        )
    }
}
