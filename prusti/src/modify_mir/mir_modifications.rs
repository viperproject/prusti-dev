use super::{mir_helper::*, passes::PledgeToProcess};

use prusti_rustc_interface::{
    index::IndexVec,
    middle::{
        mir::{
            self, patch::MirPatch, BasicBlock, BasicBlockData, Constant, Operand, Place,
            Terminator, TerminatorKind,
        },
        ty::{self, TyCtxt, TyKind},
    },
    span::{def_id::DefId, DUMMY_SP},
};

use std::{cell::RefMut, u128};

/// A general set of operations that are used to modify the MIR
pub trait MirModifier<'tcx> {
    // to be implemented!
    fn tcx(&self) -> TyCtxt<'tcx>;
    fn patcher(&self) -> RefMut<MirPatch<'tcx>>;
    fn def_id(&self) -> DefId;
    fn local_decls(&self) -> &IndexVec<mir::Local, mir::LocalDecl<'tcx>>;

    fn prepend_call(
        &self,
        fn_id: DefId,
        caller_block: BasicBlock,
        args: Vec<Operand<'tcx>>,
        generics: ty::GenericArgsRef<'tcx>,
        terminator: Terminator<'tcx>,
        dest_place: Place<'tcx>,
    ) -> BasicBlock {
        // get the bodies of the store and check function
        let new_block_data = BasicBlockData::new(Some(terminator));
        let new_block = self.patcher().new_block(new_block_data);

        let func_ty = self.tcx().mk_ty_from_kind(TyKind::FnDef(fn_id, generics));
        let func = Operand::Constant(Box::new(Constant {
            span: DUMMY_SP,
            user_ty: None,
            literal: mir::ConstantKind::zero_sized(func_ty),
        }));

        let call_terminator = TerminatorKind::Call {
            func,
            args: args.clone(),
            destination: dest_place,
            target: Some(new_block),
            // is terminating on unwind sometimes not actually what we want?
            unwind: mir::UnwindAction::Continue,
            call_source: mir::CallSource::Normal,
            fn_span: DUMMY_SP,
        };
        self.patcher()
            .patch_terminator(caller_block, call_terminator);
        new_block
    }

    // given a set of arguments, and the type that the old tuple should have
    // create a chain of basic blocks that clones each of the arguments
    // and puts them into a tuple
    fn prepend_old_cloning(
        &self,
        terminator: Terminator<'tcx>,
        old_dest_place: mir::Place<'tcx>,
        old_ty: ty::Ty<'tcx>,
        args: Vec<Operand<'tcx>>,
        clones_passed_into_function: bool,
    ) -> (BasicBlock, BasicBlock, Vec<mir::Local>) {
        let new_block_data = BasicBlockData::new(Some(terminator));
        let current_caller = self.patcher().new_block(new_block_data);
        let mut current_target = current_caller;

        let mut old_tuple = Vec::new();
        let old_tuple_fields = old_ty.tuple_fields();

        let mut locals_to_drop = Vec::new();
        for (id, operand) in args.iter().enumerate() {
            let old_values_ty = old_tuple_fields.get(id).unwrap();
            if old_values_ty.is_unit() {
                // we already know from ast, that this variable does not need
                // to be cloned
                let unit_const = unit_const(self.tcx());
                old_tuple.push(unit_const);
            } else {
                match operand {
                    mir::Operand::Constant(_) => {
                        old_tuple.push(operand.clone());
                    }
                    mir::Operand::Move(place) | mir::Operand::Copy(place) => {
                        let target_ty = Some(old_tuple_fields[id]);
                        // prepends clone blocks before the actual function is called
                        let (start_block, destination, to_drop) = self
                            .insert_clone_argument(
                                *place,
                                current_target,
                                None,
                                target_ty,
                                clones_passed_into_function,
                            )
                            .unwrap();
                        if let Some(to_drop) = to_drop {
                            locals_to_drop.push(to_drop);
                        }
                        current_target = start_block;
                        // add the result to our tuple:
                        old_tuple.push(mir::Operand::Move(destination.into()));
                    }
                }
            }
        }
        let old_rvalue = mir::Rvalue::Aggregate(
            Box::new(mir::AggregateKind::Tuple),
            IndexVec::from_raw(old_tuple),
        );
        let stmt_kind = mir::StatementKind::Assign(Box::new((old_dest_place, old_rvalue)));
        let location = mir::Location {
            block: current_caller,
            statement_index: 0,
        };
        self.patcher().add_statement(location, stmt_kind);

        // (start of clone-chain, block calling annotated function)
        (current_target, current_caller, locals_to_drop)
    }

    fn insert_clone_argument(
        &self,
        arg: mir::Place<'tcx>,
        target: BasicBlock,
        destination: Option<mir::Local>,
        target_type_opt: Option<ty::Ty<'tcx>>,
        results_dropped_by_function: bool,
    ) -> Result<(BasicBlock, mir::Local, Option<mir::Local>), ()> {
        // if we deal with a reference, we can directly call clone on it
        // otherwise we have to create a reference first, to pass to the clone
        // function.
        let clone_defid = get_clone_defid(self.tcx()).ok_or(())?;
        let param_env = self.tcx().param_env(self.def_id());
        // let clone_trait_defid = self.tcx.lang_items().clone_trait().unwrap();
        //
        let arg_ty = if let Some(target_type) = target_type_opt {
            target_type
        } else {
            arg.ty(self.local_decls(), self.tcx()).ty
        };
        let mutable_ref = matches!(arg_ty.ref_mutability(), Some(mir::Mutability::Mut));
        println!("arg type: {:?}", arg_ty);

        let dest = destination.unwrap_or_else(|| self.patcher().new_temp(arg_ty, DUMMY_SP));
        println!(
            "trying to clone arg: {:?} into destination: {:?}",
            arg, dest
        );
        if !arg_ty.is_ref() {
            // non-ref arg means we first deref and then clone.
            // destination only needs to be dropped if it's not later passed into
            // a function that drops it
            let to_drop = (!results_dropped_by_function
                && arg_ty.needs_drop(self.tcx(), param_env))
            .then_some(dest);
            let ref_ty = create_reference_type(self.tcx(), arg_ty);
            let ref_arg = self.patcher().new_temp(ref_ty, DUMMY_SP);
            // add a statement to deref the old_argument
            let rvalue = rvalue_reference_to_local(self.tcx(), arg, false);
            // the statement to be added to the block that has the call clone
            // terminator
            let ref_stmt =
                mir::StatementKind::Assign(Box::new((mir::Place::from(ref_arg), rvalue)));

            // create the substitution since clone is generic:
            let generics = self.tcx().mk_args(&[ty::GenericArg::from(arg_ty)]);
            // create the function operand:
            let clone_args = vec![Operand::Move(mir::Place::from(ref_arg))];
            // create a new basicblock:
            // TODO: make part of new mir helper too
            let (new_block, _) = self.create_call_block(
                clone_defid,
                clone_args,
                generics,
                Some(dest.into()),
                Some(target),
            )?;
            self.patcher().add_statement(
                mir::Location {
                    block: new_block,
                    statement_index: 0,
                },
                ref_stmt,
            );

            Ok((new_block, dest, to_drop))
            // let block_data = BasicBlockData::new()
        } else {
            // create a new local to store the result of clone:
            let deref_ty = arg_ty.builtin_deref(false).ok_or(())?.ty;
            let clone_dest = self.patcher().new_temp(deref_ty, DUMMY_SP);
            let to_drop = deref_ty
                .needs_drop(self.tcx(), param_env)
                .then_some(clone_dest);

            println!(
                "dereferenced type: {:?}, needs drop? {:?}",
                deref_ty, to_drop
            );
            let generics = self.tcx().mk_args(&[ty::GenericArg::from(deref_ty)]);
            let clone_args = vec![Operand::Move(arg)];
            // add an additional simple block afterwards, that dereferences
            // the the cloned value into the original receiver of old:
            // create it beforehand, so we can set the precedors target correctly
            let terminator = mir::Terminator {
                source_info: dummy_source_info(),
                kind: TerminatorKind::Goto { target },
            };
            let block_data = BasicBlockData::new(Some(terminator));
            let second_block = self.patcher().new_block(block_data);

            // borrow the clone result
            let rvalue = rvalue_reference_to_local(self.tcx(), clone_dest.into(), mutable_ref);
            let ref_stmt = mir::StatementKind::Assign(Box::new((dest.into(), rvalue)));
            self.patcher().add_statement(
                mir::Location {
                    block: second_block,
                    statement_index: 0,
                },
                ref_stmt,
            );

            let (new_block, _) = self.create_call_block(
                clone_defid,
                clone_args,
                generics,
                Some(clone_dest.into()),
                Some(second_block),
            )?;

            Ok((new_block, dest, to_drop))
        }
    }

    fn create_pledge_call_chain(
        &self,
        pledge: &PledgeToProcess<'tcx>,
        target: BasicBlock,
    ) -> Result<(BasicBlock, BasicBlock), ()> {
        // given a location, insert the call chain to check a pledge:
        // since we need to know the targets for each call, the blocks need to be created
        // in reversed order.

        // annoying, but we have to create a block to start off the dropping chain
        // early.. Even though at this point we don't know which locals we will
        // have to drop
        let drop_start_term = Terminator {
            source_info: dummy_source_info(),
            kind: TerminatorKind::Goto { target },
        };
        let drop_block_data = BasicBlockData::new(Some(drop_start_term));
        let drop_block = self.patcher().new_block(drop_block_data);

        // Create call to check function:
        let mut check_args = pledge.args.clone();
        check_args.push(mir::Operand::Move(pledge.result_copy_place)); //result arg
        check_args.push(mir::Operand::Move(pledge.old_values_place));
        check_args.push(mir::Operand::Move(pledge.before_expiry_place));
        let (check_after_block, _) = self.create_call_block(
            pledge.check,
            check_args,
            pledge.generics,
            None,
            Some(drop_block),
        )?;

        // If there is a check_before_expiry block, creat it
        let next_target = if let Some(check_before_expiry) = pledge.check_before_expiry {
            let before_check_args = vec![
                mir::Operand::Move(pledge.result_copy_place),
                mir::Operand::Move(pledge.old_values_place),
            ];
            let (new_block, _) = self.create_call_block(
                check_before_expiry,
                before_check_args,
                pledge.generics,
                None,
                Some(check_after_block),
            )?;
            new_block
        } else {
            check_after_block
        };

        // clone the result of the pledge, so it can be referred to with before_expiry
        let terminator = mir::Terminator {
            source_info: dummy_source_info(),
            kind: mir::TerminatorKind::Goto {
                target: next_target,
            },
        };
        let (clone_chain_start, _, locals_to_drop_before_expiry) = self.prepend_old_cloning(
            terminator,
            pledge.before_expiry_place,
            pledge.before_expiry_ty,
            vec![mir::Operand::Move(pledge.result_copy_place)],
            true, // this clone will be passed to a check function
        );
        // so far we can only drop the values created for before_expiry
        let (drop_chain_start, _) =
            self.create_drop_chain(locals_to_drop_before_expiry, Some(target));
        // adjust the check block's terminator
        self.patcher().patch_terminator(
            drop_block,
            mir::TerminatorKind::Goto {
                target: drop_chain_start,
            },
        );

        // wrap an `if pledge_guard around the whole thing`
        let term_switchint = mir::TerminatorKind::SwitchInt {
            discr: mir::Operand::Copy(pledge.guard_place),
            targets: mir::terminator::SwitchTargets::new(
                [(u128::MIN, target)].into_iter(),
                clone_chain_start,
            ),
        };
        let terminator = mir::Terminator {
            source_info: dummy_source_info(),
            kind: term_switchint,
        };
        let check_guard_block = mir::BasicBlockData::new(Some(terminator));
        let start_block = self.patcher().new_block(check_guard_block);
        let unset_guard_stmt = self.set_bool_stmt(pledge.guard_place, false);
        self.patcher().add_statement(
            mir::Location {
                block: clone_chain_start,
                statement_index: 0,
            },
            unset_guard_stmt,
        );
        Ok((start_block, drop_block))
    }

    /// Create a chain of drop calls to drop the provided list of locals.
    /// If there are no locals to drop, this function simply returns `target`
    /// If there is no target, we return after dropping all values
    fn create_drop_chain(
        &self,
        locals_to_drop: Vec<mir::Local>,
        target_opt: Option<BasicBlock>,
    ) -> (BasicBlock, BasicBlock) {
        let target = if let Some(target) = target_opt {
            target
        } else {
            // create a return block:
            let terminator = mir::Terminator {
                source_info: dummy_source_info(),
                kind: mir::TerminatorKind::Return,
            };
            let block_data = mir::BasicBlockData::new(Some(terminator));
            self.patcher().new_block(block_data)
        };
        let last_block = target;
        let mut current_target = target;
        for local in locals_to_drop.iter() {
            let terminator = mir::Terminator {
                source_info: dummy_source_info(),
                kind: mir::TerminatorKind::Drop {
                    place: (*local).into(),
                    target: current_target,
                    unwind: mir::UnwindAction::Continue,
                    replace: false,
                },
            };
            let block_data = mir::BasicBlockData::new(Some(terminator));
            current_target = self.patcher().new_block(block_data);
        }
        (current_target, last_block)
    }

    /// Create a call block to the function with the given def_id.
    ///
    /// * `call_id`: DefId of the called function
    /// * `args`: arguments passed to the function
    /// * `generics`: generic arguments passed to the function
    /// * `destination`: where the functions result should be stored. If None, a new
    /// local will be created
    /// * `target`: the basic block where function should jump to after returning
    ///
    /// returns (id of new basic block, destination)
    fn create_call_block(
        &self,
        call_id: DefId,
        args: Vec<mir::Operand<'tcx>>,
        generics: ty::GenericArgsRef<'tcx>,
        destination: Option<mir::Place<'tcx>>,
        target: Option<mir::BasicBlock>,
    ) -> Result<(mir::BasicBlock, mir::Place<'tcx>), ()> {
        // construct the function call
        let func_ty = self
            .tcx()
            .mk_ty_from_kind(ty::TyKind::FnDef(call_id, generics));
        let func = mir::Operand::Constant(Box::new(mir::Constant {
            span: DUMMY_SP,
            user_ty: None,
            literal: mir::ConstantKind::zero_sized(func_ty),
        }));
        // either use passed destination or create a new one
        let destination = destination.unwrap_or_else(|| {
            // find return type
            let ret_ty = fn_signature(self.tcx(), call_id, Some(generics)).output();
            mir::Place::from(self.patcher().new_temp(ret_ty, DUMMY_SP))
        });

        // args have to be constructed beforehand, including result or old_values
        let terminator_kind = mir::TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind: mir::UnwindAction::Continue,
            call_source: mir::CallSource::Normal,
            fn_span: self.tcx().def_span(call_id),
        };
        let terminator = mir::Terminator {
            source_info: dummy_source_info(),
            kind: terminator_kind,
        };
        let blockdata = mir::BasicBlockData::new(Some(terminator));
        let new_block_id = self.patcher().new_block(blockdata);

        Ok((new_block_id, destination))
    }

    /// Create a statement that assigns a boolean to a given destination
    fn set_bool_stmt(
        &self,
        destination: mir::Place<'tcx>,
        value: bool,
    ) -> mir::StatementKind<'tcx> {
        let const_kind = mir::ConstantKind::from_bool(self.tcx(), value);
        let const_true = mir::Constant {
            span: DUMMY_SP,
            user_ty: None,
            literal: const_kind,
        };
        let rhs = mir::Rvalue::Use(mir::Operand::Constant(Box::new(const_true)));
        mir::StatementKind::Assign(Box::new((destination, rhs)))
    }
}
