//! Code for encoding expressions into snapshots in pure contexts such as domain
//! axioms. Most importantly, this encoding does not use SSA.

use super::common::IntoSnapshotLowerer;
use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        builtin_methods::CallContext,
        lowerer::{FunctionsLowererInterface, Lowerer},
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low::{self as vir_low},
    middle::{self as vir_mid},
};

mod traits;

pub(in super::super::super) use self::traits::{IntoPureBoolExpression, IntoPureSnapshot};

#[derive(Default)]
struct PureSnapshot {
    /// Assume that all pointer accesses are safe.
    assume_pointers_to_be_framed: bool,
}

impl<'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx> for PureSnapshot {
    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl {
            name: variable.name.clone(),
            ty: self.type_to_snapshot(lowerer, &variable.ty)?,
        })
    }

    fn func_app_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        app: &vir_mid::FuncApp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let arguments =
            self.expression_vec_to_snapshot(lowerer, &app.arguments, expect_math_bool)?;
        let return_type = self.type_to_snapshot(lowerer, &app.return_type)?;
        let func_app = lowerer.call_pure_function_in_pure_context(
            app.get_identifier(),
            arguments,
            return_type,
            app.position,
        )?;
        let result = vir_low::Expression::DomainFuncApp(func_app);
        self.ensure_bool_expression(lowerer, &app.return_type, result, expect_math_bool)
    }

    fn labelled_old_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        old: &vir_mid::LabelledOld,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // In pure contexts values cannot be mutated, so `old` has no effect.
        self.expression_to_snapshot(lowerer, &old.base, expect_math_bool)
    }

    fn pointer_deref_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        deref: &vir_mid::Deref,
        base_snapshot: vir_low::Expression,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // FIXME: Delete.
        assert!(self.assume_pointers_to_be_framed);
        eprintln!("deref: {deref}");
        eprintln!("base_snapshot: {base_snapshot}");
        unimplemented!();
    }

    // fn deref_to_snapshot(
    //     &mut self,
    //     lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    //     deref: &vir_mid::Deref,
    //     expect_math_bool: bool,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     let base_snapshot = self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
    //     let ty = deref.base.get_type();
    //     let result = if ty.is_reference() {
    //         lowerer.reference_target_current_snapshot(ty, base_snapshot, deref.position)?
    //     } else {
    //         unreachable!();
    //         // unimplemented!("TODO: to double-check that this is actually used (and in a correct way)");
    //         // This most likely should be unreachable. In axioms we should use snapshot variables
    //         // instead.
    //         // let heap = vir_low::VariableDecl::new("pure_heap$", lowerer.heap_type()?);
    //         // lowerer.pointer_target_snapshot_in_heap(
    //         //     deref.base.get_type(),
    //         //     heap,
    //         //     base_snapshot,
    //         //     deref.position,
    //         // )?
    //         // lowerer.pointer_target_snapshot(
    //         //     deref.base.get_type(),
    //         //     &None,
    //         //     base_snapshot,
    //         //     deref.position,
    //         // )?
    //     };
    //     self.ensure_bool_expression(lowerer, deref.get_type(), result, expect_math_bool)
    // }

    // FIXME: Mark as unreachable.
    fn acc_predicate_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _acc_predicate: &vir_mid::AccPredicate,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        unimplemented!("FIXME: Delete");
        // assert!(self.is_assertion);
        // let expression = match &*acc_predicate.predicate {
        //     vir_mid::Predicate::OwnedNonAliased(predicate) => {
        //         eprintln!("pure predicate: {}", predicate);
        //         let ty = predicate.place.get_type();
        //         let place = lowerer.encode_expression_as_place(&predicate.place)?;
        //         // let root_address = lowerer.extract_root_address(&predicate.place)?;
        //         let root_address = true.into();
        //         // let snapshot = predicate.place.to_pure_snapshot(lowerer)?;
        //         let snapshot = true.into();
        //         let acc = lowerer.owned_aliased(
        //             CallContext::Procedure,
        //             ty,
        //             ty,
        //             place,
        //             root_address,
        //             snapshot,
        //             None,
        //         )?;
        //         eprintln!(" → {}", acc);
        //         acc
        //     }
        //     vir_mid::Predicate::MemoryBlockHeap(predicate) => {
        //         // let place = lowerer.encode_expression_as_place_address(&predicate.address)?;
        //         let place = true.into();
        //         let size = predicate.size.to_pure_snapshot(lowerer)?;
        //         lowerer.encode_memory_block_acc(place, size, acc_predicate.position)?
        //     }
        //     vir_mid::Predicate::MemoryBlockHeapDrop(predicate) => {
        //         // let place = lowerer.encode_expression_as_place_address(&predicate.address)?;
        //         let place = true.into();
        //         // let size = predicate.size.to_pure_snapshot(lowerer)?;
        //         let size = true.into();
        //         lowerer.encode_memory_block_heap_drop_acc(place, size, acc_predicate.position)?
        //     }
        //     _ => unimplemented!("{acc_predicate}"),
        // };
        // Ok(expression)
    }

    fn owned_non_aliased_snap(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _ty: &vir_mid::Type,
        _pointer_snapshot: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        unimplemented!()
    }

    // fn unfolding_to_snapshot(
    //     &mut self,
    //     lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    //     unfolding: &vir_mid::Unfolding,
    //     expect_math_bool: bool,
    // ) -> SpannedEncodingResult<vir_low::Expression> {
    //     todo!()
    // }

    fn call_context(&self) -> CallContext {
        todo!()
    }

    fn push_bound_variables(
        &mut self,
        _variables: &[vir_mid::VariableDecl],
    ) -> SpannedEncodingResult<()> {
        todo!()
    }

    fn pop_bound_variables(&mut self) -> SpannedEncodingResult<()> {
        todo!()
    }
}
