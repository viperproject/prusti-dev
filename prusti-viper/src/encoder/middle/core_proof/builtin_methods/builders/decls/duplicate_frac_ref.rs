use super::common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{
        addresses::AddressesInterface, builtin_methods::CallContext, lowerer::Lowerer,
        places::PlacesInterface, predicates::PredicatesOwnedInterface,
        references::ReferencesInterface, snapshots::IntoPureSnapshot,
    },
};
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct DuplicateFracRefMethodBuilder<'l, 'p, 'v, 'tcx> {
    inner: BuiltinMethodBuilder<'l, 'p, 'v, 'tcx>,
    target_place: vir_low::VariableDecl,
    source_place: vir_low::VariableDecl,
    // source_snapshot: vir_low::VariableDecl,
    address: vir_low::VariableDecl,
    source_permission_amount: vir_low::VariableDecl,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for DuplicateFracRefMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        &mut self.inner
    }
}

impl<'l, 'p, 'v, 'tcx> DuplicateFracRefMethodBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super::super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        kind: vir_low::MethodKind,
        method_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        error_kind: BuiltinMethodKind,
    ) -> SpannedEncodingResult<Self> {
        let target_place = vir_low::VariableDecl::new("target_place", lowerer.place_option_type()?);
        let source_place = vir_low::VariableDecl::new("source_place", lowerer.place_option_type()?);
        // let source_snapshot =
        //     vir_low::VariableDecl::new("source_snapshot", ty.to_snapshot(lowerer)?);
        let address = vir_low::VariableDecl::new("address", lowerer.address_type()?);
        let source_permission_amount =
            vir_low::VariableDecl::new("source_permission_amount", vir_low::Type::Perm);
        let inner =
            BuiltinMethodBuilder::new(lowerer, kind, method_name, ty, type_decl, error_kind)?;
        Ok(Self {
            inner,
            target_place,
            source_place,
            // source_snapshot,
            address,
            source_permission_amount,
        })
    }

    pub(in super::super::super::super) fn build(self) -> vir_low::MethodDecl {
        self.inner.build()
    }

    pub(in super::super::super::super) fn create_parameters(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        self.inner.parameters.push(self.target_place.clone());
        self.inner.parameters.push(self.source_place.clone());
        // self.inner.parameters.push(self.source_snapshot.clone());
        self.inner.parameters.push(self.address.clone());
        self.inner
            .parameters
            .push(self.source_permission_amount.clone());
        self.create_lifetime_parameters()?;
        self.create_const_parameters()?;
        Ok(())
    }

    // pub(in super::super::super::super) fn add_same_address_precondition(
    //     &mut self,
    // ) -> SpannedEncodingResult<()> {
    //     use vir_low::macros::*;
    //     let address = self.inner.lowerer.reference_address(
    //         self.inner.ty,
    //         self.source_snapshot.clone().into(),
    //         self.inner.position,
    //     )?;
    //     let deref_source_place = self
    //         .inner
    //         .lowerer
    //         .reference_deref_place(self.source_place.clone().into(), self.inner.position)?;
    //     let deref_target_place = self
    //         .inner
    //         .lowerer
    //         .reference_deref_place(self.target_place.clone().into(), self.inner.position)?;
    //     let source_address =
    //         self.compute_address_expression(deref_source_place, root_address.clone());
    //     let target_address = self.compute_address_expression(deref_target_place, root_address);
    //     let expression = expr! {
    //         [target_address] == [source_address]
    //     };
    //     self.add_precondition(expression);
    //     Ok(())
    // }

    pub(in super::super::super::super) fn add_frac_ref_pre_postcondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        // let address = self.inner.lowerer.reference_address(
        //     self.inner.ty,
        //     self.source_snapshot.clone().into(),
        //     self.inner.position,
        // )?;
        let address: vir_low::Expression = self.address.clone().into();
        let deref_source_place = self
            .inner
            .lowerer
            .reference_deref_place(self.source_place.clone().into(), self.inner.position)?;
        let target_type = self.inner.ty.clone().unwrap_reference().target_type;
        let decl = self.inner.type_decl.clone().unwrap_reference();
        let target_type_decl = decl.target_type;
        let lifetime = &decl.lifetimes[0];
        let deref_target_place = self
            .inner
            .lowerer
            .reference_deref_place(self.target_place.clone().into(), self.inner.position)?;
        // let _current_snapshot = self.inner.lowerer.reference_target_current_snapshot(
        //     self.inner.ty,
        //     self.source_snapshot.clone().into(),
        //     self.inner.position,
        // )?;
        let lifetime = lifetime.to_pure_snapshot(self.inner.lowerer)?;
        // let mut builder = FracRefUseBuilder::new(
        //     self.lowerer(),
        //     CallContext::BuiltinMethod,
        //     &target_type,
        //     &target_type_decl,
        //     deref_source_place,
        //     address.clone(),
        //     // current_snapshot.clone(),
        //     lifetime.clone().into(),
        // )?;
        // builder.add_lifetime_arguments()?;
        // builder.add_const_arguments()?;
        // let source_expression = builder.build()?;
        let TODO_source_slice_len = None;
        let source_expression = self.inner.lowerer.frac_ref(
            CallContext::BuiltinMethod,
            &target_type,
            &target_type_decl,
            deref_source_place.clone(),
            address.clone(),
            lifetime.clone().into(),
            TODO_source_slice_len.clone(),
            Some(self.source_permission_amount.clone().into()),
            self.inner.position,
        )?;
        self.add_precondition(source_expression.clone());
        self.add_postcondition(source_expression);
        // let mut builder = FracRefUseBuilder::new(
        //     self.lowerer(),
        //     CallContext::BuiltinMethod,
        //     &target_type,
        //     &target_type_decl,
        //     deref_target_place,
        //     address,
        //     // current_snapshot,
        //     lifetime.into(),
        // )?;
        // builder.add_lifetime_arguments()?;
        // builder.add_const_arguments()?;
        // let target_expression = builder.build();
        let TODO_target_slice_len = None;
        let target_expression = self.inner.lowerer.frac_ref(
            CallContext::BuiltinMethod,
            &target_type,
            &target_type_decl,
            deref_target_place.clone(),
            address.clone(),
            lifetime.clone().into(),
            TODO_target_slice_len.clone(),
            None,
            self.inner.position,
        )?;
        self.add_postcondition(target_expression);
        let source_snapshot = self.inner.lowerer.frac_ref_snap(
            CallContext::BuiltinMethod,
            &target_type,
            &target_type_decl,
            deref_source_place,
            address.clone(),
            lifetime.clone().into(),
            TODO_source_slice_len,
            self.inner.position,
        )?;
        let target_snapshot = self.inner.lowerer.frac_ref_snap(
            CallContext::BuiltinMethod,
            &target_type,
            &target_type_decl,
            deref_target_place,
            address,
            lifetime.into(),
            TODO_target_slice_len,
            self.inner.position,
        )?;
        let snapshot_preserved = vir_low::Expression::equals(
            source_snapshot.clone(),
            vir_low::Expression::labelled_old(None, source_snapshot.clone(), self.inner.position),
        );
        self.add_postcondition(snapshot_preserved);
        let snapshot_equality = vir_low::Expression::equals(source_snapshot, target_snapshot);
        self.add_postcondition(snapshot_equality);
        Ok(())
    }

    pub(in super::super::super::super) fn add_permission_amount_positive_precondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        let expression = self
            .inner
            .create_permission_amount_positive(&self.source_permission_amount)?;
        self.add_precondition(expression);
        Ok(())
    }
}
