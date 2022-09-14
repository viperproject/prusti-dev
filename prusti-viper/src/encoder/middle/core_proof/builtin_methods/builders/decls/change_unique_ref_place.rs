use super::common::{BuiltinMethodBuilder, BuiltinMethodBuilderMethods};
use crate::encoder::{
    errors::{BuiltinMethodKind, SpannedEncodingResult},
    middle::core_proof::{
        builtin_methods::CallContext,
        lifetimes::LifetimesInterface,
        lowerer::Lowerer,
        places::PlacesInterface,
        predicates::PredicatesOwnedInterface,
        references::ReferencesInterface,
        snapshots::{IntoPureSnapshot, IntoSnapshot},
    },
};
use vir_crate::{
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super::super) struct ChangeUniqueRefPlaceMethodBuilder<'l, 'p, 'v, 'tcx> {
    inner: BuiltinMethodBuilder<'l, 'p, 'v, 'tcx>,
    target_place: vir_low::VariableDecl,
    source_place: vir_low::VariableDecl,
    source_snapshot: vir_low::VariableDecl,
}

impl<'l, 'p, 'v, 'tcx> BuiltinMethodBuilderMethods<'l, 'p, 'v, 'tcx>
    for ChangeUniqueRefPlaceMethodBuilder<'l, 'p, 'v, 'tcx>
{
    fn inner(&mut self) -> &mut BuiltinMethodBuilder<'l, 'p, 'v, 'tcx> {
        &mut self.inner
    }
}

impl<'l, 'p, 'v, 'tcx> ChangeUniqueRefPlaceMethodBuilder<'l, 'p, 'v, 'tcx> {
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
        let source_snapshot =
            vir_low::VariableDecl::new("source_snapshot", ty.to_snapshot(lowerer)?);
        let inner =
            BuiltinMethodBuilder::new(lowerer, kind, method_name, ty, type_decl, error_kind)?;
        Ok(Self {
            inner,
            target_place,
            source_place,
            source_snapshot,
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
        self.inner.parameters.push(self.source_snapshot.clone());
        self.create_lifetime_parameters()?;
        self.create_const_parameters()?;
        Ok(())
    }

    pub(in super::super::super::super) fn add_same_address_precondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        // use vir_low::macros::*;
        // let root_address = self.inner.lowerer.reference_address(
        //     self.inner.ty,
        //     self.source_snapshot.clone().into(),
        //     self.inner.position,
        // )?;
        // let deref_source_place = self
        //     .inner
        //     .lowerer
        //     .reference_deref_place(self.source_place.clone().into(), self.inner.position)?;
        // let deref_target_place = self
        //     .inner
        //     .lowerer
        //     .reference_deref_place(self.target_place.clone().into(), self.inner.position)?;
        // let source_address =
        //     self.compute_address_expression(deref_source_place, root_address.clone());
        // let target_address = self.compute_address_expression(deref_target_place, root_address);
        // let expression = expr! {
        //     [target_address] == [source_address]
        // };
        // self.add_precondition(expression);
        Ok(())
    }

    // Change the place of UniqueRef from source to target.
    pub(in super::super::super::super) fn add_unique_ref_pre_postcondition(
        &mut self,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let root_address = self.inner.lowerer.reference_address(
            self.inner.ty,
            self.source_snapshot.clone().into(),
            self.inner.position,
        )?;
        let slice_len = self.inner.lowerer.reference_slice_len(
            self.inner.ty,
            self.source_snapshot.clone().into(),
            self.inner.position,
        )?;
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
        let current_snapshot = self.inner.lowerer.reference_target_current_snapshot(
            self.inner.ty,
            self.source_snapshot.clone().into(),
            self.inner.position,
        )?;
        let final_snapshot = self.inner.lowerer.reference_target_final_snapshot(
            self.inner.ty,
            self.source_snapshot.clone().into(),
            self.inner.position,
        )?;
        let lifetime_alive = self
            .inner
            .lowerer
            .encode_lifetime_const_into_pure_is_alive_variable(lifetime)?;
        let lifetime = lifetime.to_pure_snapshot(self.inner.lowerer)?;
        let source_expression = self.inner.lowerer.unique_ref_with_current_snapshot(
            CallContext::BuiltinMethod,
            &target_type,
            &target_type_decl,
            deref_source_place.clone(),
            root_address.clone(),
            current_snapshot.clone(),
            lifetime.clone().into(),
            slice_len.clone(),
            None,
            self.inner.position,
        )?;
        let source_final_expression = self.inner.lowerer.unique_ref_snap(
            CallContext::BuiltinMethod,
            &target_type,
            &target_type_decl,
            deref_source_place,
            root_address.clone(),
            lifetime.clone().into(),
            slice_len.clone(),
            true,
            self.inner.position,
        )?;
        self.add_precondition(expr! { lifetime_alive ==> [source_expression] });
        self.add_precondition(expr! {
            lifetime_alive ==>
            ([final_snapshot.clone()] == [source_final_expression])
        });
        let target_expression = self.inner.lowerer.unique_ref_with_current_snapshot(
            CallContext::BuiltinMethod,
            &target_type,
            &target_type_decl,
            deref_target_place.clone(),
            root_address.clone(),
            current_snapshot,
            lifetime.clone().into(),
            slice_len.clone(),
            None,
            self.inner.position,
        )?;
        let target_final_expression = self.inner.lowerer.unique_ref_snap(
            CallContext::BuiltinMethod,
            &target_type,
            &target_type_decl,
            deref_target_place,
            root_address,
            lifetime.into(),
            slice_len,
            true,
            self.inner.position,
        )?;
        self.add_postcondition(expr! { lifetime_alive ==> [target_expression] });
        self.add_postcondition(expr! {
            lifetime_alive ==>
            ([final_snapshot] == [target_final_expression])
        });
        Ok(())
    }
}
