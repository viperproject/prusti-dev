use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        lifetimes::LifetimesInterface,
        lowerer::Lowerer,
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        references::ReferencesInterface,
        snapshots::{
            IntoPureSnapshot, IntoSnapshot, IntoSnapshotLowerer, PredicateKind,
            SelfFramingAssertionToSnapshot, SnapshotBytesInterface, SnapshotValidityInterface,
            SnapshotValuesInterface,
        },
        type_layouts::TypeLayoutsInterface,
        types::TypesInterface,
    },
};
use vir_crate::{
    common::{expression::ExpressionIterator, identifier::WithIdentifier},
    low::{self as vir_low},
    middle as vir_mid,
};

pub(in super::super::super) enum ContainingPredicateKind {
    Owned,
    UniqueRef,
    FracRef,
}

pub(in super::super::super) struct PredicateDeclBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super) lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
    pub(in super::super) predicate_name: &'l str,
    pub(in super::super) ty: &'l vir_mid::Type,
    pub(in super::super) type_decl: &'l vir_mid::TypeDecl,
    pub(in super::super) parameters: Vec<vir_low::VariableDecl>,
    pub(in super::super) conjuncts: Option<Vec<vir_low::Expression>>,
    pub(in super::super) position: vir_low::Position,
    /// `place` is used by subtypes that cannot be aliased.
    pub(in super::super) place: vir_low::VariableDecl,
    // /// `address` is used by subtypes that cannot be aliased.
    // pub(in super::super) address: vir_low::VariableDecl,
    /// `address` is used by subtypes that can be aliased.
    pub(in super::super) address: vir_low::VariableDecl,
}

impl<'l, 'p, 'v, 'tcx> PredicateDeclBuilder<'l, 'p, 'v, 'tcx> {
    pub(in super::super) fn new(
        lowerer: &'l mut Lowerer<'p, 'v, 'tcx>,
        predicate_name: &'l str,
        ty: &'l vir_mid::Type,
        type_decl: &'l vir_mid::TypeDecl,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<Self> {
        Ok(Self {
            place: vir_low::VariableDecl::new("place", lowerer.place_option_type()?),
            // address: vir_low::VariableDecl::new("address", lowerer.address_type()?),
            address: vir_low::VariableDecl::new("address", lowerer.address_type()?),
            ty,
            predicate_name,
            type_decl,
            parameters: Vec::new(),
            conjuncts: None,
            position,
            lowerer,
        })
    }

    pub(in super::super) fn build(self) -> vir_low::PredicateDecl {
        vir_low::PredicateDecl {
            name: format!("{}${}", self.predicate_name, self.ty.get_identifier()),
            kind: vir_low::PredicateKind::Owned,
            parameters: self.parameters,
            body: self
                .conjuncts
                .map(|conjuncts| conjuncts.into_iter().conjoin()),
        }
    }

    pub(in super::super) fn create_lifetime_parameters(&mut self) -> SpannedEncodingResult<()> {
        self.parameters
            .extend(self.lowerer.create_lifetime_parameters(self.type_decl)?);
        Ok(())
    }

    pub(in super::super) fn create_const_parameters(&mut self) -> SpannedEncodingResult<()> {
        for parameter in self.type_decl.get_const_parameters() {
            self.parameters
                .push(parameter.to_pure_snapshot(self.lowerer)?);
        }
        Ok(())
    }

    pub(in super::super) fn add_conjunct(
        &mut self,
        conjunct: vir_low::Expression,
    ) -> SpannedEncodingResult<()> {
        self.conjuncts.as_mut().unwrap().push(conjunct);
        Ok(())
    }

    pub(in super::super) fn add_validity(
        &mut self,
        snapshot: &vir_low::VariableDecl,
    ) -> SpannedEncodingResult<()> {
        let validity = self
            .lowerer
            .encode_snapshot_valid_call_for_type(snapshot.clone().into(), self.ty)?;
        self.add_conjunct(validity)
    }

    pub(in super::super) fn add_frac_ref_pointer_predicate(
        &mut self,
        lifetime: &vir_mid::ty::LifetimeConst,
        place: vir_low::VariableDecl,
        address: vir_low::VariableDecl,
    ) -> SpannedEncodingResult<vir_mid::Type> {
        let lifetime = lifetime.to_pure_snapshot(self.lowerer)?;
        let pointer_type = {
            let reference_type = self.type_decl.clone().unwrap_reference();
            vir_mid::Type::pointer(reference_type.target_type)
        };
        self.lowerer.ensure_type_definition(&pointer_type)?;
        let expression = self.lowerer.frac_ref(
            CallContext::BuiltinMethod,
            &pointer_type,
            &pointer_type,
            place.into(),
            address.into(),
            lifetime.into(),
            None, // FIXME
            None,
            self.position,
        )?;
        self.add_conjunct(expression)?;
        Ok(pointer_type)
    }

    pub(in super::super) fn add_unique_ref_pointer_predicate(
        &mut self,
        lifetime: &vir_mid::ty::LifetimeConst,
        place: vir_low::VariableDecl,
        address: vir_low::VariableDecl,
        // _snapshot: &vir_low::VariableDecl,
    ) -> SpannedEncodingResult<vir_mid::Type> {
        let lifetime = lifetime.to_pure_snapshot(self.lowerer)?;
        // let pointer_type = &self.lowerer.reference_address_type(self.ty)?;
        let pointer_type = {
            let reference_type = self.type_decl.clone().unwrap_reference();
            vir_mid::Type::pointer(reference_type.target_type)
        };
        self.lowerer.ensure_type_definition(&pointer_type)?;
        let expression = self.lowerer.unique_ref(
            CallContext::BuiltinMethod,
            &pointer_type,
            &pointer_type,
            place.into(),
            address.into(),
            lifetime.into(),
            None, // FIXME
            None,
            self.position,
        )?;
        self.add_conjunct(expression)?;
        Ok(pointer_type)
    }

    /// `containing_predicate` – whether the predicate is used in `Owned` or `UniqueRef`.
    pub(in super::super) fn add_unique_ref_target_predicate(
        &mut self,
        target_type: &vir_mid::Type,
        lifetime: &vir_mid::ty::LifetimeConst,
        place: vir_low::Expression,
        address: vir_low::VariableDecl,
        containing_predicate: ContainingPredicateKind,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let deref_place = self
            .lowerer
            .reference_deref_place(place.clone(), self.position)?;
        let lifetime_alive = self
            .lowerer
            .encode_lifetime_const_into_pure_is_alive_variable(lifetime)?;
        let lifetime = lifetime.to_pure_snapshot(self.lowerer)?;
        let (target_address, target_len) = {
            let pointer_type = &self.lowerer.reference_address_type(self.ty)?;
            let pointer_snapshot = match containing_predicate {
                ContainingPredicateKind::Owned => {
                    self.lowerer
                        .encode_snapshot_to_bytes_function(pointer_type)?;
                    let size_of = self
                        .lowerer
                        .encode_type_size_expression2(self.ty, self.type_decl)?;
                    let bytes = self
                        .lowerer
                        .encode_memory_block_bytes_expression(address.into(), size_of)?;
                    let from_bytes = pointer_type.to_snapshot(self.lowerer)?;
                    expr! {
                        Snap<pointer_type>::from_bytes([bytes])
                    }
                }
                ContainingPredicateKind::UniqueRef => self.lowerer.unique_ref_snap(
                    CallContext::BuiltinMethod,
                    pointer_type,
                    pointer_type,
                    place,
                    address.into(),
                    lifetime.clone().into(),
                    None,
                    false,
                    self.position,
                )?,
                ContainingPredicateKind::FracRef => unreachable!(),
            };
            let target_address = self.lowerer.pointer_address(
                pointer_type,
                pointer_snapshot.clone(),
                self.position,
            )?;
            let target_len = if pointer_type.is_pointer_to_slice() {
                Some(self.lowerer.pointer_slice_len(
                    pointer_type,
                    pointer_snapshot,
                    self.position,
                )?)
            } else {
                None
            };
            (target_address, target_len)
        };
        let expression = self.lowerer.unique_ref(
            CallContext::BuiltinMethod,
            target_type,
            target_type,
            deref_place,
            target_address,
            lifetime.into(),
            target_len,
            None,
            self.position,
        )?;
        self.add_conjunct(expr! { [lifetime_alive.into()] ==> [expression] })
    }

    // FIXME: Code duplication with `add_unique_ref_target_predicate`.
    pub(in super::super) fn add_frac_ref_target_predicate(
        &mut self,
        target_type: &vir_mid::Type,
        lifetime: &vir_mid::ty::LifetimeConst,
        place: vir_low::Expression,
        address: vir_low::VariableDecl,
        containing_predicate: ContainingPredicateKind,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let deref_place = self
            .lowerer
            .reference_deref_place(place.clone(), self.position)?;
        let lifetime_alive = self
            .lowerer
            .encode_lifetime_const_into_pure_is_alive_variable(lifetime)?;
        let lifetime = lifetime.to_pure_snapshot(self.lowerer)?;
        let pointer_type = &self.lowerer.reference_address_type(self.ty)?;
        let pointer_snapshot = match containing_predicate {
            ContainingPredicateKind::Owned => {
                self.lowerer
                    .encode_snapshot_to_bytes_function(pointer_type)?;
                let size_of = self
                    .lowerer
                    .encode_type_size_expression2(self.ty, self.type_decl)?;
                let bytes = self
                    .lowerer
                    .encode_memory_block_bytes_expression(address.into(), size_of)?;
                let from_bytes = pointer_type.to_snapshot(self.lowerer)?;
                expr! {
                    Snap<pointer_type>::from_bytes([bytes])
                }
            }
            ContainingPredicateKind::UniqueRef => self.lowerer.unique_ref_snap(
                CallContext::BuiltinMethod,
                pointer_type,
                pointer_type,
                place,
                address.into(),
                lifetime.clone().into(),
                None,
                false,
                self.position,
            )?,
            ContainingPredicateKind::FracRef => self.lowerer.frac_ref_snap(
                CallContext::BuiltinMethod,
                pointer_type,
                pointer_type,
                place,
                address.into(),
                lifetime.clone().into(),
                None,
                self.position,
            )?,
        };
        let target_address =
            self.lowerer
                .pointer_address(pointer_type, pointer_snapshot.clone(), self.position)?;
        let target_len = if pointer_type.is_pointer_to_slice() {
            Some(
                self.lowerer
                    .pointer_slice_len(pointer_type, pointer_snapshot, self.position)?,
            )
        } else {
            None
        };
        let expression = self.lowerer.frac_ref(
            CallContext::BuiltinMethod,
            target_type,
            target_type,
            deref_place,
            target_address,
            lifetime.into(),
            target_len,
            None,
            self.position,
        )?;
        self.add_conjunct(expr! { [lifetime_alive.into()] ==> [expression] })
    }

    pub(in super::super) fn array_length_int(
        &mut self,
        array_length_mid: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let array_length = array_length_mid.to_pure_snapshot(self.lowerer)?;
        let size_type_mid = self.lowerer.size_type_mid()?;
        self.lowerer
            .obtain_constant_value(&size_type_mid, array_length.into(), self.position)
    }

    pub(in super::super) fn add_snapshot_len_equal_to(
        &mut self,
        snapshot: &vir_low::VariableDecl,
        array_length_mid: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<()> {
        use vir_low::macros::*;
        let snapshot_length = self
            .lowerer
            .obtain_array_len_snapshot(snapshot.clone().into(), self.position)?;
        let array_length_int = self.array_length_int(array_length_mid)?;
        let expression = expr! {
            ([array_length_int] == [snapshot_length])
        };
        self.add_conjunct(expression)
    }

    pub(in super::super::super) fn add_structural_invariant(
        &mut self,
        decl: &vir_mid::type_decl::Struct,
        predicate_kind: PredicateKind,
    ) -> SpannedEncodingResult<Vec<vir_mid::Type>> {
        if let Some(invariant) = &decl.structural_invariant {
            let mut encoder = SelfFramingAssertionToSnapshot::for_predicate_body(
                self.place.clone(),
                self.address.clone(),
                predicate_kind,
            );
            for assertion in invariant {
                let low_assertion =
                    encoder.expression_to_snapshot(self.lowerer, assertion, true)?;
                self.add_conjunct(low_assertion)?;
            }
            Ok(encoder.into_created_predicate_types())
        } else {
            Ok(Vec::new())
        }
    }
}

pub(in super::super::super) trait PredicateDeclBuilderMethods<'l, 'p, 'v, 'tcx>
where
    'p: 'l,
    'v: 'p,
    'tcx: 'v,
{
    fn inner(&mut self) -> &mut PredicateDeclBuilder<'l, 'p, 'v, 'tcx>;

    fn lowerer<'a>(&'a mut self) -> &'a mut Lowerer<'p, 'v, 'tcx>
    where
        'l: 'a,
    {
        self.inner().lowerer
    }

    fn create_body(&mut self) {
        let inner = self.inner();
        debug_assert!(inner.conjuncts.is_none(), "The body is already created.");
        inner.conjuncts = Some(Vec::new());
    }

    // FIXME: Remove code duplication.
    fn add_const_parameters_validity(&mut self) -> SpannedEncodingResult<()> {
        let inner = self.inner();
        let size_type = inner.lowerer.size_type_mid()?;
        for parameter_mid in inner.type_decl.get_const_parameters() {
            let parameter = parameter_mid.to_pure_snapshot(inner.lowerer)?;
            let validity = inner
                .lowerer
                .encode_snapshot_valid_call_for_type(parameter.into(), &size_type)?;
            inner.add_conjunct(validity)?;
        }
        Ok(())
    }
}
