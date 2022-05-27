use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        lowerer::Lowerer,
        places::PlacesInterface,
        snapshots::{
            IntoSnapshot, SnapshotAdtsInterface, SnapshotDomainsInterface, SnapshotValuesInterface,
        },
        types::TypesInterface,
    },
};
use vir_crate::{
    low as vir_low,
    middle::{self as vir_mid},
};

trait Private {
    fn reference_target_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
        version: &str,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> Private for Lowerer<'p, 'v, 'tcx> {
    fn reference_target_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
        version: &str,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let reference_type = ty.clone().unwrap_reference();
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let return_type = reference_type.target_type.to_snapshot(self)?;
        Ok(self
            .snapshot_destructor_struct_call(&domain_name, version, return_type, snapshot)?
            .set_default_position(position))
    }
}

pub(in super::super) trait ReferencesInterface {
    fn shared_non_alloc_reference_snapshot_constructor(
        &mut self,
        ty: &vir_mid::Type,
        current_snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn reference_deref_place(
        &mut self,
        place: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn reference_target_current_snapshot(
        &mut self,
        reference_type: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn reference_target_final_snapshot(
        &mut self,
        reference_type: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn reference_address(
        &mut self,
        reference_type: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn reference_address_snapshot(
        &mut self,
        reference_type: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn reference_address_type(
        &mut self,
        reference_type: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_mid::Type>;
}

impl<'p, 'v: 'p, 'tcx: 'v> ReferencesInterface for Lowerer<'p, 'v, 'tcx> {
    /// A constructor of a shared reference snapshot in context where references
    /// are not allowed to have addresses.
    fn shared_non_alloc_reference_snapshot_constructor(
        &mut self,
        ty: &vir_mid::Type,
        current_snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.ensure_type_definition(ty)?;
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        Ok(self
            .snapshot_alternative_constructor_struct_call(
                &domain_name,
                "no_alloc",
                vec![current_snapshot],
            )?
            .set_default_position(position))
    }
    fn reference_deref_place(
        &mut self,
        place: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.encode_deref_place(place, position)
    }
    fn reference_target_current_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.reference_target_snapshot(ty, snapshot, position, "target_current")
    }
    fn reference_target_final_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.reference_target_snapshot(ty, snapshot, position, "target_final")
    }
    fn reference_address(
        &mut self,
        reference_type: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(reference_type.is_reference());
        let domain_name = self.encode_snapshot_domain_name(reference_type)?;
        let return_type = self.address_type()?;
        Ok(self
            .snapshot_destructor_struct_call(&domain_name, "address", return_type, snapshot)?
            .set_default_position(position))
    }
    fn reference_address_snapshot(
        &mut self,
        reference_type: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let address = self.reference_address(reference_type, snapshot, position)?;
        let address_type = self.reference_address_type(reference_type)?;
        self.construct_struct_snapshot(&address_type, vec![address], position)
    }
    fn reference_address_type(
        &mut self,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_mid::Type> {
        let reference_type = ty.clone().unwrap_reference();
        Ok(vir_mid::Type::pointer(*reference_type.target_type))
    }
}
