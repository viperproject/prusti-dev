use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        heap::HeapInterface,
        lowerer::{DomainsLowererInterface, Lowerer},
        snapshots::{IntoSnapshot, SnapshotValuesInterface, SnapshotVariablesInterface},
        type_layouts::TypeLayoutsInterface,
    },
};
use vir_crate::{
    common::identifier::WithIdentifier,
    low as vir_low,
    middle::{self as vir_mid},
};

pub(in super::super) trait PointersInterface {
    fn pointer_address(
        &mut self,
        pointer_type: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn address_to_pointer(
        &mut self,
        pointer_type: &vir_mid::Type,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn pointer_slice_len(
        &mut self,
        pointer_type: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn pointer_target_snapshot_in_heap(
        &mut self,
        ty: &vir_mid::Type,
        heap: vir_low::VariableDecl,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn pointer_target_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        old_label: &Option<String>,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn pointer_target_as_snapshot_field(
        &mut self,
        framing_type: &vir_mid::Type,
        deref_field_name: &str,
        deref_type: vir_low::Type,
        framing_place_snapshot: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn heap_chunk_to_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        heap_chunk: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn address_in_heap(
        &mut self,
        heap: vir_low::VariableDecl,
        pointer_place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> PointersInterface for Lowerer<'p, 'v, 'tcx> {
    fn pointer_address(
        &mut self,
        pointer_type: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(pointer_type.is_pointer());
        // self.obtain_constant_value(pointer_type, snapshot, position)
        let address_type = self.address_type()?;
        self.obtain_parameter_snapshot(pointer_type, "address", address_type, snapshot, position)
    }
    fn address_to_pointer(
        &mut self,
        pointer_type: &vir_mid::Type,
        address: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(pointer_type.is_pointer());
        self.construct_struct_snapshot(pointer_type, vec![address], position)
    }
    fn pointer_slice_len(
        &mut self,
        pointer_type: &vir_mid::Type,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(pointer_type.is_pointer_to_slice());
        let len_type = self.size_type()?;
        self.obtain_parameter_snapshot(pointer_type, "len", len_type, snapshot, position)
    }
    fn pointer_target_snapshot_in_heap(
        &mut self,
        ty: &vir_mid::Type,
        heap: vir_low::VariableDecl,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let address = self.pointer_address(ty, snapshot, position)?;
        let heap_chunk = self.heap_lookup(heap.into(), address, position)?;
        // let heap_chunk = vir_low::Expression::container_op_no_pos(
        //     vir_low::ContainerOpKind::MapLookup,
        //     heap.ty.clone(),
        //     vec![heap.into(), address],
        // );
        let pointer_type = ty.clone().unwrap_pointer();
        self.heap_chunk_to_snapshot(&pointer_type.target_type, heap_chunk, position)
    }
    fn pointer_target_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        old_label: &Option<String>,
        snapshot: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if self.use_heap_variable()? {
            // let address = self.pointer_address(ty, snapshot, position)?;
            let heap = self.heap_variable_version_at_label(old_label)?;
            // let heap_chunk = vir_low::Expression::container_op_no_pos(
            //     vir_low::ContainerOpKind::MapLookup,
            //     heap.ty.clone(),
            //     vec![heap.into(), address],
            // );
            // let pointer_type = ty.clone().unwrap_pointer();
            // self.heap_chunk_to_snapshot(&pointer_type.target_type, heap_chunk, position)
            self.pointer_target_snapshot_in_heap(ty, heap, snapshot, position)
        } else {
            unimplemented!();
            // let address = self.pointer_address(ty, snapshot, position)?;
            // let pointer_type = ty.clone().unwrap_pointer();
            // let target_type = &*pointer_type.target_type;
            // self.owned_aliased_snap(
            //     CallContext::Procedure,
            //     target_type,
            //     target_type,
            //     address,
            //     position,
            // )
        }
    }
    fn pointer_target_as_snapshot_field(
        &mut self,
        framing_type: &vir_mid::Type,
        deref_field_name: &str,
        deref_type: vir_low::Type,
        framing_place_snapshot: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.obtain_parameter_snapshot(
            framing_type,
            deref_field_name,
            deref_type,
            framing_place_snapshot,
            position,
        )
    }
    fn heap_chunk_to_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        heap_chunk: vir_low::Expression,
        position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let return_type = ty.to_snapshot(self)?;
        self.create_domain_func_app(
            // FIXME: Use HEAP_CHUNK_TYPE_NAME here.
            "HeapChunk$",
            format!("heap_chunk_to${}", ty.get_identifier()),
            vec![heap_chunk],
            return_type,
            position,
        )
    }
    fn address_in_heap(
        &mut self,
        _heap: vir_low::VariableDecl,
        _pointer_place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!("Delete");
        // let pointer = pointer_place.to_pure_snapshot(self)?;
        // let address =
        //     self.pointer_address(pointer_place.get_type(), pointer, pointer_place.position())?;
        // let in_heap = vir_low::Expression::container_op_no_pos(
        //     vir_low::ContainerOpKind::MapContains,
        //     heap.ty.clone(),
        //     vec![heap.into(), address],
        // );
        // Ok(in_heap)
    }
}
