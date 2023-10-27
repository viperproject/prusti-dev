use crate::encoder::{
    errors::SpannedEncodingResult,
    middle::core_proof::{
        addresses::AddressesInterface,
        lowerer::{DomainsLowererInterface, Lowerer},
        snapshots::{IntoSnapshot, SnapshotAdtsInterface, SnapshotDomainsInterface},
        types::TypesInterface,
    },
};
use vir_crate::{
    common::expression::UnaryOperationHelpers,
    low::{self as vir_low, operations::ty::Typed},
    middle::{self as vir_mid},
};

pub(in super::super::super) trait SnapshotValuesInterface {
    // Top-down: if we have a snapshot of a struct and we want to get a snapshot
    // of its field.

    fn obtain_constant_value(
        &mut self,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn obtain_struct_field_snapshot(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_snapshot: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn obtain_enum_variant_snapshot(
        &mut self,
        base_type: &vir_mid::Type,
        variant: &vir_mid::ty::VariantIndex,
        base_snapshot: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn encode_discriminant_name(&mut self, domain_name: &str) -> SpannedEncodingResult<String>;
    fn obtain_enum_discriminant(
        &mut self,
        place: vir_low::Expression,
        ty: &vir_mid::Type,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn obtain_array_len_snapshot(
        &mut self,
        base_snapshot: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn obtain_array_element_snapshot(
        &mut self,
        base_snapshot: vir_low::Expression,
        index: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;

    // Bottom-up: if we have a snapshot of a struct's fields and we want to get
    // a snapshot of the struct.

    fn construct_constant_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn construct_unary_op_snapshot(
        &mut self,
        op: vir_mid::UnaryOpKind,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn construct_binary_op_snapshot(
        &mut self,
        op: vir_mid::BinaryOpKind,
        ty: &vir_mid::Type,
        arg_type: &vir_mid::Type,
        left: vir_low::Expression,
        right: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn construct_struct_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        arguments: Vec<vir_low::Expression>,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
    fn construct_enum_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression>;
}

impl<'p, 'v: 'p, 'tcx: 'v> SnapshotValuesInterface for Lowerer<'p, 'v, 'tcx> {
    fn obtain_constant_value(
        &mut self,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let return_type = match &ty {
            vir_mid::Type::Bool => vir_low::Type::Bool,
            vir_mid::Type::Int(_) => vir_low::Type::Int,
            vir_mid::Type::Float(vir_mid::ty::Float::F32) => {
                vir_low::Type::Float(vir_low::ty::Float::F32)
            }
            vir_mid::Type::Float(vir_mid::ty::Float::F64) => {
                vir_low::Type::Float(vir_low::ty::Float::F64)
            }
            vir_mid::Type::Pointer(_) => self.address_type()?,
            x => unimplemented!("{:?}", x),
        };
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let function_name = self.snapshot_destructor_constant_name(&domain_name)?;
        self.create_domain_func_app(
            domain_name,
            function_name,
            vec![argument],
            return_type,
            position,
        )
    }
    fn obtain_struct_field_snapshot(
        &mut self,
        base_type: &vir_mid::Type,
        field: &vir_mid::FieldDecl,
        base_snapshot: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let domain_name = self.encode_snapshot_domain_name(base_type)?;
        let return_type = field.ty.to_snapshot(self)?;
        Ok(self
            .snapshot_destructor_struct_call(&domain_name, &field.name, return_type, base_snapshot)?
            .set_default_position(position))
    }
    fn obtain_enum_variant_snapshot(
        &mut self,
        base_type: &vir_mid::Type,
        variant: &vir_mid::ty::VariantIndex,
        base_snapshot: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let domain_name = self.encode_snapshot_domain_name(base_type)?;
        let variant_ty = base_type.clone().variant(variant.clone());
        let return_type = variant_ty.to_snapshot(self)?;
        Ok(self
            .snapshot_destructor_enum_variant_call(
                &domain_name,
                &variant.index,
                return_type,
                base_snapshot,
            )?
            .set_default_position(position))
    }
    fn encode_discriminant_name(&mut self, domain_name: &str) -> SpannedEncodingResult<String> {
        Ok(format!("discriminant${domain_name}"))
    }
    fn obtain_enum_discriminant(
        &mut self,
        place: vir_low::Expression,
        ty: &vir_mid::Type,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let function_name = self.encode_discriminant_name(&domain_name)?;
        self.create_domain_func_app(
            domain_name,
            function_name,
            vec![place],
            vir_low::Type::Int,
            position,
        )
    }
    fn obtain_array_len_snapshot(
        &mut self,
        base_snapshot: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        Ok(vir_low::Expression::container_op(
            vir_low::expression::ContainerOpKind::SeqLen,
            base_snapshot.get_type().clone(),
            vec![base_snapshot],
            position,
        ))
    }
    fn obtain_array_element_snapshot(
        &mut self,
        base_snapshot: vir_low::Expression,
        index: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        Ok(vir_low::Expression::container_op(
            vir_low::expression::ContainerOpKind::SeqIndex,
            base_snapshot.get_type().clone(),
            vec![base_snapshot, index],
            position,
        ))
    }
    fn construct_constant_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        mut argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.ensure_type_definition(ty)?;
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let low_type = match &ty {
            vir_mid::Type::Bool => vir_low::Type::Bool,
            vir_mid::Type::Int(_) => vir_low::Type::Int,
            vir_mid::Type::Float(vir_mid::ty::Float::F32) => {
                vir_low::Type::Float(vir_low::ty::Float::F32)
            }
            vir_mid::Type::Float(vir_mid::ty::Float::F64) => {
                vir_low::Type::Float(vir_low::ty::Float::F64)
            }
            vir_mid::Type::Pointer(_) => self.address_type()?,
            vir_mid::Type::Reference(_) => self.address_type()?,
            x => unimplemented!("{:?}", x),
        };
        vir_low::operations::ty::Typed::set_type(&mut argument, low_type);
        Ok(self
            .snapshot_constructor_constant_call(&domain_name, vec![argument])?
            .set_default_position(position))
    }
    fn construct_unary_op_snapshot(
        &mut self,
        op: vir_mid::UnaryOpKind,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if ty == &vir_mid::Type::MBool {
            Ok(vir_low::Expression::not(argument).set_default_position(position))
        } else {
            // FIXME: Encode evaluation and simplification axioms.
            let domain_name = self.encode_snapshot_domain_name(ty)?;
            let variant = self.encode_unary_op_variant(op, ty)?;
            let function_name =
                self.snapshot_constructor_struct_alternative_name(&domain_name, &variant)?;
            let return_type = ty.to_snapshot(self)?;
            self.create_domain_func_app(
                domain_name,
                function_name,
                vec![argument],
                return_type,
                position,
            )
        }
    }
    fn construct_binary_op_snapshot(
        &mut self,
        op: vir_mid::BinaryOpKind,
        ty: &vir_mid::Type,
        arg_type: &vir_mid::Type,
        left: vir_low::Expression,
        right: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // TODO: Add MPerm special cases here.
        if ty == &vir_mid::Type::MBool {
            Ok(vir_low::Expression::binary_op(
                op.to_snapshot(self)?,
                left,
                right,
                position,
            ))
        } else {
            // FIXME: Encode evaluation and simplification axioms.
            let domain_name = self.encode_snapshot_domain_name(ty)?;
            let variant = self.encode_binary_op_variant(op, arg_type)?;
            let function_name =
                self.snapshot_constructor_struct_alternative_name(&domain_name, &variant)?;
            let return_type = ty.to_snapshot(self)?;
            self.create_domain_func_app(
                domain_name,
                function_name,
                vec![left, right],
                return_type,
                position,
            )
        }
    }

    fn construct_struct_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        arguments: Vec<vir_low::Expression>,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let domain_name = self.encode_snapshot_domain_name(ty)?;
        let function_name = self.snapshot_constructor_struct_name(&domain_name)?;
        let return_type = ty.to_snapshot(self)?;
        self.create_domain_func_app(domain_name, function_name, arguments, return_type, position)
    }
    fn construct_enum_snapshot(
        &mut self,
        ty: &vir_mid::Type,
        argument: vir_low::Expression,
        position: vir_mid::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let variant_name = match ty {
            vir_mid::Type::Enum(ty) => ty.variant.as_ref().unwrap().as_ref(),
            _ => unreachable!("expected enum or union, got: {}", ty),
        };
        let enum_ty = ty.forget_variant().unwrap();
        let domain_name = self.encode_snapshot_domain_name(&enum_ty)?;
        let function_name =
            self.snapshot_constructor_enum_variant_name(&domain_name, variant_name)?;
        let return_type = enum_ty.to_snapshot(self)?;
        self.create_domain_func_app(
            domain_name,
            function_name,
            vec![argument],
            return_type,
            position,
        )
    }
}
