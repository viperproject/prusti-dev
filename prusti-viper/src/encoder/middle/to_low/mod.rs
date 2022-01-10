use crate::encoder::errors::SpannedEncodingError;
use vir_crate::{common::identifier::WithIdentifier, low::operations::ToLowLowerer};

impl<'v, 'tcx> ToLowLowerer for crate::encoder::Encoder<'v, 'tcx> {
    type Error = SpannedEncodingError;

    fn to_low_expression_downcast(
        &self,
        _variant: vir_crate::middle::ast::expression::Downcast,
    ) -> vir_crate::low::ast::expression::Expression {
        todo!()
    }

    fn to_low_func_app(
        &self,
        app: vir_crate::middle::ast::expression::FuncApp,
    ) -> vir_crate::low::ast::expression::FuncApp {
        // TODO: This currently does not take into account snapshots.
        assert_eq!(app.arguments.len(), 0, "FIXME");
        vir_crate::low::ast::expression::FuncApp {
            function_name: app.get_identifier(),
            arguments: Vec::new(),
            parameters: Vec::new(),
            position: self.to_low_position(app.position),
            return_type: self.to_low_type(app.return_type),
        }
    }

    fn to_low_position(
        &self,
        position: vir_crate::middle::ast::position::Position,
    ) -> vir_crate::low::ast::position::Position {
        position.into()
    }

    fn to_low_variable_decl(
        &self,
        decl: vir_crate::middle::ast::variable::VariableDecl,
    ) -> vir_crate::low::ast::variable::VariableDecl {
        vir_crate::low::ast::variable::VariableDecl {
            name: decl.name,
            ty: self.to_low_type(decl.ty),
        }
    }

    fn to_low_vec_trigger(
        &self,
        _: Vec<vir_crate::middle::ast::expression::Trigger>,
    ) -> Vec<vir_crate::low::ast::expression::Trigger> {
        todo!()
    }

    fn to_low_vec_expression(
        &self,
        _: Vec<vir_crate::middle::ast::expression::Expression>,
    ) -> Vec<vir_crate::low::ast::expression::Expression> {
        todo!()
    }

    fn to_low_vec_variable_decl(
        &self,
        _: Vec<vir_crate::middle::ast::variable::VariableDecl>,
    ) -> Vec<vir_crate::low::ast::variable::VariableDecl> {
        todo!()
    }

    fn to_low_quantifier_kind_exists(&self) -> vir_crate::low::ast::expression::QuantifierKind {
        todo!()
    }

    fn to_low_quantifier_kind_for_all(&self) -> vir_crate::low::ast::expression::QuantifierKind {
        todo!()
    }

    fn to_low_type(&self, ty: vir_crate::middle::ast::ty::Type) -> vir_crate::low::ast::ty::Type {
        // TODO: This currently does not take into account snapshots, places,
        // addresses, etc.
        use vir_crate::{low::ast::ty::Type as LType, middle::ast::ty::Type as MType};
        match ty {
            MType::MBool => LType::Bool,
            MType::MInt => LType::Int,
            MType::MFloat32 => LType::Float(vir_crate::low::ast::ty::Float::F32),
            MType::MFloat64 => LType::Float(vir_crate::low::ast::ty::Float::F64),
            MType::Bool
            | MType::Int(_)
            | MType::Float(_)
            | MType::TypeVar(_)
            | MType::Tuple(_)
            | MType::Struct(_)
            | MType::Enum(_)
            | MType::Union(_)
            | MType::Array(_)
            | MType::Slice(_)
            | MType::Reference(_)
            | MType::Pointer(_)
            | MType::FnPointer
            | MType::Never
            | MType::Str
            | MType::Closure(_)
            | MType::FunctionDef(_)
            | MType::Projection(_)
            | MType::Unsupported(_) => LType::Ref,
        }
    }

    fn to_low_container_op_kind_seq_len(&self) -> vir_crate::low::ast::expression::ContainerOpKind {
        todo!()
    }

    fn to_low_container_op_kind_seq_concat(
        &self,
    ) -> vir_crate::low::ast::expression::ContainerOpKind {
        todo!()
    }

    fn to_low_container_op_kind_seq_index(
        &self,
    ) -> vir_crate::low::ast::expression::ContainerOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_implies(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_or(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_and(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_mod(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_div(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_mul(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_sub(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_add(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_le_cmp(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_lt_cmp(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_ge_cmp(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_gt_cmp(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_ne_cmp(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_binary_op_kind_eq_cmp(&self) -> vir_crate::low::ast::expression::BinaryOpKind {
        todo!()
    }

    fn to_low_unary_op_kind_minus(&self) -> vir_crate::low::ast::expression::UnaryOpKind {
        todo!()
    }

    fn to_low_unary_op_kind_not(&self) -> vir_crate::low::ast::expression::UnaryOpKind {
        todo!()
    }

    fn to_low_constant_value_fn_ptr(&self) -> vir_crate::low::ast::expression::ConstantValue {
        todo!()
    }

    fn to_low_float_const(
        &self,
        _ty: vir_crate::middle::ast::expression::FloatConst,
    ) -> vir_crate::low::ast::expression::FloatConst {
        todo!()
    }

    fn to_low_string(&self, _ty: String) -> String {
        todo!()
    }

    fn to_low_bool(&self, _ty: bool) -> bool {
        todo!()
    }

    fn to_low_expression_addr_of(
        &self,
        _variant: vir_crate::middle::ast::expression::AddrOf,
    ) -> vir_crate::low::ast::expression::Expression {
        todo!()
    }

    fn to_low_expression_deref(
        &self,
        _variant: vir_crate::middle::ast::expression::Deref,
    ) -> vir_crate::low::ast::expression::Expression {
        todo!()
    }

    fn to_low_field_decl(
        &self,
        _ty: vir_crate::middle::ast::field::FieldDecl,
    ) -> vir_crate::low::ast::field::FieldDecl {
        todo!()
    }

    fn to_low_expression_variant(
        &self,
        _variant: vir_crate::middle::ast::expression::Variant,
    ) -> vir_crate::low::ast::expression::Expression {
        todo!()
    }

    fn to_low_expression_constructor(
        &self,
        _variant: vir_crate::middle::ast::expression::Constructor,
    ) -> vir_crate::low::ast::expression::Expression {
        todo!()
    }
}
