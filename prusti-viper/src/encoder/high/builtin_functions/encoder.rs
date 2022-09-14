use super::interface::BuiltinFunctionHighKind;
use vir_crate::{
    common::expression::BinaryOperationHelpers,
    high::{self as vir_high},
};

pub(super) fn encode_builtin_function_def(kind: BuiltinFunctionHighKind) -> vir_high::FunctionDecl {
    let (fn_name, type_arguments) = encode_builtin_function_name_with_type_args(&kind);
    match kind {
        BuiltinFunctionHighKind::Unreachable(ty) => vir_high::FunctionDecl {
            name: fn_name,
            type_arguments,
            parameters: vec![],
            return_type: ty,
            // Precondition is false, because we want to be sure that this function is never used
            pres: vec![false.into()],
            posts: vec![],
            body: None,
        },
        BuiltinFunctionHighKind::Undefined(ty) => vir_high::FunctionDecl {
            name: fn_name,
            type_arguments,
            parameters: vec![],
            return_type: ty,
            pres: vec![],
            posts: vec![],
            body: None,
        },
        BuiltinFunctionHighKind::ArrayLookupPure {
            array_pred_type,
            array_len,
            return_ty,
            ..
        } => {
            let self_var = vir_high::VariableDecl::new("self", array_pred_type);
            let idx_var = vir_high::VariableDecl::new("idx", vir_high::Type::MInt);

            vir_high::FunctionDecl {
                name: fn_name,
                type_arguments,
                parameters: vec![
                    // self,
                    self_var,
                    // idx,
                    idx_var.clone(),
                ],
                return_type: return_ty,
                pres: vec![
                    // 0 <= idx < {len}
                    vir_high::Expression::less_equals(0.into(), idx_var.clone().into()),
                    vir_high::Expression::less_than(idx_var.into(), array_len.into()),
                ],
                posts: vec![],
                body: None,
            }
        }
        BuiltinFunctionHighKind::SliceLookupPure {
            slice_pred_type,
            elem_pred_type,
            return_ty,
        } => {
            let (slice_len, slice_len_type_arguments) =
                encode_builtin_function_name_with_type_args(&BuiltinFunctionHighKind::SliceLen {
                    slice_pred_type: slice_pred_type.clone(),
                    elem_pred_type,
                });
            let self_var = vir_high::VariableDecl::new("self", slice_pred_type);
            let idx_var = vir_high::VariableDecl::new("idx", vir_high::Type::MInt);

            let slice_len_call = vir_high::Expression::func_app(
                slice_len,
                slice_len_type_arguments,
                vec![self_var.clone().into()],
                vec![self_var.clone()],
                vir_high::Type::MInt,
                vir_high::Position::default(),
            );

            vir_high::FunctionDecl {
                name: fn_name,
                type_arguments,
                parameters: vec![self_var, idx_var.clone()],
                return_type: return_ty,
                pres: vec![
                    // 0 <= idx < Slice${ty}$len(self)
                    vir_high::Expression::less_equals(0.into(), idx_var.clone().into()),
                    vir_high::Expression::less_than(idx_var.into(), slice_len_call),
                ],
                posts: vec![],
                body: None,
            }
        }
        BuiltinFunctionHighKind::SliceLen {
            slice_pred_type, ..
        } => {
            let self_var = vir_high::VariableDecl::self_variable(slice_pred_type);
            let result_var = vir_high::VariableDecl::result_variable(vir_high::Type::MInt);

            vir_high::FunctionDecl {
                name: fn_name,
                type_arguments,
                parameters: vec![self_var],
                return_type: vir_high::Type::MInt,
                pres: vec![],
                posts: vec![
                    vir_high::Expression::less_equals(0.into(), result_var.clone().into()),
                    // TODO: We should use a symbolic value for usize::MAX.
                    vir_high::Expression::less_equals(result_var.into(), usize::MAX.into()),
                ],
                body: None,
            }
        }
    }
}

pub(super) fn encode_builtin_function_name_with_type_args(
    kind: &BuiltinFunctionHighKind,
) -> (String, Vec<vir_high::Type>) {
    match kind {
        BuiltinFunctionHighKind::Unreachable(typ) => {
            ("builtin$unreach".to_string(), vec![typ.clone()])
        }
        BuiltinFunctionHighKind::Undefined(typ) => ("builtin$undef".to_string(), vec![typ.clone()]),
        BuiltinFunctionHighKind::ArrayLookupPure {
            array_pred_type: container_type,
            elem_pred_type,
            ..
        }
        | BuiltinFunctionHighKind::SliceLookupPure {
            slice_pred_type: container_type,
            elem_pred_type,
            ..
        } => (
            "lookup_pure".to_string(),
            vec![container_type.clone(), elem_pred_type.clone()],
        ),
        BuiltinFunctionHighKind::SliceLen { elem_pred_type, .. } => {
            ("Slice$len".to_string(), vec![elem_pred_type.clone()])
        }
    }
}
