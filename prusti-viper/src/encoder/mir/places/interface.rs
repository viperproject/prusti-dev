use crate::encoder::{
    encoder::SubstMap,
    errors::{
        EncodingError, EncodingResult, ErrorCtxt, SpannedEncodingError, SpannedEncodingResult,
        WithSpan,
    },
    high::pure_functions::HighPureFunctionEncoderInterface,
    mir::{constants::ConstantsEncoderInterface, types::MirTypeEncoderInterface},
};
use log::debug;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir, span_bug, ty};
use rustc_span::Span;
use vir_crate::{
    common::expression::{BinaryOperationHelpers, UnaryOperationHelpers},
    high::{self as vir_high, operations::ty::Typed},
};

trait PlacesEncoderInterfacePrivate<'tcx> {}

impl<'v, 'tcx: 'v> PlacesEncoderInterfacePrivate<'tcx> for super::super::super::Encoder<'v, 'tcx> {}

pub(crate) trait PlacesEncoderInterface<'tcx> {
    fn is_local_copy(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<bool>;

    fn get_local_span(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<Span>;

    fn get_local_type(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<ty::Ty<'tcx>>;

    fn get_operand_type(
        &self,
        mir: &mir::Body<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> SpannedEncodingResult<ty::Ty<'tcx>>;

    fn encode_local_name(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<String>;

    fn encode_local_high(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<vir_high::VariableDecl>;

    fn encode_place_high(
        &self,
        mir: &mir::Body<'tcx>,
        place: mir::Place<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression>;

    fn encode_type_of_place_high(
        &self,
        mir: &mir::Body<'tcx>,
        place: mir::Place<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Type>;

    fn encode_operand_high(
        &self,
        mir: &mir::Body<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> EncodingResult<vir_high::Expression>;

    fn encode_operand_place_high(
        &self,
        mir: &mir::Body<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> EncodingResult<Option<vir_high::Expression>>;

    fn encode_unary_op_high(
        &self,
        op: mir::UnOp,
        operand: vir_high::Expression,
        ty: &vir_high::Type,
    ) -> EncodingResult<vir_high::Expression>;

    fn encode_binary_op_high(
        &self,
        op: mir::BinOp,
        left: vir_high::Expression,
        right: vir_high::Expression,
        ty: &vir_high::Type,
    ) -> EncodingResult<vir_high::Expression>;

    fn encode_binary_op_check_high(
        &self,
        op: mir::BinOp,
        left: vir_high::Expression,
        right: vir_high::Expression,
        ty: &vir_high::Type,
    ) -> EncodingResult<vir_high::Expression>;

    fn encode_cast_expression_high(
        &self,
        mir: &mir::Body<'tcx>,
        def_id: DefId,
        operand: &mir::Operand<'tcx>,
        dst_ty: &ty::Ty<'tcx>,
        tymap: &SubstMap<'tcx>,
        span: Span,
    ) -> SpannedEncodingResult<vir_high::Expression>;
}

impl<'v, 'tcx: 'v> PlacesEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn is_local_copy(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<bool> {
        let mir_type = self.get_local_type(mir, local)?;
        Ok(self.env().type_is_copy(mir_type))
    }

    fn get_local_span(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<Span> {
        Ok(mir.local_decls[local].source_info.span)
    }

    fn get_local_type(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<ty::Ty<'tcx>> {
        Ok(mir.local_decls[local].ty)
    }

    fn get_operand_type(
        &self,
        mir: &mir::Body<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> SpannedEncodingResult<ty::Ty<'tcx>> {
        Ok(operand.ty(mir, self.env().tcx()))
    }

    fn encode_local_name(
        &self,
        _mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<String> {
        Ok(format!("{:?}", local))
    }

    fn encode_local_high(
        &self,
        mir: &mir::Body<'tcx>,
        local: mir::Local,
    ) -> SpannedEncodingResult<vir_high::VariableDecl> {
        let name = self.encode_local_name(mir, local)?;
        let mir_type = self.get_local_type(mir, local)?;
        let ty = self.encode_type_high(mir_type)?;
        let variable_decl = vir_high::VariableDecl { name, ty };
        Ok(variable_decl)
    }

    fn encode_place_high(
        &self,
        mir: &mir::Body<'tcx>,
        place: mir::Place<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let root = self.encode_local_high(mir, place.local)?;
        let span = self.get_local_span(mir, place.local)?;
        let mut expr = vir_high::Expression::local_no_pos(root);
        for (i, element) in place.projection.iter().enumerate() {
            let mir_type = {
                let place_ref = mir::PlaceRef {
                    local: place.local,
                    projection: &place.projection[..i + 1],
                };
                place_ref.ty(mir, self.env().tcx())
            };
            let ty = self.encode_place_type_high(mir_type).with_span(span)?;
            expr = match element {
                mir::ProjectionElem::Deref => vir_high::Expression::deref_no_pos(expr, ty),
                mir::ProjectionElem::Field(field, _) => {
                    let parent_mir_type = {
                        let prev_place_ref = mir::PlaceRef {
                            local: place.local,
                            projection: &place.projection[..i],
                        };
                        prev_place_ref.ty(mir, self.env().tcx())
                    };
                    let parent_type = self
                        .encode_place_type_high(parent_mir_type)
                        .with_span(span)?;
                    let encoded_field = self.encode_field(&parent_type, field).with_span(span)?;
                    vir_high::Expression::field_no_pos(expr, encoded_field)
                }
                mir::ProjectionElem::Index(index) => {
                    debug!("index: {:?}[{:?}]", expr, index);
                    let encoded_index = self.encode_local_high(mir, index)?.into();
                    self.encode_index_call(expr, encoded_index)
                        .with_span(span)?
                }
                mir::ProjectionElem::ConstantIndex {
                    offset,
                    from_end: false,
                    ..
                } => {
                    debug!("constantindex: {:?}[{}]", expr, offset);
                    let encoded_index = offset.into();
                    self.encode_index_call(expr, encoded_index)
                        .with_span(span)?
                }
                mir::ProjectionElem::ConstantIndex {
                    offset,
                    from_end: true,
                    ..
                } => {
                    debug!("constantindex: {:?}[len - {}]", expr, offset);
                    unimplemented!("TODO: Unify encoding of slices and arrays.");
                }
                // ConstantIndex {
                //     offset: u64,
                //     min_length: u64,
                //     from_end: bool,
                // },
                // Subslice {
                //     from: u64,
                //     to: u64,
                //     from_end: bool,
                // },
                mir::ProjectionElem::Downcast(Some(symbol), _variant) => {
                    let variant_index = symbol.as_str().to_string().into();
                    vir_high::Expression::variant_no_pos(expr, variant_index, ty)
                }
                _ => unimplemented!("element: {:?}", element),
            }
        }
        Ok(expr)
    }

    fn encode_type_of_place_high(
        &self,
        mir: &mir::Body<'tcx>,
        place: mir::Place<'tcx>,
    ) -> SpannedEncodingResult<vir_high::Type> {
        let span = self.get_local_span(mir, place.local)?;
        let mir_type = place.ty(mir, self.env().tcx());
        self.encode_place_type_high(mir_type).with_span(span)
    }

    fn encode_operand_high(
        &self,
        mir: &mir::Body<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> EncodingResult<vir_high::Expression> {
        let expr = match operand {
            mir::Operand::Move(place) | mir::Operand::Copy(place) => {
                self.encode_place_high(mir, *place)?
            }
            mir::Operand::Constant(constant) => self.encode_constant_high(constant)?,
        };
        Ok(expr)
    }

    fn encode_operand_place_high(
        &self,
        mir: &mir::Body<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> EncodingResult<Option<vir_high::Expression>> {
        let result = match operand {
            mir::Operand::Move(place) | mir::Operand::Copy(place) => {
                Some(self.encode_place_high(mir, *place)?)
            }
            &mir::Operand::Constant(_) => None,
        };
        Ok(result)
    }

    fn encode_unary_op_high(
        &self,
        op: mir::UnOp,
        operand: vir_high::Expression,
        _ty: &vir_high::Type,
    ) -> EncodingResult<vir_high::Expression> {
        let result = match op {
            mir::UnOp::Not => vir_high::Expression::not(operand),
            mir::UnOp::Neg => vir_high::Expression::minus(operand),
        };
        Ok(result)
    }

    fn encode_binary_op_high(
        &self,
        op: mir::BinOp,
        left: vir_high::Expression,
        right: vir_high::Expression,
        ty: &vir_high::Type,
    ) -> EncodingResult<vir_high::Expression> {
        let is_bool = ty == &vir_high::Type::Bool;
        Ok(match op {
            mir::BinOp::Eq => vir_high::Expression::equals(left, right),
            mir::BinOp::Ne => vir_high::Expression::not_equals(left, right),
            mir::BinOp::Gt => vir_high::Expression::greater_than(left, right),
            mir::BinOp::Ge => vir_high::Expression::greater_equals(left, right),
            mir::BinOp::Lt => vir_high::Expression::less_than(left, right),
            mir::BinOp::Le => vir_high::Expression::less_equals(left, right),
            mir::BinOp::Add => vir_high::Expression::add(left, right),
            mir::BinOp::Sub => vir_high::Expression::subtract(left, right),
            mir::BinOp::Rem => vir_high::Expression::module(left, right),
            mir::BinOp::Div => vir_high::Expression::divide(left, right),
            mir::BinOp::Mul => vir_high::Expression::multiply(left, right),
            mir::BinOp::BitAnd if is_bool => vir_high::Expression::and(left, right),
            mir::BinOp::BitOr if is_bool => vir_high::Expression::or(left, right),
            mir::BinOp::BitXor if is_bool => vir_high::Expression::xor(left, right),
            mir::BinOp::BitAnd | mir::BinOp::BitOr | mir::BinOp::BitXor => {
                return Err(EncodingError::unsupported(
                    "bitwise operations on non-boolean types are not supported",
                ))
            }
            unsupported_op => {
                return Err(EncodingError::unsupported(format!(
                    "operation '{:?}' is not supported",
                    unsupported_op
                )))
            }
        })
    }

    fn encode_binary_op_check_high(
        &self,
        op: mir::BinOp,
        left: vir_high::Expression,
        right: vir_high::Expression,
        ty: &vir_high::Type,
    ) -> EncodingResult<vir_high::Expression> {
        if !op.is_checkable() || !prusti_common::config::check_overflows() {
            Ok(false.into())
        } else {
            let result = self.encode_binary_op_high(op, left, right, ty)?;
            Ok(match op {
                mir::BinOp::Add | mir::BinOp::Mul | mir::BinOp::Sub => match ty {
                    // Unsigned
                    vir_high::Type::Int(vir_high::ty::Int::U8) => vir_high::Expression::or(
                        vir_high::Expression::less_equals(result.clone(), std::u8::MIN.into()),
                        vir_high::Expression::greater_equals(result, std::u8::MAX.into()),
                    ),
                    vir_high::Type::Int(vir_high::ty::Int::U16) => vir_high::Expression::or(
                        vir_high::Expression::less_equals(result.clone(), std::u16::MIN.into()),
                        vir_high::Expression::greater_equals(result, std::u16::MAX.into()),
                    ),
                    vir_high::Type::Int(vir_high::ty::Int::U32) => vir_high::Expression::or(
                        vir_high::Expression::less_equals(result.clone(), std::u32::MIN.into()),
                        vir_high::Expression::greater_equals(result, std::u32::MAX.into()),
                    ),
                    vir_high::Type::Int(vir_high::ty::Int::U64) => vir_high::Expression::or(
                        vir_high::Expression::less_equals(result.clone(), std::u64::MIN.into()),
                        vir_high::Expression::greater_equals(result, std::u64::MAX.into()),
                    ),
                    vir_high::Type::Int(vir_high::ty::Int::U128) => vir_high::Expression::or(
                        vir_high::Expression::less_equals(result.clone(), std::u128::MIN.into()),
                        vir_high::Expression::greater_equals(result, std::u128::MAX.into()),
                    ),
                    vir_high::Type::Int(vir_high::ty::Int::Usize) => vir_high::Expression::or(
                        vir_high::Expression::less_equals(result.clone(), std::usize::MIN.into()),
                        vir_high::Expression::greater_equals(result, std::usize::MAX.into()),
                    ),
                    // Signed
                    vir_high::Type::Int(vir_high::ty::Int::I8) => vir_high::Expression::or(
                        vir_high::Expression::less_equals(result.clone(), std::i8::MIN.into()),
                        vir_high::Expression::greater_equals(result, std::i8::MAX.into()),
                    ),
                    vir_high::Type::Int(vir_high::ty::Int::I16) => vir_high::Expression::or(
                        vir_high::Expression::less_equals(result.clone(), std::i16::MIN.into()),
                        vir_high::Expression::greater_equals(result, std::i16::MIN.into()),
                    ),
                    vir_high::Type::Int(vir_high::ty::Int::I32) => vir_high::Expression::or(
                        vir_high::Expression::less_equals(result.clone(), std::i32::MIN.into()),
                        vir_high::Expression::greater_equals(result, std::i32::MAX.into()),
                    ),
                    vir_high::Type::Int(vir_high::ty::Int::I64) => vir_high::Expression::or(
                        vir_high::Expression::less_equals(result.clone(), std::i64::MIN.into()),
                        vir_high::Expression::greater_equals(result, std::i64::MAX.into()),
                    ),
                    vir_high::Type::Int(vir_high::ty::Int::I128) => vir_high::Expression::or(
                        vir_high::Expression::less_equals(result.clone(), std::i128::MIN.into()),
                        vir_high::Expression::greater_equals(result, std::i128::MAX.into()),
                    ),
                    vir_high::Type::Int(vir_high::ty::Int::Isize) => vir_high::Expression::or(
                        vir_high::Expression::less_equals(result.clone(), std::isize::MIN.into()),
                        vir_high::Expression::greater_equals(result, std::isize::MAX.into()),
                    ),

                    _ => {
                        return Err(EncodingError::unsupported(format!(
                            "overflow checks are unsupported for operation '{:?}' on type '{:?}'",
                            op, ty,
                        )));
                    }
                },

                mir::BinOp::Shl | mir::BinOp::Shr => {
                    return Err(EncodingError::unsupported(
                        "overflow checks on a shift operation are unsupported",
                    ));
                }

                _ => {
                    return Err(EncodingError::internal(format!(
                        "unexpected overflow check on {:?}",
                        op
                    )))
                }
            })
        }
    }

    fn encode_cast_expression_high(
        &self,
        mir: &mir::Body<'tcx>,
        def_id: DefId,
        operand: &mir::Operand<'tcx>,
        dst_ty: &ty::Ty<'tcx>,
        tymap: &SubstMap<'tcx>,
        span: Span,
    ) -> SpannedEncodingResult<vir_high::Expression> {
        let src_ty = self.get_operand_type(mir, operand)?;

        let encoded_val = match (src_ty.kind(), dst_ty.kind()) {
            // Numeric casts that cannot fail
            (ty::TyKind::Char, ty::TyKind::Char)
            | (ty::TyKind::Char, ty::TyKind::Uint(ty::UintTy::U8))
            | (ty::TyKind::Char, ty::TyKind::Uint(ty::UintTy::U16))
            | (ty::TyKind::Char, ty::TyKind::Uint(ty::UintTy::U32))
            | (ty::TyKind::Char, ty::TyKind::Uint(ty::UintTy::U64))
            | (ty::TyKind::Char, ty::TyKind::Uint(ty::UintTy::U128))
            | (ty::TyKind::Int(ty::IntTy::I8), ty::TyKind::Int(ty::IntTy::I8))
            | (ty::TyKind::Int(ty::IntTy::I8), ty::TyKind::Int(ty::IntTy::I16))
            | (ty::TyKind::Int(ty::IntTy::I8), ty::TyKind::Int(ty::IntTy::I32))
            | (ty::TyKind::Int(ty::IntTy::I8), ty::TyKind::Int(ty::IntTy::I64))
            | (ty::TyKind::Int(ty::IntTy::I8), ty::TyKind::Int(ty::IntTy::I128))
            | (ty::TyKind::Int(ty::IntTy::I16), ty::TyKind::Int(ty::IntTy::I16))
            | (ty::TyKind::Int(ty::IntTy::I16), ty::TyKind::Int(ty::IntTy::I32))
            | (ty::TyKind::Int(ty::IntTy::I16), ty::TyKind::Int(ty::IntTy::I64))
            | (ty::TyKind::Int(ty::IntTy::I16), ty::TyKind::Int(ty::IntTy::I128))
            | (ty::TyKind::Int(ty::IntTy::I32), ty::TyKind::Int(ty::IntTy::I32))
            | (ty::TyKind::Int(ty::IntTy::I32), ty::TyKind::Int(ty::IntTy::I64))
            | (ty::TyKind::Int(ty::IntTy::I32), ty::TyKind::Int(ty::IntTy::I128))
            | (ty::TyKind::Int(ty::IntTy::I64), ty::TyKind::Int(ty::IntTy::I64))
            | (ty::TyKind::Int(ty::IntTy::I64), ty::TyKind::Int(ty::IntTy::I128))
            | (ty::TyKind::Int(ty::IntTy::I128), ty::TyKind::Int(ty::IntTy::I128))
            | (ty::TyKind::Int(ty::IntTy::Isize), ty::TyKind::Int(ty::IntTy::Isize))
            | (ty::TyKind::Uint(ty::UintTy::U8), ty::TyKind::Char)
            | (ty::TyKind::Uint(ty::UintTy::U8), ty::TyKind::Uint(ty::UintTy::U8))
            | (ty::TyKind::Uint(ty::UintTy::U8), ty::TyKind::Uint(ty::UintTy::U16))
            | (ty::TyKind::Uint(ty::UintTy::U8), ty::TyKind::Uint(ty::UintTy::U32))
            | (ty::TyKind::Uint(ty::UintTy::U8), ty::TyKind::Uint(ty::UintTy::U64))
            | (ty::TyKind::Uint(ty::UintTy::U8), ty::TyKind::Uint(ty::UintTy::U128))
            | (ty::TyKind::Uint(ty::UintTy::U16), ty::TyKind::Uint(ty::UintTy::U16))
            | (ty::TyKind::Uint(ty::UintTy::U16), ty::TyKind::Uint(ty::UintTy::U32))
            | (ty::TyKind::Uint(ty::UintTy::U16), ty::TyKind::Uint(ty::UintTy::U64))
            | (ty::TyKind::Uint(ty::UintTy::U16), ty::TyKind::Uint(ty::UintTy::U128))
            | (ty::TyKind::Uint(ty::UintTy::U32), ty::TyKind::Uint(ty::UintTy::U32))
            | (ty::TyKind::Uint(ty::UintTy::U32), ty::TyKind::Uint(ty::UintTy::U64))
            | (ty::TyKind::Uint(ty::UintTy::U32), ty::TyKind::Uint(ty::UintTy::U128))
            | (ty::TyKind::Uint(ty::UintTy::U64), ty::TyKind::Uint(ty::UintTy::U64))
            | (ty::TyKind::Uint(ty::UintTy::U64), ty::TyKind::Uint(ty::UintTy::U128))
            | (ty::TyKind::Uint(ty::UintTy::U128), ty::TyKind::Uint(ty::UintTy::U128))
            | (ty::TyKind::Uint(ty::UintTy::Usize), ty::TyKind::Uint(ty::UintTy::Usize)) => {
                self.encode_operand_high(mir, operand).with_span(span)?
            }

            // Numeric casts where the source value might not fit into the target type
            (ty::TyKind::Char, ty::TyKind::Int(_))
            | (ty::TyKind::Char, ty::TyKind::Uint(_))
            | (ty::TyKind::Int(_), ty::TyKind::Char)
            | (ty::TyKind::Int(_), ty::TyKind::Int(_))
            | (ty::TyKind::Int(_), ty::TyKind::Uint(_))
            | (ty::TyKind::Uint(_), ty::TyKind::Char)
            | (ty::TyKind::Uint(_), ty::TyKind::Int(_))
            | (ty::TyKind::Uint(_), ty::TyKind::Uint(_)) => {
                let encoded_operand = self.encode_operand_high(mir, operand).with_span(span)?;
                if prusti_common::config::check_overflows() {
                    // Check the cast
                    // FIXME: Should use a high function.
                    let function_name = self
                        .encode_cast_function_use(src_ty, dst_ty, tymap)
                        .with_span(span)?;
                    let position = self
                        .error_manager()
                        .register(span, ErrorCtxt::TypeCast, def_id);
                    let return_type = self.encode_type_high(dst_ty)?;
                    let call = vir_high::Expression::function_call(
                        function_name,
                        vec![encoded_operand],
                        return_type,
                    )
                    .set_default_pos(position.into());
                    return Ok(call);
                } else {
                    // Don't check the cast
                    encoded_operand
                }
            }

            _ => {
                return Err(SpannedEncodingError::unsupported(
                    format!(
                        "unsupported cast from type '{:?}' to type '{:?}'",
                        src_ty, dst_ty
                    ),
                    span,
                ));
            }
        };

        Ok(encoded_val)
    }
}
