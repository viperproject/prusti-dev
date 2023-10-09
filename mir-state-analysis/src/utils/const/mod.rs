// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

// This module is not used, and instead we use https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/struct.Promoted.html.
// I've kept this around as a skeleton for working with `ConstValue` and `ConstAlloc` if we ever need that in the future.

use prusti_rustc_interface::{
    abi::{HasDataLayout, Size, Variants, TargetDataLayout, TagEncoding, VariantIdx},
    borrowck::{
        borrow_set::BorrowData,
        consumers::{BorrowIndex, OutlivesConstraint, RichLocation},
    },
    data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet},
    dataflow::fmt::DebugWithContext,
    index::{bit_set::BitSet, IndexVec},
    middle::{
        mir::{
            interpret::{
                alloc_range, AllocId, AllocRange, Allocation, ConstAllocation, ConstValue,
                GlobalAlloc, Scalar,
            },
            visit::Visitor,
            BasicBlock, Constant, ConstantKind, ConstraintCategory, Local, Location, Operand,
            Place as MirPlace, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
            RETURN_PLACE,
        },
        ty::{
            FloatTy, GenericArgKind, Instance, ParamEnv, ParamEnvAnd, RegionVid, ScalarInt, Ty,
            TyKind, layout::{TyAndLayout, LayoutError, HasTyCtxt, HasParamEnv}, TyCtxt, FieldDef,
        },
    },
};

use super::PlaceRepacker;

/// Do not use, see note at the top of this module
pub struct EvaluatedConst<'tcx> {
    ty: Ty<'tcx>,
    kind: EcKind<'tcx>,
}

impl<'tcx> std::fmt::Debug for EvaluatedConst<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.kind.fmt(f)
    }
}

#[derive(Debug)]
pub enum EcKind<'tcx> {
    // Primitive
    Bool(bool),
    Int(i128),
    Uint(u128), // Note: Also includes `char`
    Float(f64), // Note: it is lossless to store a `f32` in a `f64`
    Str(&'tcx str),
    // Other
    ZeroSized, // Get info from `ty`
    Function(Instance<'tcx>),
    // Compound
    Array(Vec<EvaluatedConst<'tcx>>),
    Adt(VariantIdx, Vec<(&'tcx FieldDef, EvaluatedConst<'tcx>)>),
    // Reference/Pointer
    Pointer(Option<Box<EvaluatedConst<'tcx>>>),
}

impl<'tcx> EcKind<'tcx> {
    pub fn to_bits(&self) -> Option<u128> {
        match *self {
            EcKind::Int(value) => Some(value as u128),
            EcKind::Uint(value) => Some(value),
            _ => None,
        }
    }
}

pub trait ConstEval<'tcx> {
    fn eval(self, rp: PlaceRepacker<'_, 'tcx>) -> EvaluatedConst<'tcx>;
}

impl<'tcx> ConstEval<'tcx> for Constant<'tcx> {
    fn eval(self, rp: PlaceRepacker<'_, 'tcx>) -> EvaluatedConst<'tcx> {
        let param_env = rp.tcx().param_env(rp.body().source.def_id());
        let eval = self.literal.eval(rp.tcx(), param_env, None);
        assert!(!(self.literal.try_to_scalar().is_some() && eval.is_err()));
        // let eval = eval.ok()?;
        // TODO: find a good way to resolve errors here
        let eval = eval.unwrap();
        eval.eval(self.ty(), rp)
    }
}

pub trait ConstEvalTy<'tcx> {
    fn eval(self, ty: Ty<'tcx>, rp: PlaceRepacker<'_, 'tcx>) -> EvaluatedConst<'tcx>;
}

impl<'tcx> ConstEvalTy<'tcx> for ConstValue<'tcx> {
    fn eval(self, ty: Ty<'tcx>, rp: PlaceRepacker<'_, 'tcx>) -> EvaluatedConst<'tcx> {
        println!("const {self:?}, ty: {ty:?}");
        match self {
            ConstValue::Scalar(scalar) => scalar.eval(ty, rp),
            ConstValue::ZeroSized => EvaluatedConst {
                ty,
                kind: EcKind::ZeroSized,
            },
            ConstValue::Slice { data, start, end } => {
                let inner_ty = ty.builtin_deref(true).unwrap().ty;
                let range = alloc_range(Size::from_bytes(start), Size::from_bytes(end - start));
                eval_range(data, range, inner_ty, rp)
            }
            ConstValue::Indirect { alloc_id, offset } => {
                let alloc = rp.tcx().global_alloc(alloc_id).unwrap_memory();
                let size = alloc.inner().size() - offset;
                eval_range(alloc, alloc_range(offset, size), ty, rp)
            }
        }
    }
}

impl<'tcx> ConstEvalTy<'tcx> for Scalar {
    fn eval(self, ty: Ty<'tcx>, rp: PlaceRepacker<'_, 'tcx>) -> EvaluatedConst<'tcx> {
        println!("scalar {self:?}, ty: {ty:?}");
        match self {
            Scalar::Int(bytes) => bytes.eval(ty, rp),
            Scalar::Ptr(ptr, _) => {
                match rp.tcx().global_alloc(ptr.provenance) {
                    GlobalAlloc::Function(instance) => EvaluatedConst {
                        ty,
                        kind: EcKind::Function(instance),
                    },
                    GlobalAlloc::VTable(_, _) => todo!(),
                    GlobalAlloc::Static(_) => todo!(),
                    GlobalAlloc::Memory(mem) => {
                        // If the `unwrap` ever panics we need a different way to get the inner type
                        // let inner_ty = ty.builtin_deref(true).map(|t| t.ty).unwrap_or(ty);
                        let inner_ty = ty.builtin_deref(true).unwrap().ty;
                        let inner = Box::new(mem.eval(inner_ty, rp));
                        EvaluatedConst {
                            ty,
                            kind: EcKind::Pointer(Some(inner)),
                        }
                    }
                }
            }
        }
    }
}

impl<'tcx> ConstEvalTy<'tcx> for ScalarInt {
    fn eval(self, ty: Ty<'tcx>, _rp: PlaceRepacker<'_, 'tcx>) -> EvaluatedConst<'tcx> {
        let kind = match ty.kind() {
            TyKind::Bool => EcKind::Bool(self.try_to_bool().unwrap()),
            TyKind::Int(_) => EcKind::Int(self.try_to_int(self.size()).unwrap()),
            TyKind::Char | TyKind::Uint(_) => EcKind::Uint(self.try_to_uint(self.size()).unwrap()),
            TyKind::Float(FloatTy::F32) => {
                let float = f32::from_bits(self.try_to_u32().unwrap());
                EcKind::Float(f64::from(float)) // Lossless conversion, see https://doc.rust-lang.org/std/primitive.f32.html#method.from-3
            }
            TyKind::Float(FloatTy::F64) => {
                EcKind::Float(f64::from_bits(self.try_to_u64().unwrap()))
            }
            _ => unreachable!("ScalarInt::eval: {self:?}, ty: {ty:?}"),
        };
        EvaluatedConst { ty, kind }
    }
}

impl<'tcx> ConstEvalTy<'tcx> for ConstAllocation<'tcx> {
    fn eval(self, ty: Ty<'tcx>, rp: PlaceRepacker<'_, 'tcx>) -> EvaluatedConst<'tcx> {
        let range = alloc_range(Size::ZERO, self.inner().size());
        eval_range(self, range, ty, rp)
    }
}

fn eval_range<'tcx>(
    ca: ConstAllocation<'tcx>,
    range: AllocRange,
    ty: Ty<'tcx>,
    rp: PlaceRepacker<'_, 'tcx>,
) -> EvaluatedConst<'tcx> {
    println!("ca {ca:?}, ty: {ty:?}, range: {range:?}");
    match ty.kind() {
        TyKind::Str => {
            let peat = ParamEnvAnd {
                param_env: ParamEnv::reveal_all(),
                value: ty,
            };
            let layout = rp.tcx().layout_of(peat).unwrap();
            println!("layout: {layout:?}");

            // Cannot use `read_scalar` here: it panics if the allocation size is larger
            // than can fit in u128 as it cannot create a `Scalar::Int` for the data.
            let value = ca
                .inner()
                .get_bytes_strip_provenance(&rp.tcx(), range)
                .unwrap();
            EvaluatedConst {
                ty,
                kind: EcKind::Str(std::str::from_utf8(value).unwrap()),
            }
        }
        &TyKind::Array(elem_ty, _) | &TyKind::Slice(elem_ty) => {
            let layout = layout_of(elem_ty, rp).unwrap();
            // println!("layout: {layout:?}");
            assert_eq!(range.size.bits() % layout.size.bits(), 0);
            let elements = range.size.bits() / layout.size.bits();
            let values = (0..elements)
                .map(|idx| layout.size.checked_mul(idx, &rp.tcx()).unwrap())
                .map(|offset| range.subrange(alloc_range(offset, layout.size)))
                .map(|subrange| eval_range(ca, subrange, elem_ty, rp))
                .collect();
            EvaluatedConst {
                ty,
                kind: EcKind::Array(values),
            }
        }
        // Always zero-sized, closures with captured state aren't const?
        TyKind::FnDef(..) | TyKind::Closure(..) => {
            assert_eq!(range.size.bits(), 0);
            EvaluatedConst {
                ty,
                kind: EcKind::ZeroSized,
            }
        }
        TyKind::Adt(adt, sub) if adt.variants().is_empty() => {
            todo!()
        }
        TyKind::Adt(adt, sub) => {
            if range.size.bits() == 0 {
                return EvaluatedConst {
                    ty,
                    kind: EcKind::ZeroSized,
                };
            }
            let cx = &RevealAllEnv::from(rp);
            let adt_layout = layout_of(ty, rp).unwrap();
            let index = match adt_layout.variants {
                Variants::Single { index } => index,
                Variants::Multiple { tag, ref tag_encoding, tag_field, ref variants } => {
                    let discr_type = ty.discriminant_ty(rp.tcx());
                    // TODO: compare with `tag.primitive().to_int_ty(rp.tcx())`

                    let discr_offset = adt_layout.fields.offset(tag_field);
                    let discr_layout = adt_layout.field(cx, tag_field);
                    // TODO: compare with `layout_of(discr_type, rp).unwrap()`
                    let discr_range = range.subrange(alloc_range(discr_offset, discr_layout.size));
                    let discr_bits = eval_range(ca, discr_range, discr_type, rp);
                    let discr_bits = discr_bits.kind.to_bits().unwrap();
                    match *tag_encoding {
                        TagEncoding::Direct => {
                            adt.discriminants(rp.tcx()).find(|(_, var)| var.val == discr_bits).unwrap().0
                        }
                        TagEncoding::Niche { untagged_variant, ref niche_variants, niche_start } => {
                            let variants_start = niche_variants.start().as_u32();
                            let variants_end = niche_variants.end().as_u32();
                            let variant_index_relative = discr_bits - niche_start;
                            if variant_index_relative <= u128::from(variants_end - variants_start) {
                                // We should now be within the `u32` range.
                                let variant_index_relative = u32::try_from(variant_index_relative).unwrap();
                                VariantIdx::from_u32(variants_start.checked_add(variant_index_relative).unwrap())
                            } else {
                                untagged_variant
                            }
                        }
                    }
                }
            };
            let layout = adt_layout.for_variant(cx, index);
            let variant = adt.variant(index);
            let fields = variant.fields.iter_enumerated().map(|(idx, val)| {
                let field = layout.field(cx, idx.as_usize());
                let range = range.subrange(alloc_range(layout.fields.offset(idx.as_usize()), field.size));
                (val, eval_range(ca, range, val.ty(rp.tcx(), sub), rp))
            }).collect();
            EvaluatedConst {
                ty,
                kind: EcKind::Adt(index, fields),
            }
        }
        TyKind::Tuple(_) => todo!(),
        // Note: `TyKind::FnPtr` will lead to `GlobalAlloc::Function`
        _ => {
            assert!(
                range.size.bits() <= u128::BITS.into(),
                "{ty:?}, {range:?}: {:?} / {:?}",
                ca.inner().init_mask(),
                ca.inner().provenance()
            );
            let mut range = range;
            let is_ptr = ty.is_any_ptr();// !ca.inner().provenance().range_empty(range, &rp.tcx());
            if is_ptr {
                let ptr_size = rp.tcx().data_layout().pointer_size;
                if ptr_size != range.size {
                    // For some reason all pointer allocations get reported as
                    // `16 bytes` even though they are actually `8 bytes`.
                    assert_eq!(range.size.bits(), ptr_size.bits() * 2);
                    range.size = ptr_size;
                }
                if ca.inner().provenance().range_empty(range, &rp.tcx()) {
                    assert!(ty.is_unsafe_ptr());
                    return EvaluatedConst {
                        ty,
                        kind: EcKind::Pointer(None),
                    };
                }
            }
            assert_eq!(is_ptr, ty.is_any_ptr(), "({range:?}, {is_ptr}, {ty:?}): {:?} / {:?}", ca.inner().init_mask(), ca.inner().provenance());
            match ca.inner().read_scalar(&rp.tcx(), range, is_ptr) {
                Ok(scalar) => scalar.eval(ty, rp),
                Err(err) => panic!(
                    "{err:?} ({range:?}, {is_ptr}, {ty:?}): {:?} / {:?}",
                    ca.inner().init_mask(),
                    ca.inner().provenance()
                ),
            }
        }
    }

    // println!(
    //     "Range: {range:?}, is_ptr: {is_ptr}, pointer_size: {:?}",
    //     rp.tcx().data_layout().pointer_size
    // );
    // let bytes = self.inspect_with_uninit_and_ptr_outside_interpreter(0..self.len());
    // let provenance = self.provenance();
    // println!("inner: {:?}, extra: {:?}, provenance {:?}", bytes, self.extra, provenance);
    // for (_, ptr) in provenance.ptrs().iter() {}
}

fn layout_of<'tcx>(ty: Ty<'tcx>, rp: PlaceRepacker<'_, 'tcx>) -> Result<TyAndLayout<'tcx>, &'tcx LayoutError<'tcx>> {
    let peat = ParamEnvAnd {
        param_env: ParamEnv::reveal_all(),
        value: ty,
    };
    rp.tcx().layout_of(peat)
}

struct RevealAllEnv<'a, 'tcx>(PlaceRepacker<'a, 'tcx>);
impl HasDataLayout for RevealAllEnv<'_, '_> {
    fn data_layout(&self) -> &TargetDataLayout {
        self.0.tcx.data_layout()
    }
}
impl<'tcx> HasTyCtxt<'tcx> for RevealAllEnv<'_, 'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.0.tcx()
    }
}
impl<'tcx> HasParamEnv<'tcx> for RevealAllEnv<'_, 'tcx> {
    fn param_env(&self) -> ParamEnv<'tcx> {
        ParamEnv::reveal_all()
    }
}
impl<'a, 'tcx> From<PlaceRepacker<'a, 'tcx>> for RevealAllEnv<'a, 'tcx> {
    fn from(rp: PlaceRepacker<'a, 'tcx>) -> Self {
        Self(rp)
    }
}
