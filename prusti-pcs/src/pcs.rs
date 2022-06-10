use rustc_data_structures::stable_set::FxHashSet;
use rustc_middle::{
    mir::{FakeReadCause, Local, Place},
    ty::Const,
};
use rustc_target::abi::VariantIdx;

#[allow(dead_code)]
/// Expanded MIR with explicit instructions
//  pub struct OperationalMir<'tcx> {
//      pub statements: Vec<PCSMirStatement<'tcx>>,
//      pub terminator: PCSMirTerminator,
//  }
//
//  pub struct PCSMirStatement<'tcx> {
//      pub kind: PCSMirStatementKind<'tcx>,
//  }
//
//  pub enum PCSMirStatementKind<'tcx> {
//      SetShared(Box<(Place<'tcx>, GenPlace<'tcx>)>),
//      SetMut(Box<(Place<'tcx>, GenPlace<'tcx>)>),
//      Const(Box<(Place<'tcx>, Const<'tcx>)>),
//      UndeterminedKill(Place<'tcx>),
//      FakeRead(Box<(FakeReadCause, Place<'tcx>)>),
//      SetDiscriminant {
//          place: Box<Place<'tcx>>,
//          variant_index: VariantIdx,
//      },
//      Nop,
//      Deinit(Box<Place<'tcx>>),
//      StorageLive(Local),
//      StorageDead(Local),
//      // Retag(RetagKind, Box<Place<'tcx>>),
//      // AscribeUserType(Box<(Place<'tcx>, UserTypeProjection)>, Variance),
//      // Coverage(Box<Coverage>),
//      // CopyNonOverlapping(Box<CopyNonOverlapping<'tcx>>),
//  }
//
//  // Place with optional temporaries added to it. Used for the RHS of an assignment.
//  // tmp_projection 0 is the place itself.
//  pub struct GenPlace<'tcx> {
//      place: Place<'tcx>,
//      tmp_projection: u32,
//  }
//
//  pub enum PCSPermission<'tcx> {
//      Uninit(GenPlace<'tcx>),
//      Shared(GenPlace<'tcx>),
//      Exclusive(GenPlace<'tcx>),
//  }
//
//  impl<'tcx> PCSMirStatementKind<'tcx> {
//      // INVARIANT: For any PCS annotation PCSMir, each statement's predecessor's must have at
//      //      least it's core_preconditions and it's successor at least it's core_postconditions
//
//      fn core_preconditions(&self) -> FxHashSet<PCSPermission<'tcx>> {
//          match self {
//              PCSMirStatementKind::SetShared(_) => todo!(),
//              PCSMirStatementKind::SetMut(_) => todo!(),
//              PCSMirStatementKind::Const(_) => todo!(),
//              PCSMirStatementKind::Kill(_) => todo!(),
//          }
//      }
//
//      fn core_postconditions(&self) -> FxHashSet<PCSPermission<'tcx>> {
//          match self {
//              PCSMirStatementKind::SetShared(_) => todo!(),
//              PCSMirStatementKind::SetMut(_) => todo!(),
//              PCSMirStatementKind::Const(_) => todo!(),
//              PCSMirStatementKind::Kill(_) => todo!(),
//          }
//      }
//  }
//
//  pub struct PCSMirTerminator {}

pub fn init_analysis() {}

// TODO ITEMS:
//   Prefix invariant in init semantics
//   Operational translation
//   Calling the conditional analysis (refactored for operational MIR)
//   Kill elaboration into MicroMir
