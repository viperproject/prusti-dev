#[allow(dead_code)]
/// MIR for use in operational style semantics
enum OperationalMir {}

#[allow(dead_code)]
/// Expanded MIR with explicit instructions
enum MicroMir {}

pub fn init_analysis() {}

// TODO ITEMS:
//   Prefix invariant in init semantics
//   Operational translation
//   Calling the conditional analysis (refactored for operational MIR)
//   Kill elaboration into MicroMir
