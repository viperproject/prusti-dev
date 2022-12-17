// © 2022, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::vir::{program::Program, Position};
use fxhash::{FxHashMap, FxHashSet};
use log::{debug, trace};
use viper::VerificationResult;

pub enum NormalizationInfo {
    LegacyProgram { original_position_ids: Vec<u64> },
    LowProgram,
}

impl NormalizationInfo {
    /// Normalize a vir::legacy program. Do nothing for vir::low programs.
    pub fn normalize_program(program: &mut Program) -> Self {
        match program {
            Program::Low(_) => {
                debug!("No normalization is done for vir::low programs.");
                NormalizationInfo::LowProgram
            }
            Program::Legacy(legacy_program) => {
                // Collect positions
                let mut position_ids: FxHashSet<u64> = FxHashSet::default();
                position_ids.insert(Position::default().id()); // Generated by the to_viper pass
                legacy_program.visit_positions(|p| {
                    position_ids.insert(p.id());
                });
                let mut original_position_ids: Vec<u64> = position_ids.into_iter().collect();
                original_position_ids.sort();

                // Remap positions ids to be consecutive starting from zero.
                // TODO: line and columns are not modified; we could remove them from the Position struct.
                let normalization_map: FxHashMap<u64, u64> = original_position_ids
                    .iter()
                    .copied()
                    .enumerate()
                    .map(|(i, pos_id)| (pos_id, i as u64))
                    .collect();
                trace!("Normalization map: {:?}", normalization_map);
                legacy_program.visit_positions_mut(|p| {
                    *p = Position::new(p.line(), p.column(), normalization_map[&p.id()]);
                });

                NormalizationInfo::LegacyProgram {
                    original_position_ids,
                }
            }
        }
    }

    /// Denormalize a position id.
    pub fn denormalize_position_id(&self, pos_id: u64) -> u64 {
        match self {
            NormalizationInfo::LowProgram => pos_id,
            NormalizationInfo::LegacyProgram {
                original_position_ids,
            } => *original_position_ids
                .get(pos_id as usize)
                .unwrap_or_else(|| {
                    panic!(
                        "Cannot denormalize position id {}. Probably it has not been normalized. \
                        There maximum expected normalized position is {}.",
                        pos_id,
                        original_position_ids.len(),
                    )
                }),
        }
    }

    /// Denormalize a position.
    pub fn denormalize_position(&self, pos: Position) -> Position {
        Position::new(
            pos.line(),
            pos.column(),
            self.denormalize_position_id(pos.id()),
        )
    }

    /// Denormalize the verification result.
    pub fn denormalize_program(&self, program: &mut Program) {
        match program {
            Program::Low(_) => debug!("No denormalization is done for vir::low programs."),
            Program::Legacy(legacy_program) => {
                legacy_program.visit_expressions_mut(|e| {
                    e.visit_positions_mut(|p| *p = self.denormalize_position(*p))
                });
            }
        }
    }

    /// Denormalize a position string.
    pub fn denormalize_position_string(&self, pos: &mut String) {
        let pos_id: u64 = pos.parse().unwrap_or_else(|err| {
            panic!(
                "Cannot denormalize position {:?}: parsing error {:?}",
                pos, err
            )
        });
        *pos = self.denormalize_position_id(pos_id).to_string();
    }

    /// Denormalize a verification result.
    pub fn denormalize_result(&self, result: &mut VerificationResult) {
        if let VerificationResult::Failure(ref mut ver_errors) = result {
            ver_errors.iter_mut().for_each(|ver_error| {
                if let Some(pos) = ver_error.pos_id.as_mut() {
                    self.denormalize_position_string(pos);
                }
                if let Some(pos) = ver_error.offending_pos_id.as_mut() {
                    self.denormalize_position_string(pos);
                }
                if let Some(pos) = ver_error.reason_pos_id.as_mut() {
                    self.denormalize_position_string(pos);
                }
            });
        }
    }
}
