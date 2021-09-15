use vir_crate::polymorphic::{CfgBlockIndex, Expr, Successor};
use prusti_interface::environment::BasicBlockIndex;

#[derive(Eq, PartialEq, Clone, Debug)]
pub enum MirSuccessor {
    /// A return statements
    Return,
    /// A dead path (after an `assert false` or `assume false`)
    Kill,
    Goto(BasicBlockIndex),
    GotoSwitch(Vec<(Expr, BasicBlockIndex)>, BasicBlockIndex),
}

impl MirSuccessor {
    pub fn targets(&self) -> Vec<BasicBlockIndex> {
        match self {
            MirSuccessor::Return | MirSuccessor::Kill => vec![],
            MirSuccessor::Goto(target) => vec![*target],
            MirSuccessor::GotoSwitch(guarded_targets, default) => {
                let mut targets = vec![*default];
                for (_, target) in guarded_targets {
                    targets.push(*target);
                }
                targets
            }
        }
    }

    pub fn encode<F: FnMut(BasicBlockIndex) -> CfgBlockIndex>(
        self,
        return_block: CfgBlockIndex,
        mut resolve_target: F,
    ) -> Successor {
        match self {
            MirSuccessor::Return => Successor::Goto(return_block),
            MirSuccessor::Kill => Successor::Return,
            MirSuccessor::Goto(bbi) => Successor::Goto(resolve_target(bbi)),
            MirSuccessor::GotoSwitch(mut conditional_targets, default_bbi) => {
                Successor::GotoSwitch(
                    conditional_targets
                        .drain(..)
                        .map(|(guard, bbi)| (guard, resolve_target(bbi)))
                        .collect(),
                    resolve_target(default_bbi),
                )
            }
        }
    }
}
