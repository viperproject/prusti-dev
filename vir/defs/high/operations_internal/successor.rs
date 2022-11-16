use super::super::cfg::procedure::{BasicBlockId, Successor};

impl Successor {
    pub fn get_following(&self) -> Vec<&BasicBlockId> {
        match self {
            Successor::Exit => Vec::new(),
            Successor::Goto(target) => vec![target],
            Successor::GotoSwitch(targets) => {
                targets.iter().map(|(_test, target)| target).collect()
            }
            Successor::NonDetChoice(first, second) => {
                vec![first, second]
            }
        }
    }

    pub fn map_basic_block_ids(&mut self, map: impl Fn(&mut BasicBlockId)) {
        match self {
            Successor::Exit => {}
            Successor::Goto(target) => map(target),
            Successor::GotoSwitch(targets) => {
                for (_, target) in targets {
                    map(target)
                }
            }
            Successor::NonDetChoice(first, second) => {
                map(first);
                map(second);
            }
        }
    }
}
