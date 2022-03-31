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
}
