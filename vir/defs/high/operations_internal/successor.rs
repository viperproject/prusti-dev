use super::super::cfg::procedure::{BasicBlockId, Successor};

impl Successor {
    pub fn get_following(&self) -> Vec<&BasicBlockId> {
        match self {
            Successor::Return => Vec::new(),
            Successor::Goto(target) => vec![target],
            Successor::GotoSwitch(targets) => {
                targets.iter().map(|(_test, target)| target).collect()
            }
        }
    }
}
