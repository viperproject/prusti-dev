use crate::low::cfg::procedure::{Label, Successor};

impl Successor {
    /// The successor must contain exactly one `replaced_label`.
    pub fn replace_label(&mut self, replaced_label: &Label, replacing_label: Label) {
        match self {
            Successor::Return => {
                unreachable!()
            }
            Successor::Goto(label) => {
                assert_eq!(label, replaced_label);
                *label = replacing_label;
            }
            Successor::GotoSwitch(targets) => {
                let (_, label) = targets
                    .iter_mut()
                    .find(|(_, label)| label == replaced_label)
                    .unwrap();
                *label = replacing_label;
            }
        }
    }

    pub fn get_following(&self) -> Vec<&Label> {
        match self {
            Successor::Return => Vec::new(),
            Successor::Goto(target) => vec![target],
            Successor::GotoSwitch(targets) => {
                targets.iter().map(|(_test, target)| target).collect()
            }
        }
    }
}
