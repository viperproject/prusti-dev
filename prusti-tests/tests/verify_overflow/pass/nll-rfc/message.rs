/// An adaptation of this example:
/// https://play.rust-lang.org/?version=nightly&mode=debug&edition=2018&gist=b8dfafd14113f2933c1b5127c861df44
///
/// which was created by Nicholas D. Matsakis to show-case NLL in his blog:
/// http://smallcultfollowing.com/babysteps/blog/2018/10/31/mir-based-borrowck-is-almost-here/
///
/// This example illustrates the differences between lexical borrow checker and the new non-lexical
/// borrow checker that is going to be part of Rust 2018 edition.
///
/// Changes:
///
/// +   Changed built-in types with mock types.
/// +   Rewrote loops into supported shape (while bool with no break, continue, or return).
///
/// Verified properties:
///
/// +   Absence of panics.

use prusti_contracts::*;

use std::sync::mpsc;

struct StringWrapper {
    //value: String,
}

impl StringWrapper {

    #[pure]
    #[trusted]
    fn equals(&self, other: &StringWrapper) -> bool {
        unimplemented!();
    }
}

enum Message {
    Letter { recipient: StringWrapper, data: StringWrapper },
}

struct Receiver {
    //receiver: mpsc::Receiver<Message>,
}

impl Receiver {

    #[trusted]
    pub fn recv(&mut self) -> MessageOption {
        unimplemented!();
        //MessageOption {
            //value: self.receiver.recv().ok(),
        //}
    }
}

struct Sender {
    //sender: mpsc::Sender<Message>,
}

impl Sender {
    #[trusted]
    pub fn send(&mut self, t: Message) {
        unimplemented!();
        //tx.send(message).unwrap();
    }
}

enum MessageOption {
    Some(Message),
    None,
}

impl MessageOption {

    #[pure]
    pub fn is_some(&self) -> bool {
        match self {
            MessageOption::Some(_) => true,
            MessageOption::None => false,
        }
    }

    #[requires(self.is_some())]
    pub fn take(self) -> Message {
        match self {
            MessageOption::Some(msg) => msg,
            MessageOption::None => {
                unreachable!();
            }
        }
    }

}

fn router(
    me: &mut StringWrapper,
    rx: Receiver,
    tx: Sender
) {
    let mut rx = rx;
    let mut tx = tx;
    let mut message_option = rx.recv();
    let mut is_some = message_option.is_some();
    while is_some {
        body_invariant!(message_option.is_some());
        let mut message = message_option.take();
        message_option = rx.recv();
        match &mut message {
            Message::Letter { recipient, data } => {
                if recipient.equals(me) {
                    tx.send(message);
                } else {
                    process(data);
                }
            }
        }
        is_some = message_option.is_some();
    }
}

fn process(_data: &mut StringWrapper) {}

fn main() { }
