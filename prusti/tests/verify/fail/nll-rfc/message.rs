/// An adaptation of this example:
/// https://play.rust-lang.org/?version=nightly&mode=debug&edition=2018&gist=b8dfafd14113f2933c1b5127c861df44
///
/// which was created by Matsakis to show-case NLL in his blog:
/// http://smallcultfollowing.com/babysteps/blog/2018/10/31/mir-based-borrowck-is-almost-here/
///
/// This example illustrates the differences between the lexical borrow
/// checker from Rust 2015 edition and the new non-lexical borrow
/// checker that was shipped as part of the Rust 2018 edition.
///
/// Changes:
///
/// +   Changed built-in types with mock types.
/// +   Rewrote loops into supported shape (while bool with no break, continue, or return).
///
/// Verified properties:
///
/// +   Absence of panics.

extern crate prusti_contracts;

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

enum Result<T> {
    Ok(T),
    Err,
}

impl<T> Result<T> {
    #[pure]
    fn is_ok(&self) -> bool {
        match self {
            Result::Ok(_) => true,
            Result::Err => false,
        }
    }
    #[requires="self.is_ok()"]
    fn unwrap(self) -> T {
        match self {
            Result::Ok(v) => v,
            Result::Err => unreachable!(),
        }
    }
}

impl Sender {
    #[trusted]
    pub fn send(&mut self, t: Message) -> Result<()> {
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

    #[requires="self.is_some()"]
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
    #[invariant="is_some ==> message_option.is_some()"]
    while is_some {
        let mut message = message_option.take();
        match &message {
            Message::Letter { recipient, data } => {
                if recipient.equals(me) {
                    // The program does not handle the case in which `send()` fails, so the
                    // `unwrap()` might panic.
                    tx.send(message)
                        .unwrap(); //~ ERROR precondition might not hold.
                } else {
                    process(data);
                }
            }
        }
        message_option = rx.recv();
        is_some = message_option.is_some();
    }
}

fn process(_data: &StringWrapper) {}

fn main() { }
