/// An adaptation of this example:
/// https://play.rust-lang.org/?version=nightly&mode=debug&edition=2018&gist=b8dfafd14113f2933c1b5127c861df44
///
/// which was created by Matsakis to show-case NLL in his blog:
/// http://smallcultfollowing.com/babysteps/blog/2018/10/31/mir-based-borrowck-is-almost-here/

use std::sync::mpsc::{Receiver, Sender};

enum Message {
    Letter { recipient: String, data: String },
}

fn router(me: &str, rx: Receiver<Message>, tx: Sender<Message>) {
    for message in rx {
        match &message {
            Message::Letter { recipient, data } => {
                if recipient != me {
                    tx.send(message).unwrap();
                } else {
                    process(data);
                }
            }
        }
    }
}

fn process(_data: &str) {}
