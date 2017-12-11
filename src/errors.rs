use jni;
use std;

// Create the Error, ErrorKind, ResultExt, and Result types
error_chain!{
    foreign_links {
        Io(std::io::Error);
        Utf8Error(std::str::Utf8Error);
        // FIXME: why is this required?
        UnknownJniError(jni::Error);
    }

    links {
        JniErrors(jni::errors::Error, jni::errors::ErrorKind);
    }
}
