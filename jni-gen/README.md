JNI-gen
=======

Generator of Rust bindings to Java classes.

The generated code uses the `jni` crate to interact with the JVM.

Requirements
------------

* `libjvm.so` needs to be in the `LD_LIBRARY_PATH` environment variable.
* The crate that makes use of `jni-gen` should have the `once_cell` dependency.
