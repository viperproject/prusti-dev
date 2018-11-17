Steps to prepare the artifact for submission
============================================

1.  Install dependencies by using the script
    ``sudo bash install_dependencies.sh``.
2.  Install the new version of Z3 as /usr/bin/viper-z3.

    1.  Do not forget to chmod it.
    2.  Check if works with viper-z3 --help.

3.  Install the new version of Silicon.

    1.  rm -rf /usr/lib/viper/*
    2.  Move the silicon fat jar into /usr/lib/viper.
    3.  Test it by trying to verify an empty method.

4.  Compile Prusti::

        make release

5.  Copy the following files to VM::

	mkdir -p /usr/local/prusti/lib
	cp target/release/prusti-driver /usr/local/prusti/prusti-driver
    chmod 755 /usr/local/prusti/prusti-driver
	cp target/release/libprusti.so /usr/local/prusti/libprusti.so
	cp target/release/deps/libprusti_contracts-*.rlib /usr/local/prusti/libprusti_contracts.rlib
    ADD docker/prusti /usr/local/bin/prusti
    ADD docker/cargo-prusti /usr/local/bin/cargo-prusti
    chmod 755 /usr/local/bin/prusti
    chmod 755 /usr/local/bin/cargo-prusti

6.  Add to ~/.bashrc::

    export RUSTUP_HOME=/usr/local/rustup
    export CARGO_HOME=/usr/local/cargo
    export PATH=/usr/local/cargo/bin:$PATH

7.  Get examples on the VM.
