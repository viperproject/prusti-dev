Steps to prepare the artifact for submission
============================================

1.  Install dependencies by using the script
    ``sudo bash install_dependencies.sh``.
2.  Install the new version of Z3 as /usr/bin/viper-z3.

    1.  Do not forget to chmod it.
    2.  Check if works with viper-z3 --help.

3.  Install the new version of Silicon.

    1.  rm -r /usr/lib/viper/*
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
    ADD bin/prusti /usr/local/bin/prusti
    ADD bin/cargo-prusti /usr/local/bin/cargo-prusti
    chmod 755 /usr/local/bin/prusti
    chmod 755 /usr/local/bin/cargo-prusti

6.  Add to ~/.bashrc::

    export RUSTUP_HOME=/usr/local/rustup
    export CARGO_HOME=/usr/local/cargo
    export PATH=/usr/local/cargo/bin:$PATH

7.  Get examples on the VM.
8.  Delete log and nll-facts folders.
8.  Create VM snapshot.
9.  Export VM into OVA.
9.  ZIP VM together with README.
10. Take sha256.
11. Upload to the server.
12. Upload README to the server.

6ee6948d786a8d54319bc1ef35af54ebe733e73dce40b1573ca21cdcefeeb505

12. Publish the link to VM as a software link.
13. Upload README as a supplementary material.
