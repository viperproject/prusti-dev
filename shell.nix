{}:

let
  rust-overlay = (import (builtins.fetchTarball "https://github.com/oxalica/rust-overlay/archive/master.tar.gz"));

  pkgs = import <nixpkgs> {
    # overlays = [ rust-overlay ];
  };
in
  with pkgs;

  mkShell {
    RUST_SRC_PATH = "${rustPlatform.rustLibSrc}";
    buildInputs = [
      openssl pkg-config
      # (pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain)
    ];
  }
