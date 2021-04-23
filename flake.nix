{
  description = "A static verifier for Rust, based on the Viper verification infrastructure.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    naersk.url = "github:nmattia/naersk";
    rust-overlay.url = "github:oxalica/rust-overlay";
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, naersk, rust-overlay, utils }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ rust-overlay.overlay ];
        };

        rust = pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain;

        naersk-lib = naersk.lib."${system}".override {
          cargo = rust;
          rustc = rust;
        };

        prusti-version = "${self.tag or "${self.lastModifiedDate}.${self.shortRev or "dirty"}"}";
      in rec {
        packages = {
          prusti = naersk-lib.buildPackage {
            name = "prusti";
            version = "${prusti-version}";
            root = ./.;
            buildInputs = [
              pkgs.pkg-config
              pkgs.wget
              pkgs.gcc
              pkgs.openssl
              pkgs.jdk11
              packages.viper
              packages.ow2_asm
            ];
            nativeBuildInputs = [
              pkgs.makeWrapper
            ];

            copyTarget = true;
            compressTarget = false;

            override = _: {
              preBuild = ''
                export LD_LIBRARY_PATH="${pkgs.jdk11}/lib/openjdk/lib/server"
                export VIPER_HOME="${packages.viper}/backends"
                export Z3_EXE="${packages.viper}/z3/bin/z3"
                export ASM_JAR="${packages.ow2_asm}/asm.jar"
              '';
            };
            overrideMain = _: {
              postInstall = ''
                rm $out/bin/test-crates

                for f in $(find $out/bin/ $out/libexec/ -type f -executable); do
                  wrapProgram $f \
                    --set RUST_SYSROOT "${rust}" \
                    --set JAVA_HOME "${pkgs.jdk11}/lib/openjdk" \
                    --set LD_LIBRARY_PATH "${pkgs.jdk11}/lib/openjdk/lib/server" \
                    --set VIPER_HOME "${packages.viper}/backends" \
                    --set Z3_EXE "${packages.viper}/z3/bin/z3"
                done

                mkdir $out/bin/deps
                cp $out/target/release/libprusti_contracts.rlib $out/bin
                cp $out/target/release/deps/libprusti_contracts_internal-* $out/bin/deps
                rm -rf $out/target
                rm $out/bin/deps/*.{rlib,rmeta}
              '';
            };
          };

          viper = pkgs.fetchzip {
            name = "viper";
            url = "https://viper.ethz.ch/downloads/ViperToolsNightlyLinux.zip";
            stripRoot = false;
            hash = "sha256-82vnyO7QWaLzehnBzPJxuEmdqK0MnWWwQnmdLq28sQc=";
          };

          ow2_asm = pkgs.stdenv.mkDerivation rec {
            name = "asm";
            version = "3.3.1";
            src = pkgs.fetchurl {
              url = "https://repo.maven.apache.org/maven2/${name}/${name}/${version}/${name}-${version}.jar";
              hash = "sha256-wrOSdfjpUbx0dQCAoSZs2rw5OZvF4T1kK/LTRkSd9/M=";
            };
            dontUnpack = true;
            dontBuild = true;
            installPhase = ''
              mkdir $out
              cp ${src} $out/asm.jar
            '';
          };
        };

        checks = {
          # prusti-test = naersk-lib.buildPackage {
          #   name = "prusti-test";
          #   version = "${prusti-version}";
          #   root = ./.;
          #   checkInputs = [
          #     pkgs.pkg-config
          #     pkgs.wget
          #     pkgs.gcc
          #     pkgs.openssl
          #     pkgs.jdk11
          #     packages.viper
          #     packages.ow2_asm
          #   ];

          #   doCheck = true;

          #   override = _: {
          #     preBuild = ''
          #       export LD_LIBRARY_PATH="${pkgs.jdk11}/lib/openjdk/lib/server"
          #       export VIPER_HOME="${packages.viper}/backends"
          #       export Z3_EXE="${packages.viper}/z3/bin/z3"
          #       export ASM_JAR="${packages.ow2_asm}/asm.jar"
          #     '';
          #     preCheck = ''
          #       export RUST_SYSROOT="${rust}"
          #       export JAVA_HOME="${pkgs.jdk11}/lib/openjdk"
          #       export LD_LIBRARY_PATH="${pkgs.jdk11}/lib/openjdk/lib/server"
          #       export VIPER_HOME="${packages.viper}/backends"
          #       export Z3_EXE="${packages.viper}/z3/bin/z3"
          #     '';
          #   };
          # };

          prusti-simple-test = pkgs.runCommand "prusti-simple-test" {
            buildInputs = [
              defaultPackage
              rust
            ];
          }
          ''
            cargo new --name example $out/example
            sed -i '1s/^/use prusti_contracts::*;\n/;s/println.*$/assert!(true);/' $out/example/src/main.rs
            cargo-prusti --manifest-path=$out/example/Cargo.toml
          '';
        };

        defaultPackage = packages.prusti;
      }
    );
}
