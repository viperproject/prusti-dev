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

            copyLibs = true;
            copyLibsFilter = ''
              select(.reason == "compiler-artifact" and ((.target.kind | contains(["lib"])) and (.package_id | test("prusti-contracts"))) and .profile.test == false)
            '';

            override = _: {
              preBuild = ''
                export LD_LIBRARY_PATH="${pkgs.jdk11}/lib/openjdk/lib/server"
                export VIPER_HOME="${packages.viper}/backends"
                export Z3_EXE="${packages.viper}/z3/bin/z3"
                export ASM_JAR="${packages.ow2_asm}/asm.jar"
              '';
              postInstall = ''
                for f in $(find $out/bin/ $out/libexec/ -type f -executable); do
                  wrapProgram $f \
                    --set RUST_SYSROOT "${rust}" \
                    --set JAVA_HOME "${pkgs.jdk11}/lib/openjdk" \
                    --set LD_LIBRARY_PATH "${pkgs.jdk11}/lib/openjdk/lib/server" \
                    --set VIPER_HOME "${packages.viper}/backends" \
                    --set Z3_EXE "${packages.viper}/z3/bin/z3"
                done

                cp -r $out/lib/. $out/bin
                rm -rf $out/lib/
              '';
            };
          };

          viper = pkgs.fetchzip {
            name = "viper";
            url = "https://viper.ethz.ch/downloads/ViperToolsNightlyLinux.zip";
            stripRoot = false;
            hash = "sha256-oV9VgGmzNrLW6n08vXU2rlV6S9Eca3U0L+gNbVxKhEE=";
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

        defaultPackage = packages.prusti;
      }
    );
}
