{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      rust-overlay,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ rust-overlay.overlays.default ];
        };

        rust-toolchain = pkgs.rust-bin.stable."1.92.0".default;

        python = pkgs.python314.withPackages (ps: [
          ps.trio # 0.33
        ]);

        rust-vendor = pkgs.rustPlatform.importCargoLock {
          lockFile = ./artifact/redex/fuzz/rust-template/Cargo.lock;
        };

        cargo-offline-config = pkgs.writeText "cargo-config.toml" ''
          [source.crates-io]
          replace-with = "vendored-sources"

          [source.vendored-sources]
          directory = "${rust-vendor}"

          [net]
          offline = true
        '';

        model = pkgs.stdenv.mkDerivation {
          pname = "models";
          version = "0.1.0";
          src = pkgs.lib.cleanSource ./artifact/redex;
          nativeBuildInputs = [ pkgs.racket ];

          buildPhase = ''
            export HOME=$(mktemp -d)
            # fuzz/main.rkt transitively requires every model; compiling it
            # compiles the world into compiled/*.zo for fast startup.
            raco make fuzz/main.rkt fuzz/figs.rkt
          '';

          # Module tests need the real runtimes
          # (Swift, Rust, etc) and spawn processes
          doCheck = false;

          installPhase = ''
            mkdir -p $out/lib/redex
            cp -r . $out/lib/redex
            chmod +x $out/lib/redex/fuzz/fuzz-parallel.sh
          '';
        };
        toolchains = [
          pkgs.racket
          python # 3.14 + trio 0.33
          pkgs.nodejs_22 # ES2025 support
          pkgs.typescript
          pkgs.dotnet-sdk_10 # C# 14 / .NET 10
          rust-toolchain # 1.92.0
          pkgs.gawk
        ];

        fuzz = pkgs.writeShellApplication {
          name = "fuzz";
          runtimeInputs = toolchains;
          runtimeEnv = {
            ASYNC_FUZZ_CARGO_CONFIG = cargo-offline-config;
          };
          text = ''
            # Swift is taken from the system toolchain (Xcode on macOS, the
            # base image's swift.org toolchain in the container), not nix.
            # The nix Apple SDK shadows it via DEVELOPER_DIR/SDKROOT; clear
            # those so swiftc resolves the system SDK.
            unset DEVELOPER_DIR SDKROOT
            export FUZZ_CACHE="''${FUZZ_CACHE:-$PWD/fuzz-cache}"
            exec bash ${model}/lib/redex/fuzz/fuzz-parallel.sh "$@"
          '';
        };

        figs = pkgs.writeShellApplication {
          name = "figs";
          runtimeInputs = toolchains;
          runtimeEnv = {
            ASYNC_FUZZ_CARGO_CONFIG = cargo-offline-config;
            FIGS_DIR = ./artifact/figs;
          };
          text = ''
            unset DEVELOPER_DIR SDKROOT
            exec racket ${model}/lib/redex/fuzz/figs.rkt "$@"
          '';
        };

        run-tests = pkgs.writeShellApplication {
          name = "run-tests";
          runtimeInputs = toolchains;
          runtimeEnv = {
            ASYNC_FUZZ_CARGO_CONFIG = cargo-offline-config;
          };
          text = ''
            unset DEVELOPER_DIR SDKROOT
            cd ${model}/lib/redex
            racket tests.rkt
            racket fuzz/witness-check.rkt
          '';
        };

        # Swift 6 is not in nixpkgs, so the official swift.org
        # image is the BASE and the nix closure toolchains,
        # precompiled models, the fuzz and run-tests commands,
        # the source tree at /artifact — is layered on top.
        # The nix store paths carry their own glibc, so they
        # coexist with the Ubuntu base untouched.
        swift-base = pkgs.dockerTools.pullImage {
          imageName = "swift";
          imageDigest = "sha256:f0bfe313779a0bb99db87f97c88ea6ada014aa6b3359f9c5583bf70b0b721217";
          finalImageName = "swift";
          finalImageTag = "6.0.3-jammy";
          os = "linux";
          arch = if pkgs.stdenv.hostPlatform.isAarch64 then "arm64" else "amd64";
          sha256 =
            if pkgs.stdenv.hostPlatform.isAarch64 then
              "sha256-/NxpyiDEuCDjw5Qkjd8987U1C/WFRLFVCNdKESF0A0o="
            else
              "sha256-PE0Cmk7DC5rbmbsPfg/WB5rJpS7blQDc8A1JRtNdPrk=";
        };

        artifact-src = pkgs.runCommand "artifact-src" { } ''
          mkdir -p $out/artifact
          cp -r ${pkgs.lib.cleanSource ./artifact}/. $out/artifact/
        '';

        image = pkgs.dockerTools.buildLayeredImage {
          name = "async-models-artifact";
          tag = "latest";
          fromImage = swift-base;
          # NOTHING nix-owned is merged into the filesystem root except
          # /artifact (a fresh directory): merging package roots shadows the
          # base's usrmerge symlinks (/lib -> usr/lib) in overlayfs, which
          # deletes the ELF interpreter every base binary hardcodes and
          # breaks swiftc. The nix programs reach PATH by store path instead,
          # so the base filesystem is byte-identical to swift:6.0.3-jammy.
          contents = [ artifact-src ];
          config = {
            Cmd = [
              "/bin/bash"
              "-l"
            ];
            WorkingDir = "/artifact";
            Env = [
              # nix store bin dirs (fuzz, run-tests, figs, toolchains, and a
              # cc for rustc — the base ships clang but no cc), then the
              # base image's own /usr/bin (swiftc lives there).
              "PATH=${
                pkgs.lib.makeBinPath (
                  [
                    fuzz
                    run-tests
                    figs
                    pkgs.stdenv.cc
                  ]
                  ++ toolchains
                )
              }:/usr/local/bin:/usr/bin:/bin"
              "ASYNC_FUZZ_CARGO_CONFIG=${cargo-offline-config}"
              # /artifact is nix-store-sourced (read-only permissions);
              # run outputs go under the writable HOME
              "FUZZ_CACHE=/root/fuzz-cache"
              "HOME=/root"
            ];
          };
        };

        linuxSystem = builtins.replaceStrings [ "darwin" ] [ "linux" ] system;
        image-runner = pkgs.writeShellApplication {
          name = "artifact-image";
          runtimeInputs = [
            pkgs.docker
          ]
          ++ pkgs.lib.optionals pkgs.stdenv.hostPlatform.isDarwin [ pkgs.colima ];
          text = ''
            tag=async-models-artifact:latest

            ${pkgs.lib.optionalString pkgs.stdenv.hostPlatform.isDarwin ''
              # macOS has no native containers: colima runs a Linux VM with
              # a docker daemon (first start downloads the VM image).
              if ! colima status >/dev/null 2>&1; then
                echo "starting colima..." >&2
                colima start
              fi
              export DOCKER_HOST="unix://$HOME/.colima/default/docker.sock"
            ''}

            if ! docker info >/dev/null 2>&1; then
              echo "error: no reachable docker daemon" >&2
              exit 1
            fi

            if tarball=$(nix build --no-link --print-out-paths \
                           "path:${self}#packages.${linuxSystem}.image" \
                           2>/dev/null); then
              docker load -i "$tarball"
            else
              echo "note: cannot nix-build the ${linuxSystem} image on this host" >&2
              echo "      (no Linux builder); building with docker instead" >&2
              docker build -t "$tag" -f ${self}/artifact/docker/Dockerfile ${self}
            fi
            exec docker run --rm -it "$tag"
          '';
        };

        #  -------------------------------------------------------------------
        # Paper

        texEnv = pkgs.texlive.combine {
          inherit (pkgs.texlive)
            scheme-medium
            latexmk
            collection-latexextra
            collection-fontsextra
            acmart
            libertine
            libertinus
            libertinus-fonts
            newtx
            inconsolata
            ;
        };

        buildLuaScript = pkgs.writeShellScriptBin "build-lua" ''
          mkdir -p build
          exec ${texEnv}/bin/latexmk -pdflua -view=none -outdir=build main.tex "$@"
        '';

        buildScript = pkgs.writeShellScriptBin "build" ''
          mkdir -p build
          exec ${texEnv}/bin/latexmk -pdf -view=none -outdir=build main.tex "$@"
        '';

        watchScript = pkgs.writeShellScriptBin "watch" ''
          mkdir -p build
          exec ${texEnv}/bin/latexmk -pvc -pdf -view=none -interaction=nonstopmode -outdir=build main.tex "$@"
        '';

        paper = pkgs.stdenv.mkDerivation {
          pname = "async-await-paper";
          version = "0.1.0";
          src = ./paper;
          nativeBuildInputs = [ texEnv ];
          buildPhase = ''
            export HOME=$TMPDIR
            latexmk -pdf -view=none -interaction=nonstopmode -outdir=build main.tex
          '';
          installPhase = ''
            mkdir -p $out
            cp build/main.pdf $out/main.pdf
          '';
        };
      in
      {
        packages = {
          default = paper;
          inherit
            paper
            fuzz
            model
            run-tests
            figs
            image-runner
            ;
        }
        // pkgs.lib.optionalAttrs pkgs.stdenv.hostPlatform.isLinux {
          inherit image;
        };

        apps.image = {
          type = "app";
          program = "${image-runner}/bin/artifact-image";
        };

        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.racket
            python # 3.14 + trio 0.33
            pkgs.nodejs_22 # ES2025 support
            pkgs.typescript
            pkgs.dotnet-sdk_10 # C# 14 / .NET 10
            rust-toolchain # 1.92.0
          ];

          # Generated Rust programs build offline against the vendored crates.
          ASYNC_FUZZ_CARGO_CONFIG = cargo-offline-config;

          shellHook = ''
            # Swift comes from the system toolchain (Xcode), not nix — we do
            # not pin a swift toolchain here. The nix Apple SDK shadows the
            # system one via DEVELOPER_DIR/SDKROOT, so clear them and let
            # swiftc fall back to the system Xcode (xcode-select default).
            unset DEVELOPER_DIR SDKROOT

            echo "async-redex-models dev shell"
            echo "  racket:  $(racket --version)"
            echo "  python:  $(python3 --version)"
            echo "  node:    $(node --version)"
            echo "  dotnet:  $(dotnet --version)"
            echo "  rustc:   $(rustc --version)"
            echo "  swift:   $(swiftc --version 2>/dev/null | head -1 || echo '(system swiftc unavailable)')"
          '';
        };

        devShells.paper = pkgs.mkShell {
          buildInputs = [
            pkgs.skimpdf
            texEnv
            buildLuaScript
            buildScript
            watchScript
            pkgs.python3
          ];
          # Needed for lualatex font resolution.
          OSFONTDIR = "${texEnv}/share/texmf/fonts/";
          PYTHON = pkgs.python3;
        };
      }
    );
}
