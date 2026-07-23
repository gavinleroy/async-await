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

        # --- Pinned versions (from paper) ---

        rust-toolchain = pkgs.rust-bin.stable."1.92.0".default;

        python = pkgs.python314.withPackages (ps: [
          ps.trio # 0.33
        ]);

        # --- Vendored Rust dependencies (tokio + smol) ---
        #
        # The lockfile lives with the template manifest in
        # redex/fuzz/rust-template; regenerate it there with
        # `cargo generate-lockfile` after changing pinned versions.
        # Generated programs build with `cargo --offline` against this
        # vendor directory (see ASYNC_FUZZ_CARGO_CONFIG in fuzz/run.rkt).
        rust-vendor = pkgs.rustPlatform.importCargoLock {
          lockFile = ./redex/fuzz/rust-template/Cargo.lock;
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
          src = pkgs.lib.cleanSource ./redex;
          nativeBuildInputs = [ pkgs.racket ];

          buildPhase = ''
            export HOME=$(mktemp -d)
            # fuzz/main.rkt transitively requires every model; compiling it
            # compiles the world into compiled/*.zo for fast startup.
            raco make fuzz/main.rkt fuzz/figs.rkt
          '';

          # Module tests need the real runtimes (python/node/cargo/swiftc/
          # dotnet) and spawn processes; they run in the dev shell, not the
          # nix sandbox.
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

        # `nix run .#fuzz` (also the default): the full fuzz endpoint — all
        # lanes in parallel against the precompiled models, one cache
        # directory per run (default ./fuzz-cache), live status on the
        # terminal. See redex/fuzz/fuzz-parallel.sh for flags.
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

        # `nix run .#figs`: run every paper-figure program (figs/<n>/<lane>)
        # through the same harness the fuzzer uses for generated programs,
        # printing one markdown table per figure. Args pass through
        # (`-r N`, or an alternate figs directory).
        figs = pkgs.writeShellApplication {
          name = "figs";
          runtimeInputs = toolchains;
          runtimeEnv = {
            ASYNC_FUZZ_CARGO_CONFIG = cargo-offline-config;
            # default figure-program directory; a positional argument overrides
            FIGS_DIR = ./figs;
          };
          text = ''
            unset DEVELOPER_DIR SDKROOT
            exec racket ${model}/lib/redex/fuzz/figs.rkt "$@"
          '';
        };

        # `nix run .#run-tests`: every model's hand-written test suite (each
        # async test also compiles and runs the REAL program), followed by
        # the witness-search differential gate.
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

        # --- Docker image, built by nix (linux only: the image closure is
        # linux ELF). Swift 6 is not in nixpkgs, so the official swift.org
        # image is the BASE (pinned by digest, per-arch content hash) and
        # the nix closure — toolchains, precompiled models, the fuzz and
        # run-tests commands, the source tree at /artifact — is layered on
        # top. The nix store paths carry their own glibc, so they coexist
        # with the Ubuntu base untouched.
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
          cp -r ${pkgs.lib.cleanSource ./.}/. $out/artifact/
        '';

        image = pkgs.dockerTools.buildLayeredImage {
          name = "async-models-artifact";
          tag = "latest";
          fromImage = swift-base;
          contents =
            toolchains
            ++ [
              fuzz
              run-tests
              figs
              model
              artifact-src
              pkgs.bashInteractive
              pkgs.coreutils
              pkgs.gnugrep
              pkgs.gnused
              pkgs.findutils
              pkgs.which
              pkgs.procps
              # rustc needs a C linker (`cc`); the swift base ships clang
              # for Swift but no cc
              pkgs.stdenv.cc
            ];
          config = {
            Cmd = [
              "/bin/bash"
              "-l"
            ];
            WorkingDir = "/artifact";
            Env = [
              # /bin: the nix closure (fuzz, run-tests, racket, dotnet, …);
              # /usr/bin: the base image's swift toolchain.
              "PATH=/bin:/usr/bin:/usr/local/bin"
              "ASYNC_FUZZ_CARGO_CONFIG=${cargo-offline-config}"
              # /artifact is nix-store-sourced (read-only permissions);
              # run outputs go under the writable HOME
              "FUZZ_CACHE=/root/fuzz-cache"
              "HOME=/root"
            ];
          };
        };

        # `nix run .#image` ≡ (1) obtain the docker image for THIS
        # machine's architecture, (2) run it in docker — with the container
        # runtime itself supplied by nix, so a user with only Nix needs
        # nothing else: the docker CLI comes from nixpkgs, and on macOS
        # colima provides the Linux VM + docker daemon. (The primary
        # distribution channel is CI-built per-arch images pushed to a
        # registry; this is the self-contained fallback.)
        #
        # The image is resolved at RUNTIME, never interpolated — that would
        # make the Linux image a build dependency of the runner, which a
        # darwin host cannot satisfy: first try the nix-built image for the
        # matching linux system (native on Linux; macOS with a Linux
        # builder), else `docker build` with docker/Dockerfile (Docker runs
        # Linux internally everywhere, targeting the host arch).
        linuxSystem = builtins.replaceStrings [ "darwin" ] [ "linux" ] system;
        image-runner = pkgs.writeShellApplication {
          name = "artifact-image";
          runtimeInputs =
            [ pkgs.docker ]
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
              docker build -t "$tag" -f ${self}/docker/Dockerfile ${self}
            fi
            exec docker run --rm -it "$tag"
          '';
        };
      in
      {
        packages =
          {
            default = fuzz;
            inherit
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
      }
    );
}
