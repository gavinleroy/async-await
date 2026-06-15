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
      in
      {
        packages.default = pkgs.writeShellApplication {
          name = "fuzz";
          runtimeInputs = [
            pkgs.racket
            python # 3.14 + trio 0.33
            pkgs.nodejs_22 # ES2025 support
            pkgs.typescript
            pkgs.dotnet-sdk_10 # C# 14 / .NET 10
            rust-toolchain # 1.92.0
          ];
          runtimeEnv = {
            ASYNC_FUZZ_CARGO_CONFIG = cargo-offline-config;
          };
          text = ''
            # Swift is taken from the system toolchain (Xcode), not nix. The
            # nix Apple SDK shadows it via DEVELOPER_DIR/SDKROOT; clear those
            # so swiftc resolves the system Xcode SDK (xcode-select default).
            unset DEVELOPER_DIR SDKROOT
            racket ${./redex/fuzz/main.rkt} "$@"
          '';
        };

        packages.model = pkgs.stdenv.mkDerivation {
          pname = "models";
          version = "0.1.0";
          src = pkgs.lib.cleanSourceWith ./redex;
          nativeBuildInputs = [ pkgs.racket ];

          buildPhase = ''
            export HOME=$(mktemp -d)
            raco make .
          '';

          doCheck = true;
          checkPhase = ''
            export HOME=$(mktemp -d)
            raco test .
          '';

          installPhase = ''
            mkdir -p $out/lib/redex
            cp *.rkt $out/lib/redex/

            mkdir -p $out/share/cargo-templates
            cp fuzz/rust-template/Cargo.toml fuzz/rust-template/Cargo.lock \
              $out/share/cargo-templates/
          '';
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
