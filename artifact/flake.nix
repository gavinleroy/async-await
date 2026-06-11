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

        # Template Cargo.toml files for generated Rust programs
        cargo-toml = pkgs.writeText "Cargo.toml" ''
          [package]
          name = "generated"
          version = "0.1.0"
          edition = "2021"

          [dependencies]
          tokio = { version = "=1.50.0", features = ["full"] }
          smol = "=2.0.2"
        '';
      in
      {
        packages.default = pkgs.writeShellApplication {
          name = "fuzz";
          runtimeInputs = [
            pkgs.racket
            python # 3.14 + trio 0.33
            pkgs.nodejs_22 # ES2025 support
            pkgs.nodePackages.typescript
            pkgs.dotnet-sdk_10 # C# 14 / .NET 10
            rust-toolchain # 1.92.0
          ];
          text = ''
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
            cp ${cargo-toml} $out/share/cargo-templates/Cargo.toml
          '';
        };

        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.racket
            python # 3.14 + trio 0.33
            pkgs.nodejs_22 # ES2025 support
            pkgs.nodePackages.typescript
            pkgs.dotnet-sdk_10 # C# 14 / .NET 10
            rust-toolchain # 1.92.0
          ];

          shellHook = ''
            echo "async-redex-models dev shell"
            echo "  racket:  $(racket --version)"
            echo "  python:  $(python3 --version)"
            echo "  node:    $(node --version)"
            echo "  dotnet:  $(dotnet --version)"
            echo "  rustc:   $(rustc --version)"
          '';
        };
      }
    );
}
