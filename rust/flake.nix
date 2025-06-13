{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay.url = "github:oxalica/rust-overlay";
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    flake-utils.lib.eachDefaultSystem (system:
      let 
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs { 
          inherit system overlays; 
        }; 
      in {
        devShell = with pkgs; mkShell {
          nativeBuildInputs = [
            rust-bin.stable.latest.default
            rust-analyzer
          ];
        };
      });
}
