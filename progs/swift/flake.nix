{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils  }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system ; };
      in {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            # NOTE, the version in NixPkgs is 5.10. We need at lest Swift 6
            # Watch the issue here: https://github.com/NixOS/nixpkgs/issues/343210
            swift
            swiftpm
            sourcekit-lsp
            swiftPackages.Foundation
          ];
        };
      });
}
