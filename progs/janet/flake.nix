{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils  }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system ; };
        netrepl-start = pkgs.writeShellScriptBin "netrepl-start" ''
          janet -e "(import spork/netrepl) (netrepl/server)"
        '';
      in {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [ 
            janet
            jpm
            netrepl-start
          ];
          #export JANET_PATH="$PWD/src:$PWD/lib:$PWD/vendor"
          shellHook = ''
            export JANET_TREE="$HOME/.local/share/janet"
            export JANET_PATH="$JANET_PATH:$JANET_TREE/lib"
          '';
        };
      });
}
