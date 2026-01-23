{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        texEnv = pkgs.texlive.combine {
          inherit (pkgs.texlive)
            scheme-medium
            latexmk
            collection-latexextra
            acmart
            libertine
            libertinus
            newtx
            inconsolata
            ;
        };

        buildScript = pkgs.writeShellScriptBin "build" ''
          mkdir -p build
          exec ${texEnv}/bin/latexmk -view=non -outdir=build main.tex "$@"
        '';

        watchScript = pkgs.writeShellScriptBin "watch" ''
          mkdir -p build
          exec ${texEnv}/bin/latexmk -pvc -pdf -view=none -interaction=nonstopmode -outdir=build main.tex "$@"
        '';
      in
      {
        devShells.default =
          with pkgs;
          pkgs.mkShell {
            buildInputs = [
              skimpdf
              texEnv
              buildScript
              watchScript
              python3
            ];
            # You'll need to set this if you want to use lualatex
            #OSFONTDIR = "${texEnv}/share/texmf/fonts/opentype/public;${texEnv}/share/texmf/fonts/truetype/public";
            PYTHON = python3;
          };
      }
    );
}
