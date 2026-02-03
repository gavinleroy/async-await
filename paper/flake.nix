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
      in
      {
        devShells.default =
          with pkgs;
          pkgs.mkShell {
            buildInputs = [
              skimpdf
              texEnv
              buildLuaScript
              buildScript
              watchScript
              python3
            ];
            # You'll need to set this if you want to use lualatex
            OSFONTDIR = "${texEnv}/share/texmf/fonts/";
            PYTHON = python3;
          };
      }
    );
}
