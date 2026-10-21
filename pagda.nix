{ pkgs, pagda }:

let
  architectureSvg = pkgs.runCommand "architecture.svg"
    { nativeBuildInputs = [ pkgs.graphviz ]; } ''
    export HOME=$(mktemp -d)
    cp -r ${./.} work && chmod -R +w work && cd work
    ${pagda.agda}/bin/agda --compile --ghc-flag=-O0 \
      --ghc-flag=-o --ghc-flag=./passport-compiler src/pipeline/Main.agda
    ./passport-compiler | dot -Tsvg > "$out"
  '';
in
{
  overlay = final: prev: {
    standard-library-meta = prev.standard-library-meta.overrideAttrs (_: {
      version = "algebraic-solvers-97e2f65f";
      src = pkgs.fetchFromGitHub {
        owner = "agda";
        repo = "agda-stdlib-meta";
        rev = "97e2f65f5c8a1cc07aacec32b4974668ef32979b";
        hash = "sha256-jA65FwnhoIxahmJtkaCnoDvo+PvmejeO6JJPh4aPvJI=";
      };
    });

    categorical-crypto = prev.categorical-crypto.overrideAttrs (_: {
      version = "protocol-rewrite-437dca12";
      src = pkgs.fetchFromGitHub {
        owner = "input-output-hk";
        repo = "categorical-crypto";
        rev = "437dca12c85f096715fc06d9155146b3afc5f46e";
        hash = "sha256-iFPrkUnUaw+xw74CE559QcxCkzhmsWZ9JIWnqNCTIig=";
      };
    });
  };

  docs = pagda.docBackends.enhancedHtml {
    offline = false;
    modules = [ "Passport" "Midnight" ];
    entryModule = "Passport";
  };

  docsAssets."architecture.svg" = architectureSvg;
}
