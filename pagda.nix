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
      version = "protocol-rewrite-f280e04f";
      src = pkgs.fetchFromGitHub {
        owner = "input-output-hk";
        repo = "categorical-crypto";
        rev = "f280e04f34a6d893fcf48b0f9b2845bc045122ea";
        hash = "sha256-lQY1j8vl4VTKpAS2rf0yp5JiY4KPvMMkfznK2xvl1dc=";
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
