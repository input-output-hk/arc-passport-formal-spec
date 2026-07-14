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
  docs = pagda.docBackends.enhancedHtml {
    offline = false;
    modules = [ "Passport" "Midnight" ];
  };

  # Fold the rendered diagram and a landing page (the docs tree has no index of
  # its own) into the docs output.
  docsAssets = {
    "architecture.svg" = architectureSvg;
    "index.html" = ./docs-index.html;
  };
}
