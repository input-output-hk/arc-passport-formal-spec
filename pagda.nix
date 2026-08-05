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
    entryModule = "Passport";
  };

  docsAssets."architecture.svg" = architectureSvg;
}
