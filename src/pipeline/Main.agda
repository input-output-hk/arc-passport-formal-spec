------------------------------------------------------------------------
-- Midnight.Passport pipeline entry point
--
-- Emits the architecture diagram as Graphviz DOT on stdout. Render with:
--
--   agda --compile --ghc-flag=-O0 --ghc-flag=-o --ghc-flag=./passport-compiler \
--     pipeline/Main.agda
--   ./passport-compiler | dot -Tsvg > architecture.svg
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module pipeline.Main where

open import IO

open import Midnight.Passport.Semantics using (architectureˢ)
open import Midnight.Passport.Compiler using (compileDot)

main : Main
main = run (putStrLn (compileDot architectureˢ))
