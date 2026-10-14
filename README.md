# Spectacular

[![DOI](https://zenodo.org/badge/471054656.svg)](https://zenodo.org/badge/latestdoi/471054656)

Welcome to the Spectacular project, a re-envisioning of [QuickSpec](https://hackage.haskell.org/package/quickspec) using ECTAs.

Spectacular uses the ECTAs of [cfta](https://github.com/Tritlo/microecta/tree/microcfta/cfta) and builds with GHC 9.14.1.
For Spectacular itself, check out the [spectacular/](/tree/spectacular/spectacular) subdirectory!
To see it in action, run `cabal build` in this directory, and then run `./benchmark.sh` in `spectacular/`.

The environment variable `SPECTACULAR_TESTS` sets the number of test cases (1000 by default, as in QuickSpec).
Fewer test cases are faster, but they let more false laws through, and the prover builds on each law that it prints.
With 100 test cases, `bench-huge-lists 7 1` prints false laws, and the rules that follow from them hide true laws such as `xs == take x xs ++ drop x xs`.

