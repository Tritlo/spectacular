


lists-build:
	cabal build --enable-profiling --profiling-detail=all-functions --reinstall && cabal exec -- ghc -fprof-auto -prof -O2 -threaded -rtsopts -o lus examples/Lists.hs -package spectacular-0.0.1

enable-prof:
	cabal configure --enable-profiling --profiling-detail=all-functions
disable-prof:
	cabal configure --disable-profiling

mini-lists-build:
	cabal build --enable-profiling --profiling-detail=all-functions --reinstall && cabal exec -- ghc -fprof-auto -prof -O2 -threaded -rtsopts -o minili examples/MiniList.hs -package spectacular-0.0.1

benchmark-build:
	cabal build --reinstall
	cabal exec -- ghc -O2 -threaded -rtsopts -o li examples/Lists.hs -package spectacular-0.0.1
	cabal exec -- ghc -O2 -threaded -rtsopts -o hli examples/HugeLists.hs -package spectacular-0.0.1
	cabal exec -- ghc -O2 -threaded -rtsopts -o oct examples/Octonions.hs -package spectacular-0.0.1
	cabal exec -- ghc -O2 -threaded -rtsopts -o rgx examples/Regex.hs -package spectacular-0.0.1
	cabal exec -- ghc -O2 -threaded -rtsopts -o lmon examples/ListMonad.hs -package spectacular-0.0.1
	echo "Done"

benchmark:
	gtime -v ./$(tgt) 2> $(tgt).bench | tee $(tgt).rules 

mini-prof: 
	/usr/bin/time -v ./minili +RTS -p -RTS 5 && profiteur minili.prof

run-prof: 
	/usr/bin/time -v ./lus +RTS -p -RTS 6 && profiteur lus.prof

big-prof: 
	/usr/bin/time -v ./lus +RTS -p -RTS 7 && profiteur lus.prof

big-par: 
	/usr/bin/time -v ./lus +RTS -N4 -RTS 6

huge-build:
	cabal build --enable-profiling --profiling-detail=all-functions --reinstall && cabal exec -- ghc -fprof-auto -prof -O2 -threaded -rtsopts -o hlus examples/HugeLists.hs -package spectacular-0.0.1

huge-prof-5: 
	/usr/bin/time -v ./hlus +RTS -p -RTS 5 && profiteur hlus.prof

huge-prof-6: 
	/usr/bin/time -v ./hlus +RTS -p -RTS 6 && profiteur hlus.prof

huge-prof-7: 
	/usr/bin/time -v ./hlus 7 +RTS -N4 -RTS && profiteur hlus.prof

huge-build-no-pro:
	cabal build --reinstall && cabal exec -- ghc -O2 -threaded -rtsopts -o hlus examples/HugeLists.hs -package spectacular-0.0.1

lists-build-no-pro:
	cabal build --reinstall && cabal exec -- ghc -O2 -threaded -rtsopts -o list-no-pro examples/Lists.hs -package spectacular-0.0.1

lists-no-pro7: 
	/usr/bin/time -v ./list-no-pro 7 +RTS -N1 -RTS

huge-no-pro7: 
	/usr/bin/time -v ./hlus 7 +RTS -N1 -RTS
