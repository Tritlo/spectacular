


lists-build:
	cabal build --enable-profiling --profiling-detail=all-functions --reinstall && cabal exec -- ghc -fprof-auto -prof -O2 -threaded -rtsopts -o lus examples/Lists.hs -package synthspec-0.0.1

mini-lists-build:
	cabal build --enable-profiling --profiling-detail=all-functions --reinstall && cabal exec -- ghc -fprof-auto -prof -O2 -threaded -rtsopts -o minili examples/MiniList.hs -package synthspec-0.0.1

mini-prof: 
	/usr/bin/time -v ./minili +RTS -p -RTS 5 && profiteur minili.prof

run-prof: 
	/usr/bin/time -v ./lus +RTS -p -RTS 6 && profiteur lus.prof

big-prof: 
	/usr/bin/time -v ./lus +RTS -p -RTS 7 && profiteur lus.prof

big-par: 
	/usr/bin/time -v ./lus +RTS -N4 -RTS 6

huge-build:
	cabal build --enable-profiling --profiling-detail=all-functions --reinstall && cabal exec -- ghc -fprof-auto -prof -O2 -threaded -rtsopts -o hlus examples/HugeLists.hs -package synthspec-0.0.1

huge-prof-5: 
	/usr/bin/time -v ./hlus +RTS -p -RTS 5 && profiteur hlus.prof

huge-prof-6: 
	/usr/bin/time -v ./hlus +RTS -p -RTS 6 && profiteur hlus.prof

huge-prof-7: 
	/usr/bin/time -v ./hlus 7 +RTS -N4 -RTS && profiteur hlus.prof
