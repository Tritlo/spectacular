#/usr/bin/env bash
FORMAT="%C %E %M"


for bench in Lists Octonions Regex ListMonad HugeLists; do
    echo "Building $bench..."
    BRES=$(cabal build && cabal exec -- ghc benchmarks/$bench.hs -O3 -o $bench)
done

for p in {1..4}; do
    echo "Timing phase $p..."
    for bench in Lists Octonions Regex ListMonad; do
        RES=$(/usr/bin/time --output=timed --format="$FORMAT" ./$bench 7 $p | tail -n 1)
        TIMERES=$(cat timed)
        echo "$TIMERES $RES"
    done
    for s in 3 4; do
        RES=$(/usr/bin/time --output=timed --format="$FORMAT" ./HugeLists $s $p | tail -n 1)
        TIMERES=$(cat timed)
        echo "$TIMERES $RES"
    done
done

