#!/usr/bin/env bash
# The fuzz endpoint: run all (or selected) lanes in parallel, one process per
# language, with a per-run cache directory and live multiplexed status.
#
#   fuzz-parallel.sh [options]
#     -s SEED     RNG seed            (default: random, printed; program i is
#                 a pure function of (seed, lang, i), so pass the printed
#                 seed back with -s to reproduce a run exactly)
#     -n N        programs per lane   (default: 50)
#     -r R        runtime runs        (default: 20)
#     -l LANGS    space-separated lanes (default: all seven)
#     -o DIR      cache root          (default: $FUZZ_CACHE or ./fuzz-cache)
#
# Every run gets fuzz-cache/<UTC-stamp>-seed<S>/ containing meta.json, one
# <lang>.log + <lang>.jsonl + <lang>-summary.json per lane, and summary.json.
# Lanes are independent (per-language RNG seeding); never run two lanes of
# the SAME language concurrently (shared per-language cargo target dir).
set -u

SEED=$((RANDOM * 32768 + RANDOM))
N=50; R=20
LANGS="asyncio javascript trio smol tokio csharp swift"
ROOT="${FUZZ_CACHE:-fuzz-cache}"
while getopts "s:n:r:l:o:" opt; do
  case $opt in
    s) SEED=$OPTARG ;;
    n) N=$OPTARG ;;
    r) R=$OPTARG ;;
    l) LANGS=$OPTARG ;;
    o) ROOT=$OPTARG ;;
    *) exit 2 ;;
  esac
done

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RUN="$ROOT/$(date -u +%Y%m%dT%H%M%SZ)-seed$SEED"
mkdir -p "$RUN"

printf '{"seed":%s,"count":%s,"runtime_runs":%s,"langs":"%s","started":"%s"}\n' \
  "$SEED" "$N" "$R" "$LANGS" "$(date -u +%FT%TZ)" > "$RUN/meta.json"

echo "fuzz: generating $N programs x $R runs per lane (seed $SEED)"
echo "fuzz: lanes: $LANGS"
echo "fuzz: cache dir $RUN  (details per lane: <lang>.log, records: <lang>.jsonl)"
echo

# Lanes write ONLY to their log files; stdout belongs to the progress bars.
pids=()
for lang in $LANGS; do
  racket "$DIR/main.rkt" -l "$lang" -n "$N" -r "$R" --seed "$SEED" --out "$RUN" \
    > "$RUN/$lang.log" 2>&1 &
  pids+=($!)
done

# shellcheck disable=SC2086
python3 "$DIR/progress.py" "$RUN" "$N" $LANGS &
prog=$!

for p in "${pids[@]}"; do
  wait "$p" || true
done
touch "$RUN/.lanes-done"

wait "$prog"
status=$?
echo "fuzz: results in $RUN"
exit $status
