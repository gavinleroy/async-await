# Artifact: Executable Redex Models of Async/Await Runtimes

This artifact contains executable PLT Redex semantics for the async/await
implementations of **seven real runtimes** — Python `asyncio`, Python `trio`,
JavaScript (node), C# (.NET), Swift, Rust `tokio`, and Rust `smol` — together
with a **differential fuzzer** that tests each model against its real runtime:
for every generated program, every output the real runtime produces must be a
member of the model's output set.

## The intended workflow

The artifact is meant to be walked through in this order — each step builds
trust that the next step's results mean something:

1. **Enter the environment.** Either load the container (`nix run .#image`,
   or `docker build` from `docker/Dockerfile` on hosts that cannot build a
   Linux nix closure) or use `nix develop` natively. Everything below runs
   identically in both; the container just fixes the Swift toolchain and
   pre-warms caches.

2. **Establish that the models and the pipeline work: `run-tests`**
   (~10 min). This runs every hand-written semantics test — 182 across the
   base language and the seven runtime models — and each async test does
   double duty: it checks the Redex model's output *and* compiles and runs
   the same program on the real runtime, checking that too. It ends with the
   witness-search differential gate (the fuzzer's membership oracle checked
   against an exhaustive enumerator). Green here means: the semantics load,
   every toolchain works, and the fuzzer's oracle is trustworthy.

3. **Kick the fuzzer's tires: `fuzz -n 2`** (~2–3 min). Two generated
   programs per lane, end to end: type-directed generation, compilation to
   real Python/JS/C#/Swift/Rust, 20 executions each, and a witness search
   for every observed output. You see one progress bar per lane and a final
   verdict table; a cache directory with per-program JSONL records appears
   under `$FUZZ_CACHE`.

4. **Run the real experiment: `fuzz`** (50 programs/lane, ~10–15 min on 8+
   cores). This is the artifact's central claim in executable form: *for
   every generated program, every output the real runtime exhibits is in
   the model's output set.* The expected result is the one in
   FUZZ-RESULTS.md — zero mismatches, zero crashes, zero unconfirmed. The
   run prints its random seed; `fuzz -s <seed>` re-generates the exact same
   programs, so any finding is reproducible in isolation
   (`fuzz -s <seed> -l tokio`).

5. **Interpret and drill in.** A `MISMATCH` is a *proof* (exhaustion of the
   pruned state space) that the model cannot produce something the runtime
   did — the exit code turns nonzero, and the offending program + outputs
   are in the lane log and JSONL. An `unconfirmed` is honestly weaker:
   the search budget ran out (see FUZZ.md for the escalation tiers that
   make this rare). Per-program records in `fuzz-cache/<run>/<lane>.jsonl`
   carry the generated term, every observed output with its run count and
   verdict, and timings — enough to replay any single case.

6. **Read the semantics.** The models are the contribution; the fuzzer is
   the evidence. Each `redex/<runtime>.rkt` states its design points as
   comments on the rules that implement them (dispatch discipline,
   cancellation, entry/exit), including the runtime probes that justify
   them. DIFF.md tracks every rule change against the paper baseline;
   FUZZ.md is the pipeline's engineering log, including every semantics bug
   the fuzzer caught.

For authors/maintainers the loop is the same with an edit step in front:
change a rule in `redex/<runtime>.rkt` → `raco test redex/<runtime>.rkt`
(that model's suite, model + real runtime) → `racket
redex/fuzz/witness-check.rkt` if the search infrastructure changed → a
`fuzz` run to look for regressions on fresh programs — and FUZZ.md gets a
findings entry when semantics change.

## Getting started

### Docker image, built by Nix (recommended for evaluation)

```sh
nix build .#image      # → result: a docker-loadable image tarball
nix run  .#image       # loads the image into docker and opens a shell inside
```

The image is assembled by Nix (`dockerTools.buildLayeredImage`): the base is
the official swift.org **Swift 6.0.3** image (Swift is not in nixpkgs), pinned
by digest, and the Nix-built closure — every other toolchain, the precompiled
models, the exposed commands, and the source tree — is layered on top. Inside
the container (working directory `/artifact`, the full source):

```sh
fuzz                   # the fuzz endpoint (same flags as `nix run .#fuzz`)
fuzz -n 2              # quick 2-programs-per-lane run
run-tests              # all 182 model tests + the witness-search gate
racket …               # racket, python3, node, dotnet, rustc, swiftc all on PATH
```

There is no Nix inside the container — everything is already on `PATH`.
`nix run .#image` is fully self-contained on Linux and macOS, x86 and ARM:
the docker CLI comes from nixpkgs, on macOS colima (also from nixpkgs)
provides the Linux VM + docker daemon — a user with only Nix needs nothing
else. The image for the host's architecture is resolved at runtime: the
nix-built image where the host can build Linux closures (any Linux host;
macOS with a Linux builder), otherwise an automatic `docker build` from
`docker/Dockerfile` inside the nix-provided runtime. The primary
distribution channel is CI-built images: `packages.x86_64-linux.image`
and `packages.aarch64-linux.image` are the two artifacts to build in CI
and push to a registry as one multi-arch manifest.

### Native (macOS/Linux with Nix)

```sh
nix develop            # dev shell; swiftc comes from the system toolchain (Xcode on macOS)
nix run .#fuzz         # the full fuzz endpoint
nix run .#run-tests    # all model test suites + the witness-search gate
```

Rust crate dependencies are vendored by the flake — generated programs build
offline everywhere.

## Kick the tires (~10 minutes)

```sh
# 1. All hand-written semantics tests (182 tests across the base language +
#    7 runtime models; each async test also compiles and runs the REAL
#    program and checks it against the model):
nix develop -c racket redex/tests.rkt
#    (equivalently: nix develop -c raco test redex/<model>.rkt per model)

# 2. The witness search's differential gate (search vs. exhaustive
#    reference enumerator):
nix develop -c racket redex/fuzz/witness-check.rkt

# 3. A small fuzz run (2 programs per lane):
nix run .#fuzz -- -n 2
```

## Full evaluation

```sh
nix run .#fuzz                      # 50 programs/lane, random seed (printed)
nix run .#fuzz -- -s <seed>         # reproduce a specific run
```

Program `i` of a lane is a pure function of `(seed, lang, i)`, so passing a
printed seed back reproduces the exact program set. Each run writes a cache
directory `fuzz-cache/<stamp>-seed<S>/` with per-lane JSONL records (program
term, per-output run counts, per-output verdicts, timings) and logs. The live
display shows one progress bar per lane; the exit code is nonzero on any
confirmed mismatch or crash.

Interpretation of per-output verdicts:

- `producible` — a concrete model execution reaching that output was found.
- `unreachable` — exhaustion proof: the model **cannot** produce the runtime's
  output. This is a confirmed semantics mismatch, the property under test.
- `inconclusive` — search budget ran out (reported as `unconfirmed`, not a
  failure; see FUZZ.md for the escalation tiers that make this rare).

Reference results: **[FUZZ-RESULTS.md](FUZZ-RESULTS.md)** records the latest
full runs — currently 210/210 and 350/350 programs with **zero mismatches,
zero unconfirmed, zero crashes** — with per-lane wall-clock and search-time
statistics. Expect roughly 10–15 minutes for a full 50-program run on 8–12
cores (the tokio lane dominates; its work-stealing scheduler gives the model
the largest search space).

## Repository map

```
flake.nix                  pinned toolchains, vendored Rust deps, the fuzz app
redex/
  core.rkt                 store/metafunction helpers shared by every language
  lc.rkt                   base call-by-value λ-calculus: state, mutation,
                           delimited continuations (reset/shift), structs, lists
  exn.rkt                  exceptions layered on the base language (throw/catch)
  platform.rkt             THE SHARED RUNTIME PLATFORM: a macro that builds an
                           event-system language over a base language — machine
                           state (t σ Q T P) = clock, store, ready queue, timer
                           queue, OS threads; tasks; scheduler + timer rules;
                           the big-step wrapper; per-model extension points
  py.rkt / rust.rkt        surface async languages (async/lambda, await) that
                           the Python- and Rust-family models extend
  aio.rkt                  asyncio model   (single-threaded loop, one-shot cancel)
  trio.rkt                 trio model      (structured concurrency, nurseries,
                                            checkpoint cancellation, shuffled dispatch)
  javascript.rkt           JS model        (microtask/macrotask event loop)
  csharp.rkt               C# model        (eager tasks, thread pool)
  swift.rkt                Swift model     (eager tasks, flag-only cooperative cancel)
  tokio.rkt                tokio model     (work stealing, inline block_on,
                                            JoinHandle→Result, abort, racy shutdown tail)
  smol.rkt                 smol model      (single executor thread ∥ inline block_on)
  typecheck.rkt            the type system shared by the generator and backends
  tests.rkt                driver that runs every module's test suite
  fuzz/
    typegen.rkt            type-directed program generator (well-typed by
                           construction; per-program deterministic seeding)
    compile-py/js/cs/swift/rs.rkt
                           type-directed backends emitting real Python/JS/C#/
                           Swift/Rust from generated programs
    run.rkt                compiling + executing real programs (offline cargo,
                           dotnet, swiftc, node, python)
    main.rkt               the fuzzer: runtime batches, membership verdicts,
                           three-tier parallel search dispatch
    model.rkt              machine-state wrapping, canonical state dedup,
                           terminal-output observation
    witness.rkt            the multi-target witness search (membership oracle)
    witness-place.rkt      place (OS-thread) worker running whole searches
    reference.rkt          exhaustive output-set enumerator (ground truth)
    witness-check.rkt      differential gate: search vs. reference
    fuzz-parallel.sh       the endpoint driver (`nix run .#fuzz`)
    rust-template/         pinned Cargo manifest + lockfile for vendoring
```

Each model file states its design points in comments (dispatch discipline,
cancellation semantics, entry/exit behavior) with the runtime probes that
justify them.

## Documentation

- **FUZZ.md** — the pipeline in depth: generator design, witness search
  (pruning, walk biases, escalation tiers, soundness arguments), timer/clock
  semantics, per-runtime findings log with every semantics bug found and fixed.
- **FUZZ-RESULTS.md** — latest reproducible runs and their numbers.
- **DIFF.md** — a complete accounting of every Redex-rule change since the
  paper-baseline commit, organized by layer.

## Paper figures ↔ concrete programs

`figs/` holds one directory per program-bearing paper figure (`figs/4`,
`figs/5`, …) containing one plain FILE per language, named after its fuzz
lane (`trio.py`, `csharp.cs`, `tokio.rs`, …). No per-program build
scaffolding: the fuzz harness (`redex/fuzz/run.rkt`) already builds and
runs a program of a given language in the pinned environment (vendored
crates, flake toolchains), so figure programs use exactly the versions the
models were validated against. See `figs/README.md` for each figure's
pseudocode and expected outputs — all translations verified (Eagerness
`CAB`/`ABC`/nondet; Suspension `ABCAB`/`AABBC`; Extent `A`/`AB`;
Destruction `AB`/ε/`A`). `figs/1/` (the seven-language motivating example)
is scaffolding awaiting the final program text.

Run them all with **`nix run .#figs`** (also available as `figs` inside the
container): every figure program goes through the harness R times (default
5) and one markdown table per figure is printed — languages as rows, with
each distinct output and its count. Compare against the expected outputs in
`figs/README.md`.

## Notes for evaluators

- **Swift** is the one toolchain outside Nix: the container takes it from the
  official Swift 6.0.3 base image; native macOS takes it from Xcode (the dev
  shell clears `DEVELOPER_DIR`/`SDKROOT` so the system toolchain resolves).
- The first tokio/smol program of a session compiles the vendored dependency
  tree once into a shared cargo target directory (~1–2 min); the Docker build
  pre-warms this.
- Runs are CPU-bound and parallel: 8+ cores and ~8 GB RAM recommended. Never
  run two fuzz lanes of the same language concurrently (shared cargo target
  directory).
- Real runtimes are nondeterministic; re-running a seed reproduces the same
  *programs*, while observed runtime outputs may vary between runs. The
  membership claim is per observed output, so this only varies which outputs
  get checked — variation in either direction is evidence, not noise.
