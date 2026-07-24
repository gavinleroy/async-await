# Artifact: A Design Space Exploration of Async/Await

This artifact contains the models described in Section 4 of the paper "A Design Space Exploration of Async/Await".

This artifact contains executable [Redex](https://docs.racket-lang.org/redex/) semantics for the async/await
implementations of seven real runtimes — Python `asyncio`, Python `trio`,
JavaScript (node), C# (.NET), Swift, Rust `tokio`, and Rust `smol` --- together
with a differential fuzzer that tests each model against its real runtime.

## Getting Started

The only system requirement for running this artifact is Docker.

Prebuilt images are published to the GitHub Container Registry for both
`x86_64` and `arm64` (Docker selects the right one automatically):

```bash
docker pull ghcr.io/gavinleroy/async-await:latest
docker run --rm -it ghcr.io/gavinleroy/async-await:latest
```

(For a specific release, replace `latest` with the release tag.)

This drops you into a shell in the artifact directory, which contains the
full source tree — the Redex models under `redex/`, the figure programs
under `figs/` — with the three evaluation commands on `PATH`:

- `run-tests` — every model's test suite (each async test also compiles and
  runs the real program, checked against the model output)
- `fuzz` — the differential fuzzer, we'll use this later
- `figs` — runs the paper-figure programs and prints their output tables

All seven real runtimes (Python 3.14, Node, .NET, Rust, Swift 6) are
preinstalled at pinned versions; nothing is downloaded at run time. Give
Docker at least 8 GB of memory.

> **Memory requirements.** Languages are run in parallel and you'll need to provision Docker with enough memory.
>
> - Docker Desktop (macOS/Windows): Settings → Resources → Memory.
> - colima: colima start --cpu 4 --memory 16 (the default VM is 2 GB, which is not enough).
>
> If output shows `Killed` or `LANE DIED` this is a OOM error.

## Kick the Tires (5 minutes)

We will evaluate the stability of your environment by running a few small programs with the fuzzer against the model.

Run the following:

```bash
fuzz -n 2
```

You should see output *like* the following:

```
fuzz: generating 2 programs x 50 runs per lane (seed 12345)
fuzz: lanes: asyncio javascript trio smol tokio csharp swift
fuzz: cache dir /home/artifact/artifact/fuzz-cache/20260724T012624Z-seed12345  (d
etails per lane: <lang>.log, records: <lang>.jsonl)

asyncio    [########################]   2/2   done 0:30  2 ok
javascript [########################]   2/2   done 0:30  2 ok
trio       [########################]   2/2   done 0:28  2 ok
smol       [########################]   2/2   done 0:27  2 ok
tokio      [########################]   2/2   done 0:23  2 ok
csharp     [########################]   2/2   done 0:30  2 ok
swift      [########################]   2/2   done 0:37  2 ok


lane         pass  mism unconf crash     wall
asyncio         2     0      0     0     0.5m
javascript      2     0      0     0     0.5m
trio            2     0      0     0     0.5m
smol            2     0      0     0     0.5m
tokio           2     0      0     0     0.4m
csharp          2     0      0     0     0.5m
swift           2     0      0     0     0.6m
total          14     0      0     0
```

You *should not* see output that says `ERROR` or `MISMATCH`. In the second table printed, if any column except `pass` contains a non-zero value, this could indicate that environment is unstable or misconfigured. If that happens, there will be an output line such as:

```
smol: failure details in /home/artifact/artifact/fuzz-cache/20260722T215342Z-seed27 0486700/smol.log
```

This could indicate that the environment is setup incorrectly. So please let me know, including your architecture, and the contents of the printed log file.

## Evaluation (30 minutes)

The full evaluation follows the claims in the paper: we run *fifty* random programs in each language against our models. In the kick-the-tires you ran 2 programs.

Specifically, for 50 generated programs, running the real-world program 50 times produces an I/O output that the model can generate. Run the command:

```bash
fuzz -n 50
```

For each of the 7 runtimes, the fuzzer generates (a) a random *type-correct* program in the model language, and (b) compiles that program into the respective real-world program. The real program is run 50 times and each output observed is checked that it's in the set of model outputs.

This command will take quite a while to complete, not only because it's running real-world programs with `sleep`s, it also runs the Redex model that models *fine-grained* concurrency and thread interleaving.

The entire set of model outputs is not generated, instead, we lazily search through the model space for the real outputs observed. (Generating the full model search space is infeasible.) In some rare circumstances you may see an *unconfirmed* output:

This means that the exhaustiveness checker has run out of fuel when search for an output. The fuzzer has been engineered such that this doesn't happen --- at least, not often --- but it is a possible scenario that you should be aware of.

Of course, the full artifact is the actual Redex models as written, which you can find in the `redex/` directory.
