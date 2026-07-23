# Artifact: A Design Space Exploration of Async/Await

This artifact contains the models described in the paper, as well as scripts to reproduce figures of program output. A rough overview of the data for which we've provided an artifact to evaluate:

- Figure 1, program outputs for all sampled languages.
- Figure 4, program outputs for select runtimes
- Figure 5, program outputs for select runtimes
- Figure 6, program outputs for select runtimes
- Section 4, a fuzzer for providing evidence that the formal model reflects reality

An overview of what this artifact contains: executable PLT Redex semantics for the async/await
implementations of seven real runtimes — Python `asyncio`, Python `trio`,
JavaScript (node), C# (.NET), Swift, Rust `tokio`, and Rust `smol` --- together
with a differential fuzzer that tests each model against its real runtime.

## Getting Started

The environment is provided in one of two ways: Nix (with flakes) and Docker. Pick whichever you're most familiar with.

### Nix

`nix run .#image`

### Docker

TODO

## Kick the Tires (5 minutes)

We will evaluate the stability of your environment using two commands.

1. We will test the language environments (e.g., Rust, Swift), run the following:

    ```bash
    GRACE=0 figs 1
    ```

    The provided output should read as follows:

    ```
    ## Figure 1

    | language | status | ex1 (5 runs) | ex2 (5 runs) | ex3 (5 runs) |
    |---|---|---|---|---|
    | csharp | ok | `AB` | `AB` | `AB` |
    ```

    This command runs the program in Figure 1 for all languages. If you see the table as output (rows potentially permuted), then the full evaluation will work.

    > **Note, this *will not* output the same data as Figure 1.** By setting `GRACE=0` this makes the command faster, at the expense of correctness. This is just to test that the environment is executable on your machine.

2. We will test the Redex model environment, run the following:

    ```bash
    fuzz -n 2
    ```

    You should see output *like* the following:

    ```
    fuzz: generating 2 programs x 20 runs per lane (seed 270486700)
    fuzz: lanes: asyncio javascript trio smol tokio csharp swift
    fuzz: cache dir /home/artifact/artifact/fuzz-cache/20260722T215342Z-seed270486700  (d
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

We will run the full evaluation in two parts. Evaluating the *figures* and evaluating the *models*.

### Figures (5 minutes)

Run the command: `figs`

This command will run the programs for the figures 1, 4, 5, and 6, which are those that claim specific outputs. You may match the output of each printed figure table to that in the paper. If it's correct, it will print the following:

TODO

The programs used to model the figures are available in the `figs/` directory, should you want to look at them yourself.

### Redex Models (30 minutes)

We claim that our Redex models match the behavior of real-world, specifically, that for 50 randomly generated programs, running the real-world program 50 times produces an I/O output that the model can generate. Run the command:

```bash
fuzz -n 50
```

For each of the 7 runtimes, this generates (a) a random *type-correct* program in the model language, and (b) compiles that program into the respective real-world program. The real program is run 50 times and each output observed is checked that it's in the set of model outputs.

This command will take quite a while to complete, not only because it's running real-world programs with `sleep`s, it also runs the Redex model that models *fine-grained* concurrency and thread interleaving.

The entire set of model outputs is not generated, instead, we lazily search through the model space for the real outputs observed. (Generating the full model search space is infeasible.) In some rare circumstances you may see an *unconfirmed* output:

This means that the exhaustiveness checker has run out of fuel when search for an output. The fuzzer has been engineered such that this doesn't happen --- at least, not often --- but it is a possible scenario that you should be aware of.

Of course, the full artifact is the actual Redex models as written, which you can find in the `redex/` directory.
