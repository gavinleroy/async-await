# Tasks

This file contains a list of benchmark programs used to evaluate the semantics
of async/await constructs in the wild. Each task contains a description of the
intended program behavior, and then links to the implementation of that task
in various languages. We draw a distinction between coroutines and tasks when
both are exposed by the language.

Some quick terminology:

- *computation*: refers to work performed concurrently. Typically used to refer
  to a coroutine or task.

- *coroutine*: work that can be suspended and later resumed on the
  *current thread.* Coroutines live at the language level and in these
  examples imply that a runtime is *not* involved (yet). The three
  languages that *expose* coroutines are C++, Rust, and Python.

  ```rust
  async fn read_file(file: std::path::Path) -> String 
  { /*...*/ }

  fn client() {
    let fut = read_file("./README.md");
    //  ^^^ `fut` is a `coroutine` and has not been scheduled.
    // It won't do anything until it's polled, and coroutines 
    // need to be polled by something
  }
  ```

- *task*: work that is spawned by the current executor (runtime). Tasks commonly
  imply that the work may run on a different thread but this depends on the runtime.

The languages that will be used in each of the benchmarks

- C++ (cppcoro)
- Rust (tokio)
- Rust (smol)
- Python (asyncio)
- Haskell
- C#
- Swift
- JavaScript

<!-- ## Call async function, await it -->
<!---->
<!-- ## Start computation, do sync work, then get the result -->
<!---->
<!-- - IO bound -->
<!-- - comp bound -->

## Wait for N concurrent computations to finish (`wait-n`)

## Race N computations against each other (race-n)

## Cancel task (`cancel`)

## Spawn a task on thread T (`spawn-on`)

## Call async from sync code (`from-sync`)
