# Async/Await

> Since the parent and child processes may both mutate (parts of) the same
> shared state (namely, the world), `forkIO` immediately introduces non-determinism.
> For example, if one process decides to read a file, and the other deletes it,
> the effect of running the program will be unpredictable. Whilst this non-determinism
> is not desirable, it is not avoidable; indeed, every concurrent language is
> non-deterministic. The only way to enforce determinism would be by somehow constraining
> the two processes to work on separate parts of the state (different files, in our
> example). The trouble is that *essentially all the interesting applications of
> concurrency involve the deliberate and controlled mutation of shared state,*
> such as screen real estate, the file system, or the internal data structures
> of the program.

## What makes async/await generally hard?

- Fundamental misunderstanding of execution [see SO](https://stackoverflow.com/questions/37576685/using-async-await-with-a-foreach-loop)

  ```javascript
  async function printFiles () {
    const files = await getFilePaths()

    files.forEach(async (file) => {
      const contents = await fs.readFile(file, 'utf8')
      console.log(contents)
    })
  }
  ```

  ```javascript
  // Read in sequence
  async function printFiles () {
    const files = await getFilePaths();

    for (const file of files) {
      const contents = await fs.readFile(file, 'utf8');
      console.log(contents);
    }
  }
  ```

  ```javascript
  // Read in parallel
  async function printFiles () {
    const files = await getFilePaths();

    await Promise.all(files.map(async (file) => {
      const contents = await fs.readFile(file, 'utf8')
      console.log(contents)
    }));
  }
  ```

- Control flow is hard, and understanding how basic blocks
  fit together is tricky [see SO](https://stackoverflow.com/questions/33289726/combination-of-async-function-await-settimeout)

  ```javascript
  // The while loop runs too fast!
  async function asyncGenerator() {
    while (goOn) {
      var fileList = await listFiles(nextPageToken);
      var parents = await requestParents(fileList);
    }

    // ...
  }
  ```

  ```javascript
  async function asyncGenerator() {
    while (goOn) {
      var fileList = await sleep(listFiles, nextPageToken);
      var parents = await requestParents(fileList);
    }
    // ...
  }

  // Whoops, doesn't work!
  async function sleep(fn, par) {
    return await setTimeout(async function() {
      await fn(par);
    }, 3000, fn, par);
  }
  ```

  ```javascript
  // Better loop (maybe?)
  while (goOn) {
    var [parents] = await Promise.all([
        listFiles(nextPageToken).then(requestParents),
        timeout(5000)
    ]);
  }
  ```

- Devs might be forced to use it when they don't want to [see SO](https://stackoverflow.com/questions/79612417/how-to-wait-until-async-function-finish-the-job-and-then-call-it-again-from-non)
  Ex, SwiftUI, C# forms, ...

## What makes async/await in Rust hard?

- Future execution is different from other languages [see SO](https://stackoverflow.com/questions/52835725/what-is-the-purpose-of-async-await-in-rust)

  ```cs
  async Task Foo()
  {
      var task = LongRunningOperationAsync();

      // Some other non-related operation
      AnotherOperation();

      result = task.Result;
  }
  ```

- Minimal `std` support. This is improving, but if you're a beginner it's hard
  to know which crates to use.
- `Send/'static` bounds everywhere. *Note,* this isn't inherent to async but
  to *tokio*. Other runtimes like [`smol`](https://crates.io/crates/smol)
  don't use a static threaded runtime, so `'static` bounds seldom occur.
- Deadlocks and getting semantics correct (cite Akshay and Deepti's code).

Large projects, whether they use async or not, reinvent the wheel to some degree.

To quote [HackerNews](https://news.ycombinator.com/item?id=37436413):
> At least my clunky select "runtime" code can be safely contained in a
> couple functions while the rest of the code remains blissfully unaware of
> the magic going on under the hood.

## Task APIs

- `join`/`join_all` equivalents
- `spawn`
- `cancel` is not common, it's provided by Python/Swift(/C#?), but none others

## General Async Difficulties

- What do async/await do under the hood? (Diagrams showing desugared code?)
- What is my async good for? In a vacuum
- Why is async better than threads?
- Why is blocking bad? (Related to understanding the runtime semantics)
- Preemptive v. Cooperative scheduling
- Coloring problem, calling async from non-async context
- When does async work start, when does it stop, how to propagate cancellation?

## Rust Specific Difficulties

- Stackful v. Stackless coroutines
- Tokio v. Rust std v. SMOL v. ...
- How do I share data? When do I need allocations? Where does my data live?
  - Interior mutability, and specifically Non-mutable references being not
    being immutable. I.e., & doesn't mean that the underlying value is a constant,
    but rather that that reference is shared (and thus needs some runtime checks
    and/or locking), vs. &mut means the reference is unique. “Mut” seems to
    confuse people and this comes up more in async/threaded code since most things
    aren't mut but still mutable through locks.
- Coroutines v. Tasks

## Languages

High-level table that's bound to change.

| Lang | Model | Immediate | Event Loop | Thread Safety |
|-|-|-|-|-|
|Rust|Coroutine|N| User | Trait |
|Python| Coroutine |N| User | Doc |
|JavaScript|Promise|Y| Kernel | Doc |
|OCaml <4|Promise|Y|User| Doc |
|OCaml 5 / Eio|?|?|User| Doc |
|0xCAML|?|?|User| Mode |
|Swift|Promise|Y| Kernel| Protocol |
|C#|Coroutine|Y| Kernel| ? |

### Pending Questions

- What problems are related to the syntactic sugar of async/await?
- What problems are related to the runtime semantics?
- What problems are related to implicit rules? (Drop safety, etc.)
- Are people just bad at cooperating? (Are these the same people that use
  all the machines in a shared laundry room?)

### C++

#### Basic desugaring of a function to a coroutine

```cpp
R f(Params) { body }
```

```cpp
generator<int> g() {
  for (int i = 0; ; ++i)
    co_yield i;
}


using P = typename coroutine_handle<R, Params>::promise_type;

R f(Params) {
  P p;
  auto gro = p.get_return_object();
  co_await p.initial_suspend();
  try { body } catch (...) { p.set_exception(std::current_exception()); }
final_suspend: 
  co_await p.final_suspend();
}

/* 
co_return expr; => p.return_value(expr); goto final_suspend;

co_return; => p.return_void(void); goto final_suspend;

co_yield expr; => co_await p.yield_value(expr);
*/
```

### Haskell

Docs on Haskell [Concurrency](https://hackage.haskell.org/package/async-2.2.5/docs/Control-Concurrent-Async.html#g:2)
Haskell `Async` is built on lexically-scoped threads.

### NodeJS

JS promises have no notion of a Task tree like C# and Swift (see below).

#### API

- `Promise.then`
- `Promise.catch`
- `Promise.race` (takes first settled promise)
- `Promise.all`
- `Promise.allSettled`
- `Promise.any` (takes first fulfilled promise)

#### Anti-Patterns

- Turning errors into resolved Promises by not throwing in a `catch`
- Failing to return from `then`
- Calling `then` multiple times on the same Promise

#### Cancellation

Use `AbortSignal` that acts like a cancellation token. Each promise needs to explicitly check for an abort.

### Rust

[NotGull](https://notgull.net/) has some interesting stuff.

### Python

Introduced in [PEP 492](https://peps.python.org/pep-0492/)

### Swift

[Proposal 0304](https://github.com/swiftlang/swift-evolution/blob/main/proposals/0304-structured-concurrency.md)

| Task Kind | Use when | Launched by | Launchable from | Lifetime | Cancellation | Inherits from Origin |
|-|-|-|-|-|-|-|
| `async-let` | straigt line composition | `async let x =` | async functions | scoped to statement | automatic | priority/task-local values |
| Group | dynamic # children | `group.async` | `withTaskGroup` | scoped to task group | automatic | priority/task-local values |
| Unstructured | dynamic scope |  `Task {}` | anywhere | unscoped | via `Task` | priority/task-local values/actor |
| Detached | dynamic context (priority/actor) | `Task.detached` | anywhere | unscoped | via `Task` | nothing |

Some extra notes:

- Runtime contract that "threads do not block"
- Task trees are the central data structure behind the scenes
- Marking a task as canceled does not stop the task
- When a task is canceled, all descendants are marked as cancelled too.
- Design code with cancellation in mind, "cooperative cancellation"
  Here's an example:

  > Can I write the same thing with a join-all?

  ```swift
  func fetchThumbnail(for ids: [String]) async throws -> [String: UIImage] {
    var thumbnails: [String: UIImage] = [:]
    for id in ids {
      try Task.checkCancellation() // throws an error if cancelled
      // if Task.isCancelled { break; } // NOTE, returns partial result
      thumbnails[id] = try await fetchOneThumbnail(withId: id)
    }
    return thumbnails
  }
  ```

### CSharp

> Note, I'm still looking for an "official proposal."

#### Literature

- [Awaitable/Awaiter](https://weblogs.asp.net/dixin/understanding-c-sharp-async-await-2-awaitable-awaiter-pattern)
- [Under the Covers](https://devblogs.microsoft.com/dotnet/how-async-await-really-works/)

Transformation: heap-based CPS

Microsoft documentation really emphasizes IO/CPU-bound computations. If it's IO, then just use async/await, if it's CPU bound, use `Task.Run` to place the work on a separate thread.

A Task can be configured through the [`TaskCreateOptions` enum](https://learn.microsoft.com/en-us/dotnet/api/system.threading.tasks.taskcreationoptions?view=net-9.0), which requires that a Task object be created manually. This is similar to using the Swift "unstructured Task" but the configuration options allow for the semantics of the "destructured Task." Notably, C# has a similar "Task tree" hierarchy that Swift does. There are options for spawning attached/detached children, and the semantics of synchronization depend on how the task was spawned: [Attached and Detached Children](https://learn.microsoft.com/en-us/dotnet/standard/parallel-programming/attached-and-detached-child-tasks).

#### API

*Wait* operations are blocking, whereas the *when* methods create a task that resolves when the specified task/action is finished.

- `Wait()`, with overloads for timespan and cancellation token.
- `WaitAll(Task[])`, with overloads for timespan and cancellation token
- `WaitAny(Task[])`, with overloads for timespan and cancellation token
- `WhenAll(Task[])`, with overloads for timespan and cancellation token
- `WhenAny(Task[])`, with overloads for timespan and cancellation token

#### Cancellation

To cancel tasks a `CancellationToken` needs to be created an explicitly used, everywhere. Calling `Dispose` on a Task that isn't cancelled, faulted, or finished raises an `InvalidOperation` exception.

The `OperationCancelled` (the exception that is thrown in a thread upon cancellation of an operation that the thread was executing) and `TaskCancelled` (thrown when an awaited task is cancelled) exceptions need to be handled.

#### Miscellany

A `ValueTask` may only be awaited once, consumers may not call `GetAwaiter` until the instance has completed. Value tasks are used for high-throughput applications because they reuse memory from a pool of `IValueTaskSource` (OO naming conventions ... amiright?) objects, thus reducing memory overhead.

LINQ expressions are lazy, so async calls don't happen immediately! So the `ToArray` below is necessary to force the execution of the enumerable.

```cs
private static async Task<User[]> GetUsersAsyncByLINQ(IEnumerable<int> userIds)
{
    var getUserTasks = userIds.Select(id => GetUserAsync(id)).ToArray();
    return await Task.WhenAll(getUserTasks);
}
```

## The Giant Table of Async/Await Semantics

> *Note,* coroutines exist as language constructs. *Tasks* are provided by a runtime

|Lang | Stack | Cooperation | Start | Finish | Drop-able | Cancellation | Schedule |
|-|-|-|-|-|-|-|-|
| C++ | Less | Coop | Config | Config | Y | Premp | ? |
| Rust | Less | Coop | Lazy | Eager | Y | Premp | ? |
| Python |
| Swift |
| C# |
| Haskell |
| JavaScript | Full | Premp | Eager | Eager | N | Coop | - |

## Project Ideas

### Engineering

- Identify anti-patterns and provide a debugger for them
  ([DrAsync](https://dl.acm.org/doi/pdf/10.1145/3510003.3510097)-like)
- Identify `CancellationUnsafe` futures (Sniffer-like / auto-traits)
- Identify blocking code that is called from Async (Sniffer-like)

### Education

- Memory / stack diagrams for coroutines / tasks (stacker-like)
