# Design

## Sep 9, Meeting

Formalize and prove safety/lifeness properties for a given async program (designs).

Framing: we are trying to surface the ipmlicit theorems in the desigsn of these languages as opposed to concurrency theory

section 1: intro
section 2: grounded in problems that users have across languaegs
section 3: worked examples, semi-formal examples of how X works (e.g., cancellation) in languages
tables: properties, tasks, etc

## Sep 16, Meeting

## ---

Before I begin, here are some hypotheses about this fucking project.

- Async is *harder* in Rust because of Ownership + Traits: developers must think
  about the lifetime of a computation (dynamic) in terms of the lifetime of a
  variable (static). Rust does not impose a runtime, and since the default
  runtime is not *structured,* reasoning about computation lifetime is harder. :tm:

- There are additional difficulties in Rust like async iterators and other
  API surfaces that are not yet stable.

- The underlying coroutine model *does not matter.* Unless, you're C++ and
  you've forced developers to write their own types, then it really does.

## Runtime Design Decisions

### Structured vs Unstructured Concurrency

- *Structured,* the lifetime of a child will *not* outlive the
  parent. This follows traditional scoping rules.

- *Unstructured,* explicit monitoring trees are necessary, and
  the developer must implement this in library code. APIs may
  not follow the same conventions.

### Strong vs Weak (Runtime) Task References

- *Strong,* all tasks registered in the runtime will continue
  to run, regardless of whether the user has awaited them or not.
  This makes sense for `'static` tasks, but logic bugs can cause  
  memory performance issues later.

- *Weak,* logic bugs are silently cleaned up, just like memory.
  This can cause problems because the strong references, e.g.,
  on a stack, are the only thing keeping an operation running and
  the lifetime of a computation may not be obvious.

### Can the Runtime Cancel Running Tasks

- *Yes,* on shutdown of the event loop, it can cancel and remove
  all running tasks. Hides logic bugs and not every task needs
  to be awaited.

- *No,* a program with an infinite computation will not terminate.
  This follows from a sync program with an infinite loop that
  wouldn't terminate.

## Safety

- Exception Safety

- Lifetime Safety

- Resource Leaks

- Data Races / API Races

- Forward Progress

## Lifetime Safety

> **Concurrency Resource,** treat concurrency as a resource that can be created
> and destroyed. A "concurrency resource" is *created* when you start a
> potentially concurrent operation and *destroyed* when you join a potentially
> concurrent operation.

Join point can be either be a "happens with" (thread synchronization) or
a "sequenced with" (same thread).

> **Structured Concurrency,** ensures that concurrency resources have lifetimes
> that nest within program scopes. Deterministically reason about the lifetime
> of concurrent operations so that we can ensure all concurrent use of an object
> *happens before* the object's destruction.

```rust
fn other_work() {}
async fn bar<T>(x: &T) {}

// NOTE, this code would execute without error,
// but the type system doesn't allow it because 
// the lifetime of `t` is unknown.
async fn foo<T>(x: &T) {
  let t = tokio::spawn(bar(x));
  other_work();
  return t.await;
}
```

A *detached operation* is something that you may want. By default (in Tokio),
you only get detached operations, but you only need a detached operation
rarely --- it shouldn't be the default. Every task should have a *continuation,*
detached operations do not.

## Destructor Strategies

- Join by blocking
- Detach
- Cancel

```cpp
future<std::vector<int>> get_common_friends(database& db, int uid1, int uid2) {
  future<std::vector<int>> f1 = get_friends(db, uid1);
  future<std::vector<int>> f2 = get_friends(db, uid2);

  auto ids1 = co_await std::move(f1);
  auto ids2 = co_await std::move(f2);
  //auto [ids1, ids2] = co_await when_all(std::move(f1), std::move(f2));

  co_return common_elements(std::move(ids1), std::move(ids2));
}
```

## Intuition

*(If your language does not support structured concurrency)*
Concurrency resources should be scoped, and *lazily started* tasks
should be the default in order to actually get concurrency. Use
concurrency combinators to encapsulate different error-reduction
strategies.

- `when_all`
- `when_all_ready`
- `when_range`
- `when_windowed`
- `when_windowed`
- `take_until`
- `timeout(source, dur)` => `take_util(source, schedule_after(dur))`
- `via`
- `on`
- `when_any`
- `merge`
- `when_n_successful`
- ...

## Problems

Found using

- [Top 50 Most Upvoted `async-await` questions](https://data.stackexchange.com/stackoverflow/query/1912276/top-50-most-upvoted-async-await-questions)

- []()

### [Using a `forEach` loop](https://stackoverflow.com/questions/37576685/using-async-await-with-a-foreach-loop)

```javascript
async function printFiles () {
  const files = await getFilePaths()

  files.forEach(async (file) => {
    const contents = await fs.readFile(file, 'utf8')
    console.log(contents)
  })
}
```

> This code does work, but could something go wrong with this? I had someone
> tell me that you're not supposed to use async/await in a higher-order
> function like this, so I just wanted to ask if there was any issue with this.

## [Call async from sync](https://stackoverflow.com/questions/9343594/how-to-call-asynchronous-method-from-synchronous-method-in-c)

## [What does a suspend function mean in Kotlin coroutines?](https://stackoverflow.com/questions/47871868/what-does-a-suspend-function-mean-in-kotlin-coroutines)

## [Catching exceptions](https://stackoverflow.com/questions/5383310/catch-an-exception-thrown-by-an-async-void-method)

Exceptions don't follow the traditional flow if they are not awaited directly, and
"async void" functions in C# don't have a Task object to capture the exception.

> I actually mean it's straight-forward to read - whereas I know what's actually
> going on is really complicated - so my brain is telling me not to believe my eyes...

## [Give me a simple example](https://stackoverflow.com/questions/50757497/simplest-async-await-example-possible-in-python)

Examples provided use a lot (comparatively) of the async API. The seemingly
extra details make users get lost.
