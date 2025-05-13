# Async/Await

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

What a CPS Coroutine model might look like

```rust
trait Future {
    type Output;

    fn schedule(self, continuation: impl FnOnce(Self::Output));
}
```
