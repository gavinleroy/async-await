# Real-World Scenarios for the Nine Design Dimensions

Each dimension below is anchored to a concrete real-world *mechanism* (in the
spirit of the suspension/buffered-reads example), with a paragraph of
justification and 2–3 corroborating sources. The paper's *terms* are
non-standard and return nothing in search, so every scenario is anchored to the
underlying *phenomenon* the dimension abstracts over.

Three scenarios (suspension, awareness, persistence) deliberately concretize
rationale already gestured at in the paper; the other six add fresh, evidenced
cases. Four dimensions (destruction, awareness, direction, persistence) all
touch cancellation, so the scenarios are chosen to *isolate* the specific axis.

---

## 1. Eagerness — Async on microcontrollers with no heap (Embassy)

The sharpest real-world consequence of laziness is *where the task lives in
memory*. Because Rust/Python futures are **lazy** (calling an async fn does
nothing; it returns a poll-able object), the compiler can lower an `async fn`
into a state machine that stores only the locals live across an `await` and
lives **on the stack** — no allocation. This is exactly what makes async viable
on embedded devices that have no allocator: the Embassy framework runs entirely
on a single shared stack, "never calls malloc," statically allocates all task
state, and reports three tasks totaling ~400 bytes. An **eager** or
**semi-eager** design that materializes a heap-allocated task on every call
would be a non-starter there. The flip side — the well-known beginner pain that
"a future does nothing until you `.await` or poll it" — is the cost the
dimension trades for that control.

**Evidence:**
- Embassy — <https://embassy.dev/>
- embassy-rs/embassy — <https://github.com/embassy-rs/embassy>
- Rust forum: "Futures do nothing unless you `.await` or poll them" — <https://users.rust-lang.org/t/futures-do-nothing-unless-you-await-or-poll-them/112972>

## 2. Suspension — Buffered reads starving the runtime

The buffered-read example is right and is documented at the implementation
level: an async read "may complete immediately," issuing only a single syscall,
so once a buffer is full, subsequent reads return synchronously with no actual
I/O. Under **dynamic** suspension, a hot loop of such reads never actually
yields — an I/O-bound task silently becomes CPU-bound and starves every other
task on that executor, inflating tail latency. This is concrete enough that
Tokio shipped a mitigation: each task gets a per-poll **operation budget**, and
once spent, Tokio's own resources deliberately return "not ready" to *force* a
yield (plus a `yield_now`/`coop` escape hatch — the very primitive the design
rationale mentions). **Static** suspension (JS's spec-guaranteed yield)
eliminates the failure mode by construction.

**Evidence:**
- Tokio: "Reducing tail latencies with automatic cooperative task yielding" — <https://tokio.rs/blog/2020-04-preemption>
- tokio `AsyncReadExt` docs (single syscall / may complete immediately) — <https://docs.rs/tokio/latest/tokio/io/trait.AsyncReadExt.html>
- tokio `task::coop` docs — <https://docs.rs/tokio/latest/tokio/task/coop/index.html>

## 3. Extent — Background tasks using resources after their scope closed

The canonical hazard of **indefinite** extent is a "fire-and-forget" task that
outlives the scope which owns its resources — e.g., a task that keeps using a
database connection or file handle after the `with`/`defer` block that opened it
has already cleaned it up, or the upvoted `forEach(async …)` pattern that
returns before its workers finish. This is the motivating problem behind the
structured-concurrency movement: tying a task's **dynamic** extent to a lexical
scope (Trio nurseries, Swift `TaskGroup`, Kotlin `coroutineScope`) makes "no
task escapes its scope" a structural guarantee, the same way structured
programming eliminated `goto`. The real-world payoff is that resource lifetimes
and cancellation become composable instead of a manual bookkeeping problem.

**Evidence:**
- njs: "Notes on structured concurrency, or: Go statement considered harmful" — <https://vorpus.org/blog/notes-on-structured-concurrency-or-go-statement-considered-harmful/>
- Trio core (nurseries) — <https://trio.readthedocs.io/en/stable/reference-core.html>
- Pairs with the StackOverflow `forEach` orphan example already cited in the paper.

## 4. Reference Strength — asyncio silently garbage-collecting in-flight tasks

This dimension has an unusually crisp, widely-hit bug. Because Asyncio's runtime
holds only **weak** references to tasks, `asyncio.create_task(coro)` whose handle
you don't store can be collected *mid-execution* — the work just vanishes,
sometimes with a "Task was destroyed but it is pending!" warning, sometimes
silently. The official docs now carry an explicit warning ("Save a reference to
the result of this function… The event loop only keeps weak references to tasks.
A task that isn't referenced elsewhere may get garbage collected at any time,
even before it's done") and recommend stashing tasks in a module-level `set`. A
**strong**-handle runtime (JS, C#, Tokio) runs the task to completion
regardless. This is the clearest demonstration that "does the runtime's
reference count?" is a user-visible semantic choice, not an implementation
detail.

**Evidence:**
- Python docs: `asyncio.create_task` weak-reference warning — <https://docs.python.org/3/library/asyncio-task.html>
- CPython #91887: "Use strong references for free-flying tasks" — <https://github.com/python/cpython/issues/91887>
- SuperFastPython: the asyncio disappearing-task bug — <https://superfastpython.com/asyncio-disappearing-task-bug/>

## 5. Destruction — Graceful shutdown / connection draining on SIGTERM

When an orchestrator tells a service to stop (Kubernetes sends SIGTERM, then
SIGKILL after a grace period — 30s by default), the in-flight tasks must be
*destroyed* somehow, and the three points of this dimension are exactly the
three real options operators choose between. **Terminate** (just exit) drops
in-flight writes and produces the documented failures of abrupt shutdown:
garbage/partial data, unflushed files, leaked connections. **Await** is "drain":
stop accepting new work, let active requests finish, then exit. **Cancel** stops
promptly but cleanly. The whole "graceful shutdown" genre — `Server.Shutdown`,
`terminationGracePeriodSeconds`, readiness-probe-then-drain — is the industry
working out which destruction policy to apply and how long to wait.

**Evidence:**
- Google Cloud: "Kubernetes best practices: terminating with grace" — <https://cloud.google.com/blog/products/containers-kubernetes/kubernetes-best-practices-terminating-with-grace>
- CNCF: decoding the pod termination lifecycle — <https://www.cncf.io/blog/2024/12/19/decoding-the-pod-termination-lifecycle-in-kubernetes-a-comprehensive-guide/>
- DEV: SIGTERM in-flight draining patterns — <https://dev.to/axiom_agent/nodejs-graceful-shutdown-in-production-sigterm-in-flight-draining-and-zero-downtime-deploys-2a7h>

## 6. Propagation — Swallowed background-task exceptions (Node's crash-by-default reversal)

A failed fire-and-forget task that *looks* like it succeeded is a classic
silent-failure bug, and there's a clean natural experiment: Node.js originally
took the **never**-propagate path (an unhandled promise rejection logged a
warning and the process kept running), developers routinely ignored it, and the
project judged that wrong enough to flip the default in v15 — an unhandled
rejection now **terminates the process** (DEP0018), on the reasoning that a
swallowed rejection means the app is likely in a faulty state. Python+Asyncio
similarly only surfaces "Task exception was never retrieved" at GC time. Trio
occupies the other end — its nursery re-raises child exceptions at scope exit
(the **destruction** point of this dimension) so an error can't be lost. The
shift shows this isn't academic: a whole ecosystem decided silent propagation
was a liability.

**Evidence:**
- IBM: Node.js 15 release — updated handling of rejections — <https://developer.ibm.com/blogs/nodejs-15-release-blog/>
- DZone: "The tiny mistake that crashed our Node.js app" (unhandled rejection) — <https://dzone.com/articles/unhandled-promise-rejections-nodejs-crash>
- Maxim Orlov: Node 15 default rejection behavior — <https://maximorlov.com/node-js-15-is-out-what-does-it-mean-for-you/>

## 7. Awareness (Cooperation) — Cancellation safety: data lost when a future is dropped mid-op

This is the dimension with the strongest documented "it bit a real production
team" evidence. Oxide's RFD 400 walks through exactly the failure the rationale
describes: a `Sender::send()` (or `read_exact`) used inside `tokio::select!`
gets *dropped* when another branch fires first, and because Rust's cancellation
is **unaware** — the future is just dropped, with no chance to react beyond
synchronous `Drop` — the in-flight value is "dropped — lost in the ether," or
partially-read bytes vanish and corrupt the stream. RFD 400 generalizes this to
data loss, broken cross-`await` invariants, and incomplete external cleanup
(their serial-console/migration case left a connection broken mid-session).
Tokio's own docs make "cancellation safety" a per-method contract (`read_exact`
explicitly *not* safe; `read_to_end` safe). **Aware** cancellation
(Python/Swift exceptions) is what lets a `finally`/`except` restore the
invariant.

**Evidence:**
- Oxide RFD 400: "Dealing with cancel safety in async Rust" — <https://rfd.shared.oxide.computer/rfd/0400>
- tokio `select!` docs (cancellation safety section) — <https://docs.rs/tokio/latest/tokio/macro.select.html>
- tokio discussion #4416: guaranteeing cancel safety — <https://github.com/tokio-rs/tokio/discussions/4416>

## 8. Direction — Request-scoped cancellation flowing down a call tree

The everyday version of "how does cancellation move through the graph?" is: a
client disconnects (or an HTTP/2 RST arrives, or a deadline expires) and that
cancellation must reach the in-flight database query and the downstream RPCs so
they stop burning resources on a result nobody will read. Go's `context.Context`
is the canonical **top-down** implementation — cancelling a parent context
automatically cancels every child, and `http.Request.Context()` is cancelled on
client disconnect so a context-aware DB driver aborts the query. gRPC propagates
the deadline/cancellation *across service boundaries* via the `grpc-timeout`
header so the whole chain can be cut at once. A second clean spec is Happy
Eyeballs (RFC 8305), where the first connection to win the IPv4/IPv6 race must
cancel the losing attempts. The direction choice decides whether that
propagation is automatic or a manual token you can forget to thread through.

**Evidence:**
- Go: "Canceling in-progress operations" (request context → DB query) — <https://go.dev/doc/database/cancel-operations>
- gRPC: Deadlines guide (cross-service propagation) — <https://grpc.io/docs/guides/deadlines/>
- RFC 8305 §5: cancel other connection attempts once one succeeds — <https://www.rfc-editor.org/rfc/rfc8305.html>

## 9. Persistence — Async cleanup after cancellation (sending a TLS close_notify)

The reason persistence matters in practice is that *cleanup is sometimes itself
async*. Closing a TLS connection cleanly requires sending a `close_notify` alert
so the peer is cryptographically assured the shutdown was intentional and not a
truncation attack — and that's an `await`. If a connection is being torn down
because it was cancelled/timed out, **persistent** cancellation means that
cleanup `await` *immediately re-raises* `Cancelled`, so you can't send the
goodbye unless you explicitly **shield** it (Trio's `move_on_after(…,
shield=True)`); Trio's own TLS layer documents giving up on the notification but
still closing the socket so the resource isn't leaked.
**Transient/instantaneous** cancellation (Asyncio) lets the cleanup run
unimpeded but risks a later cancellation being missed. So the persistence point
a language picks directly determines whether "send a goodbye message before you
go" is even expressible.

**Evidence:**
- Trio core docs: cancellation of async cleanup + `shield` — <https://trio.readthedocs.io/en/stable/reference-core.html>
- Trio I/O docs: TLS `close_notify` on close + cancellation behavior — <https://trio.readthedocs.io/en/stable/reference-io.html>
- njs: "Timeouts and cancellation for humans" — <https://vorpus.org/blog/timeouts-and-cancellation-for-humans/>

---

## Open questions / things to decide before this goes near the paper

- **Overlap with existing rationale.** Suspension, awareness, and persistence
  restate examples the paper already gestures at — leaned in because suspension
  is the model. If these should be *distinct* from the rationale text, second,
  non-overlapping scenarios can be found for those three.
- **Eagerness is the weakest fit.** The Embassy/stack-allocation angle is really
  a consequence of *laziness specifically*, not the eager/semi-eager points — so
  it argues "why lazy exists" more than "why the dimension matters." An
  alternative scenario that turns on eager-vs-semi-eager (e.g., Swift scheduling
  work off the main actor for UI responsiveness vs. C# running it inline) has
  supporting material and could be swapped in.

---

## Incorporation summary

How each scenario lands against the *existing* prose in `dimensions/`, ranked by
fit. "Gap" means the dimension's design rationale currently has no real-world
motivation, so the scenario adds something new. "Covered" means the section
already carries an equivalent motivating example, so no new text is needed.

| # | Dimension | Fit | Action |
|---|-----------|-----|--------|
| 4 | References | **Strong, gap** | Add — the disappearing-task bug is the best fit of the nine |
| 5 | Destruction | **Strong, gap** | Add SIGTERM/drain as a motivating opener to the rationale |
| 6 | Propagation | **Strong, gap** | Add Node v15 reversal as evidence the failure mode is real |
| 2 | Suspension | Covered | One-sentence enrichment (Tokio operation budget); buffered-read example already present |
| 8 | Direction | Good motivation, gap | Add request-cancellation opener; drop Happy Eyeballs (one example is stronger). Note: Go/gRPC sit outside the surveyed languages, so frame as illustration only |
| 7 | Awareness | Covered | RFD 400 already cited; optional `select!` data-loss instance for concreteness |
| 3 | Extent | Covered | `with`-block / goto motivation already present; optional `forEach(async …)` orphan enrichment |
| 1 | Eagerness | **Weak** | Embassy argues *laziness*, not the axis — replaced below |
| 9 | Persistence | **Redundant** | `close_notify` already in the section verbatim — replaced below |

For the two poor fits, stronger scenarios follow — both chosen so the *design
point itself raises a class of bugs*, which motivates the dimension better than a
performance or deployment anecdote.

### 1. Eagerness (replacement) — the silent no-op of a never-awaited coroutine

The Embassy scenario motivates *why laziness exists*, not why the eager /
semi-eager / lazy split is a dimension worth naming. A sharper motivation is that
the eagerness choice directly determines what goes wrong when a programmer
forgets to await. Under **lazy** evaluation (Python, Rust), calling an async
function and discarding the result does *nothing at all*: the coroutine is
constructed and dropped, the work silently never runs, and Python emits only a
`RuntimeWarning: coroutine '…' was never awaited` — a warning, not an error, that
is easy to miss in a service's logs. The work simply does not happen, and the bug
surfaces far downstream as a missing side effect. Under **eager** evaluation
(C#, JS) the same mistake has the opposite failure mode: the call runs to its
first await and keeps going as an unobserved fire-and-forget task, so the work
*does* happen, possibly concurrently and possibly with a rejection nobody
observes. The eagerness point a language picks thus decides whether "I forgot to
await" means "the work vanished" or "the work ran behind my back" — two
different, equally-documented beginner hazards that a single design dimension
predicts.

**Evidence:**
- Python docs: never-awaited coroutine `RuntimeWarning` — <https://docs.python.org/3/library/asyncio-task.html#coroutines>
- Rust async book: futures are lazy and do nothing until `.await`/polled — <https://rust-lang.github.io/async-book/>
- Rust forum: "Futures do nothing unless you `.await` or poll them" — <https://users.rust-lang.org/t/futures-do-nothing-unless-you-await-or-poll-them/112972>

### 9. Persistence (replacement) — swallowed cancellation under transient semantics

The `close_notify` scenario is already in `persistence.tex` essentially verbatim,
and it motivates the **persistent** side (cleanup gets re-cancelled, hence
shielding). A non-redundant, bug-driven motivation comes from the **transient**
side, where the hazard is the mirror image: a cancellation that is *lost*. Under
transient cancellation (Asyncio), a `CancelledError` delivered into a task can be
caught — deliberately, or accidentally by a broad `except Exception` — and once
caught it does not come back, so the task keeps running as if it were never
cancelled. This was considered dangerous enough that CPython reclassified
`CancelledError` to inherit from `BaseException` rather than `Exception` in 3.8,
specifically so ordinary `except Exception` handlers stop swallowing it, and
later added `Task.uncancel()` and a cancellation count so primitives like
`asyncio.timeout` can tell whether a cancellation they requested was actually
honored. The user-visible bug is a timeout or shutdown that silently fails to
fire because some inner `await` ate the cancellation. **Persistent** cancellation
(Trio, Swift) forecloses this class of bug by construction: the flag stays set,
so the *next* await re-raises and the signal cannot be quietly lost. The
persistence point therefore decides whether "a task ignored its cancellation" is
a recoverable choice or an unrecoverable swallowed signal.

**Evidence:**
- Python docs: Task cancellation, "must not suppress `CancelledError`," `Task.uncancel()` — <https://docs.python.org/3/library/asyncio-task.html#task-cancellation>
- Python 3.8 changelog: `asyncio.CancelledError` now inherits from `BaseException` — <https://docs.python.org/3/whatsnew/3.8.html>
- njs: "Timeouts and cancellation for humans" (why a level-triggered/persistent flag avoids lost cancels) — <https://vorpus.org/blog/timeouts-and-cancellation-for-humans/>
