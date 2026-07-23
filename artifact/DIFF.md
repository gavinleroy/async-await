# Model changes: `2286881` → working tree

Every change to the Redex rules since commit `2286881d26686f16c5d5fad3c72cc19234f4477b`
("latexify table", 2026-04-01), when the model lived at `models/redex/`, against the
current `artifact/redex/`. Compiled by diffing all 13 model files pairwise; organized
by layer. Search/fuzz infrastructure (`fuzz/`) is out of scope except where a language
module exports something for it.

## Base language (`lc.rkt`, `core.rkt`, `exn.rkt`)

- **`fix` removed, `letrec` made first-class.** The old grammar had `(fix e)` with a
  "fix" unrolling rule, and `letrec` was a core.rkt *metafunction* desugaring a single
  binding into `fix`. Now `(letrec ([x_!_ e] ...) e)` is grammar (with E/M/G contexts)
  evaluated by a real "letrec" rule: gensym-fresh names, right-hand sides renamed
  against each other (mutual recursion), values bound in the store. The `fix` rule,
  its grammar production, and the sugar metafunction are gone.
- **`#:binding-forms` deleted** — in lc.rkt and the `async/lambda` declarations of
  py/rust/javascript/swift/csharp. No evaluation rule ever used Redex's α-machinery:
  every binder elimination (app/let/letrec/shift/async-app) explicitly renames to
  `gensyms`-fresh names and stores values in σ, and `substitute*` is defined on the
  empty `REDEX` language — it always was plain uniform renaming, which cannot capture
  when the target is globally fresh. The declarations only caused per-match freshening
  (~62% of all reduction time) and made rule firings mint α-equivalent twin
  successors. Removal is semantics-preserving; the 182-test battery plus the
  witness-vs-reference differential gate confirm.
- **exn.rkt**: renames tracking lc only (`num->string` → `number->string`,
  `append` → `string-append`, `fix G` → letrec G context).

## Timing model (`platform.rkt`, cross-cutting)

- **Logical time.** Every rule's `(where/error t_1 (step t_0))` became `t_1 = t_0`
  (~48 rules across all files); the `step` metafunction is dead. Computation is
  instantaneous; deadlines (`os/io n` = now+n) measure *wait*, not compute. The old
  per-step clock polluted deadlines with how much computation ran between two
  `os/io`s, producing false cancellations.
- **`os/block-wait`**: was "advance clock only if below the *minimum* pending
  deadline (`T:next-signal-at`)"; now jumps to *any* pending deadline (direct
  ellipsis match on T). `os/io n` promises *at least* n steps, so deadline inversion
  (a 3-tick timer firing after a 4-tick one — observed in real runtimes under
  scheduler jitter) must be expressible.
- **`sys/signal` — the biggest semantic change, in two steps.** Originally the
  `T:pop` metafunction popped only the minimum-deadline due timer. Step one: "any
  *due* timer may fire" as a nondeterministic ellipsis match (metafunctions must be
  functions; rules may be nondeterministic). Step two: the clock advance was **fused
  into delivery** — any *pending* timer, due or not, may fire, with
  `t_1 = max(t_0, t_d)`. Equivalence argument: the two-rule form (jump to any
  deadline, then deliver due) could always jump to the maximum pending deadline,
  making every timer simultaneously due, so deadline *values* never constrained
  delivery order — only creation order (causality) did. Fusion reaches exactly the
  same delivery orders without materializing clock-only intermediate states.
- **`sys/signal-cancel`** (exn layer): the `T:pop-cancelled` metafunction became an
  ellipsis match on any cancelled timer. The metafunction *faulted* ("matched 3
  different ways, 2 different results") whenever two cancelled timers were pending.

## Scheduler gating (`platform.rkt`)

- New macro flags: **`#:single-threaded`** (synchronous code runs unbounded — an
  infinite loop blocks a real event loop; `big-step` gains `#:allow-infinity?`) and
  **`#:serial-dispatch`** (the four scheduler rules — `sys/schedule`,
  `sys/schedule-cancelled` ×2, `sys/signal`, `sys/signal-cancel` — gate on a new
  `sys/idle?` metafunction: dispatch only at loop quiescence, timers only once Q is
  drained; run-to-completion + micro-before-macro).
- New **`task:uncancel`** metafunction (asyncio's one-shot cancellation delivery
  consumes the flag).
- **`big-step` cap 1 → 50.** At cap 1, `await`'s completed-check and
  dependent-registration split across interleavable steps — a lost-wakeup race that
  was a model artifact, not runtime semantics.
- Added: a generic `program-output`, and every language exports a non-collapsing
  **`-->>lang`** (the same union minus `make-big-step`) — no new semantics; it
  exposes every successor for the witness search and reference enumerator.

## Per-runtime changes

### asyncio
Restructured single-threaded: `#:single-threaded`, 0 worker slots. `os/block-coro`
no longer lowers the entry through `spawn` (back of Q); it stacks the entry task's
wrapper frame directly on the root (asyncio.run drives main immediately).
`sys/schedule` shadowed: ready thunks run as frames *on the parked root* (the
pattern is the idle gate); split into a normal rule (guard: not cancelled) and a
cancelled rule that `throw-in`s "cancelled" **and `task:uncancel`s** (one-shot
delivery). `os/block-exit-throwing` **deleted** and `os/block-exit`'s
unawaited-error guard dropped: asyncio.run returns main's value; an unretrieved
task exception is stderr-only (PROPAGATION: log, not reraise).

### trio
`#:single-threaded`, 0 slots, same inline-entry restructuring but the entry wrapper
keeps the `task:await-dependencies` nursery tail. Dispatch shadows are
**any-position pop** (trio deliberately shuffles runnable batches — a sound
over-approximation) and cancellation splits three ways: fresh spawn thunks
(reset-shaped) dispatch *normally* even when cancelled (probed: a cancelled child
still runs to its first checkpoint), resumed continuations get `throw-in` (a
suspension *is* a checkpoint), and there is no `uncancel` (sticky scopes). The
`os/io` override now allocates the io task as a *child* of the issuer
(`allocate-dependency`) and adds the previously missing `catch` wrapper — without
it a cancellation thrown into a pending io thunk escaped as a bare throw and its
waiters never woke.

### tokio
Full restructuring. Inline entry: `os/block-coro` stacks the entry future's frame
on the root (probed: block_on polls on the calling thread), wrapping the result as
`(struct [type "Ok"] [value …])` — the **JoinHandle → Result** discipline (spawn
settles Ok; cancellation settles Err; awaiting a coroutine stays raw). Dispatch:
the old head-pop with an inline `is-cancelled? → (void)` hack became three rules —
any-position **work-stealing dispatch** (guard: not cancelled),
**`sys/schedule-main`** (a queue entry whose label unifies with the `self` pointer
of the task the root blocks on resumes as a frame on the parked root, any
position — block_on resumptions don't queue behind workers), and
`sys/schedule-cancelled` (any position; settles Err and wakes dependents *without
running the body*). `sys/signal-cancel`: the old rule dropped the cancelled timer
on the floor; now it pushes to Q so the Err-settle wakes dependents (the drop
deadlocked `os/block`). New **`os/block-done`**: exit the moment the entry settles,
dropping Q and T (pending work abandoned) but *keeping worker frames* — mid-poll
workers finish, producing the racy shutdown-tail prints after the final result.
The free-running clock is the base fused `sys/signal` (no shadow); a prose note
records the provenance (output `ABC|24` was enumeration-proven unreachable under
the old quiescent-only clock, yet the real runtime produced it).

### smol
Same inline Ok-wrapping entry, `sys/schedule-main`, Err-settling
`sys/schedule-cancelled`, Q-pushing `sys/signal-cancel`, and exit-drops-Q/T
`os/block-done` as tokio (with 1 executor slot and FIFO head-pop dispatch kept —
smol's executor is serial). Added **`sys/schedule-reactor`**: io-wake-shaped
queue entries pop from ANY position — real smol completes timers on the
reactor thread, so an unpolled task at the head of the executor queue cannot
delay an io completion (found by the in-container Linux fuzz:
cancel-before-first-poll outputs were provably unreachable under pure FIFO;
see FUZZ.md Findings 2026-07-22). Two smol-specific cancel rules replaced the old
spawn-a-canceller encoding: **`cancel-unstarted`** (an unpolled task is closed in
place — unlinked from Q, settled Err, waiter allocated already-done, no executor
round-trip; matches async-task) and an inline flag-set on the caller's own poll for
started tasks (the old rule deferred the flag to a queued canceller task, which let
already-queued wakeups of the target run first — orderings real smol cannot
produce).

### javascript
`#:single-threaded` + `#:serial-dispatch` (micro-before-macro verified against
node). `await` on a *settled* promise: the old rule parked the continuation in the
task's waiters — which never drain again — a guaranteed lost wakeup (6/6 generated
programs stuck). Now it `os/start-soon`s the continuation directly (real JS queues
a microtask). `sys/schedule` shadow: microtasks run as frames on the parked root.
`-->js` was accidentally built from `make-big-step -->sys/exn`, so the overrides
never ran — now `-->sys/overrides`.

### swift
Cancellation rebuilt as **flag-only cooperative** (probed on Swift 6):
`sys/schedule` shadow with *no* cancelled guard (a cancelled task's body still
runs), a `sys/signal` shadow that is the fused delivery *minus* the cancelled guard
(a cancelled sleeper's timer still fires; without this it deadlocks in T), and
`sys/schedule-cancelled` / `sys/signal-cancel` disabled outright
(`side-condition #false`). The old platform-exn behavior threw "cancelled" into
every cancelled task's dispatch — provably wrong against the real runtime.

### csharp
`-->c#` was built from `make-big-step -->sys/exn`, making its `os/block-done`
override (exit with tasks remaining in Q/T) dead code; now `-->sys/overrides`.
Otherwise only the cross-cutting changes.

### py / rust (surface languages)
Besides binding-forms removal: the `async-app` freshness bug,
`(gensyms (σ e_body) …)` → `(gensyms (σ_0 e_body) …)`. The bare `σ` was a literal
symbol, so fresh names were not guaranteed disjoint from the store — and `ext1`
*replaces* on key collision, silently corrupting a live binding. (js/swift/csharp
always guarded correctly.) The trivial `resume!` metafunction was dropped (plain
application).

## Validation

Every change above is exercised by the 182-test module battery, the
witness-vs-reference differential gate (`fuzz/witness-check.rkt`), and two clean
full fuzz runs (560 programs across 7 runtimes, 0 mismatch / 0 unconfirmed /
0 crash — see FUZZ-RESULTS.md). Two places encode claims about the real runtimes
that rest on runtime probes rather than rules alone: swift's disabled-rule shadows
(flag-only cancellation) and tokio/smol's `os/block-done` Q/T-drop with surviving
worker frames (racy shutdown tail). The probes are documented in FUZZ.md.
