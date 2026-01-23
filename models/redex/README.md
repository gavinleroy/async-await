# Redex Models

## Rules

- `async-app`
  - Run immediately ("hot start")
  - Schedule for later
  - Build coroutine ("cold start")

- `async-run`
  - *No-op,* if language uses hot starts
  - Schedule for later

- `await-continue` (awaiting on a completed Task)
  - Run immediately
  - Schedule for later

## Uncertainties

- Differences in languages make it hard to compare the "same" program
  - e.g., exceptions

- By being faithful to the language layers Rust/Python are a bit harder to understand
