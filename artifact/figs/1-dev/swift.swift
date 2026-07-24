// Figure 1-dev — Swift (decision-tree variant).
//
// Three calling contexts, one per dimension group:
//   ex1 START OF LIFE  plain structured application, never awaited
//   ex2 END OF LIFE    spawn, extent ends un-awaited (no grace)
//   ex3 CANCELLATION   timeout a parent awaiting its spawned child
//
// spawn      = `async let` (the structured spawn: cancelled + implicitly
//              awaited at scope end)
// timeout    = figlib timeout: a task group racing fn against a sleep,
//              cancelling the loser; cancellation propagates structurally
// ex1 note   = semi-eager: the child is scheduled concurrently, so the
//              A/B/C interleaving is a race — but A and B ALWAYS appear
//              (the scope stays open past the child's completion), unlike
//              the lazy lanes' bare `C`. The nondeterminism is itself the
//              semi-eager signature.
//
// Predicted: ex1 `CAB` (common case; A/C order races), ex2 `AC`
// (scope-end cancellation cuts the child mid-sleep), ex3 `A` (cancelAll
// reaches the async-let child through the task tree at 1 s).
//
// Build: swiftc -swift-version 6 -parse-as-library

import Foundation

func graceSeconds() -> Double {
    Double(ProcessInfo.processInfo.environment["GRACE"] ?? "3") ?? 3
}

func work(_ d: Double) async throws {
    print("A")
    // simulate log write
    try await sleep(d)
    print("B")
}

func ex1() async throws {
    async let t: Void = work(0)  // plain structured application, never awaited
    print("C")
    try await sleep(graceSeconds())
    // scope end: the (long-done) child is implicitly awaited
}

func ex2() async throws {
    async let t: Void = work(2)  // spawn, never awaited
    try await sleep(1)  // do other work ...
    print("C")
    // scope end: the child is cancelled, then implicitly awaited
}

func parent() async throws {
    async let task: Void = work(2)
    try await task
}

func ex3() async {
    await timeout(1) { try await parent() }
    try? await sleep(graceSeconds())
}

@main
struct Main {
    static func main() async {
        switch CommandLine.arguments[1] {
        case "1": try? await ex1()
        case "2": try? await ex2()
        case "3": await ex3()
        default: fatalError("expected ex number 1-3")
        }
    }
}
