// Figure 1-dev — Swift (decision-tree variant).
//
// Three calling contexts, one per dimension group:
//   ex1 START OF LIFE  plain structured application, never awaited
//   ex2 END OF LIFE    spawn detached, extent ends un-awaited
//   ex3 CANCELLATION   timeout a parent awaiting its spawned child
//
// spawn      = `async let` (the structured spawn: cancelled + implicitly
//              awaited at scope end — a task CANNOT detach)
// timeout    = figlib timeout: a task group racing fn against a sleep,
//              cancelling the loser; cancellation propagates structurally
// ex1 note   = semi-eager: the child is scheduled concurrently, so the
//              A/B/C interleaving is a race — but A and B ALWAYS appear
//              (the scope stays open past the child's completion), unlike
//              the lazy lanes' bare `C`. The nondeterminism is itself the
//              semi-eager signature.
//
// Predicted: ex1 `CAB` (common case; order races), ex2 `AC`
// (processDetached's scope end cancels the child at birth; its body
// still runs, so A prints, but the sleep throws), ex3 `AC` (cancelAll
// at 1 s reaches the async-let child through the task tree).
//
// Build: swiftc -swift-version 6 -parse-as-library

import Foundation

func writeToLog() async throws {
    print("A")
    // simulate log write
    try await sleep(2)
    print("B")
}

func processAwait() async throws {
    async let task: Void = writeToLog()
    try await sleep(0)
    try await task
}

func processDetached() async {
    async let task: Void = writeToLog()
    // scope end: the child is cancelled, then implicitly awaited
}

func ex1() async throws {
    async let t: Void = writeToLog()  // plain structured application, never awaited
    print("C")
    try await sleep(3)
    // scope end: the (long-done) child is implicitly awaited
}

func ex2() async throws {
    await processDetached()
    try await sleep(1)
    print("C")
}

func ex3() async {
    await timeout(1) { try await processAwait() }
    print("C")
    try? await sleep(3)
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
