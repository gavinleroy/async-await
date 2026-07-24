// Figure 1 — Swift (timeout variant).
//
// spawn      = `async let` (the structured spawn: cancelled + implicitly
//              awaited at scope end)
// timeout    = figlib timeout: a task group racing fn against a sleep,
//              cancelling the loser; cancellation propagates structurally
// throws     = writeToLog propagates the cancelled sleep's throw, so a
//              cancellation cuts it before B (no do/catch needed)
// isolation  = each ex ends with a 3 s grace sleep (no-op for Swift:
//              children are cancelled at their scope ends).
//
// Predicted: ex1 `A` (child cancelled at process_detach's scope end during
// its sleep; A occasionally lost to semi-eager scheduling), ex2 `A`
// (group cancel at 0.1 s reaches the async-let child mid-sleep), ex3 `A`
// (process_detach's own scope already cancelled the child).
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
    async let task: Void = writeToLog()  // spawn
    try await sleep(0)  // do other work ...
    try await task
}

func processDetach() async throws {
    async let task: Void = writeToLog()  // spawn, never awaited
    try await sleep(0)  // do other work ...
    // scope end: the child is cancelled, then implicitly awaited
}

func ex1() async throws {
    try await processDetach()
}

func ex2() async throws {
    await timeout(1) { try await processAwait() }
}

func ex3() async throws {
    await timeout(1) { try await processDetach() }
}

@main
struct Main {
    static func main() async {
        switch CommandLine.arguments[1] {
        case "1": try? await ex1()
        case "2": try? await ex2()
        case "3": try? await ex3()
        default: fatalError("expected ex number 1-3")
        }
        let grace = Double(ProcessInfo.processInfo.environment["GRACE"] ?? "3") ?? 3
        try? await sleep(grace)
    }
}
