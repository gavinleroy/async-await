// Figure library — Swift.
//
// sleep(seconds): the lane's sleep. THROWING, deliberately: a cancelled
// Task.sleep throws CancellationError, and propagating that throw is how
// Swift cancellation cuts a function short.
// timeout(seconds, fn): race fn against a sleep in a task group and cancel
// the loser (the paper's Fig. 3 Swift version). Cancellation propagates
// structurally into fn's children.

func sleep(_ seconds: Double) async throws {
    try await Task.sleep(for: .seconds(seconds))
}

func timeout(_ seconds: Double, _ fn: @Sendable () async throws -> Void) async {
    await withoutActuallyEscaping(fn) { fn in
        await withTaskGroup(of: Void.self) { group in
            group.addTask { try? await fn() }
            group.addTask { try? await sleep(seconds) }
            defer { group.cancelAll() }
            _ = await group.next()
        }
    }
}
