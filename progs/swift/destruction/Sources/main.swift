func inner() async {
    try? await Task.sleep(
        for: .seconds(10))
    if Task.isCancelled {
        print("I was cancelled")
    }
    print("done")
}

func work() async throws {
    async let _ = inner()
    try await Task.sleep(
        for: .seconds(0))
    print("exiting")
}

try await work()
