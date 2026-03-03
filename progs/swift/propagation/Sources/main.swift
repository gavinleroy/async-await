enum Err: Error { case bad }

func inner() async throws {
    throw Err.bad
}

func work() async {
    async let _ = inner()
    try? await Task.sleep(
        for: .seconds(0))
    print("exiting")
}

await work()
