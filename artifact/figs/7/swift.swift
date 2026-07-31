// Figure 7 (Destruction): Swift destruction is CANCELLED — the structured
// child's extent ends with shortLived's scope, where it is cancelled (and
// implicitly awaited). Cancellation lands during work's first sleep, so
// neither print runs.
// Expected output: nothing (deterministic).
//
// Build: swiftc -swift-version 6 -parse-as-library main.swift -o main

func work() async {
    do {
        try await Task.sleep(for: .seconds(2))
        print("A")
        try await Task.sleep(for: .seconds(2))
        print("B")
    } catch {
        // cancelled during a sleep: no further prints
    }
}

func shortLived() async {
    async let t: Void = work() // spawn, never awaited
    // end of scope: t is cancelled + implicitly awaited
}

@main
struct Main {
    static func main() async {
        await shortLived()
        try? await Task.sleep(for: .seconds(3))
    }
}
