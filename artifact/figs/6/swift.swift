// Figure 6 (Extent): Swift extent is DYNAMIC — the structured child
// (`async let`) is tied to its enclosing scope; when main's scope ends
// without awaiting it, the child is cancelled (and implicitly awaited).
// The cancelled sleep throws, so "B" never prints.
// Expected output: A (deterministic).
//
// Build: swiftc -swift-version 6 -parse-as-library main.swift -o main

func work() async {
    do {
        try await Task.sleep(for: .seconds(1.0))
        print("B")
    } catch {
        // cancelled during the sleep: no print
    }
}

@main
struct Main {
    static func main() async {
        async let w: Void = work() // spawn, never awaited
        print("A")
        // end of scope: w's extent ends here — cancel + implicit await
    }
}
