// Figure 4 (Eagerness): Swift is SEMI-EAGER — `async let` immediately
// schedules the child task on the concurrent executor while the caller
// keeps running past the call.
// Expected output: NONDETERMINISTIC. "C" prints at its line; "A" lands
// anywhere between line 1 and the completion of `await a`, "B" between
// line 2 and `await b` (e.g. ABC, ACB, CAB, CBA, ...).
//
// Build: swiftc -swift-version 6 -parse-as-library main.swift -o main

func work(_ msg: String) async {
    print(msg)
}

@main
struct Main {
    static func main() async {
        async let a: Void = work("A")
        async let b: Void = work("B")
        print("C")
        await a
        await b
    }
}
