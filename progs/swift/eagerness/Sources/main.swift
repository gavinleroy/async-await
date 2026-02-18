@main
@MainActor
struct AsyncProgram {
    static var counter = 0

    static func write(_ msg: Any) async {
        print(msg, terminator: "")
        try! await Task.sleep(for: .milliseconds(0))
    }

    static func asyncInt() async -> Int {
        await write("entering")
        let me = counter
        counter += 1
        let until = Int.random(in: 0...5000)

        for _ in 0..<until {
            await write("\(me)")
        }
        await write("done")
        return until
    }

    // NOTE, "working" gets printed first (almost always) because
    // the other tasks are scheduled "soon" but not immediately
    static func main() async {
        async let a = asyncInt()
        async let b = asyncInt()
        print("working")
        let c = await (a + b)
        await write(c)
    }
}
