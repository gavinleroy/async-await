@main
@MainActor
struct AsyncProgram {
    static var counter = 0

    static func cont() async -> Bool {
        return true
    }

    static func write(_ msg: Any) async {
        print(msg, terminator: "")
    }

    static func asyncInt() async -> Int {
        await write("entering")
        let me = counter
        counter += 1
        let until = Int.random(in: 0...5000)

        for _ in 0..<until {
            if !(await cont()) {
                break
            }
            await write("\(me)")
        }
        await write("done")
        return until
    }

    // NOTE, with no suspensions all 0's are printed first
    // TODO, explain how this works with the semi-eager semantics?
    // Here's a quote from the proposal (https://github.com/swiftlang/swift-evolution/blob/main/proposals/0317-async-let.md):
    //
    // async let is similar to a let, in that it defines a local constant that is initialized by the expression on the right-hand side of the =. However, it differs in that the initializer expression is evaluated in a separate, concurrently-executing child task.
    // The child task begins running as soon as the async let is encountered. By default, child tasks use the global, width-limited, concurrent executor, in the same manner as task group child-tasks do. It is a future direction to allow customizing which executor these should be executing on. On normal completion, the child task will initialize the variables in the async let.
    static func main() async {
        async let a = asyncInt()
        async let b = asyncInt()
        print("working")
        let c = await (a + b)
        await write(c)
    }
}
