struct ArghError: Error, CustomStringConvertible {
    var description: String { "argh" }
}

@main
struct AsyncProgram {
    static func write(_ msg: Any) async {
        print(msg)
    }

    static func asyncInt() async throws -> Int {
        func inner() async throws {
            throw ArghError()
        }
        async let _ = inner()
        // NOTE, equivalent
        // let _ = Task { try await inner() }
        return 0
    }

    static func main() async throws {
        async let a = asyncInt()
        async let b = asyncInt()
        print("working")

        do {
            let c = try await (a + b)
            await write(c)
        } catch {
            print("caught")
        }
    }
}
