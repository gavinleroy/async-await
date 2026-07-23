import Foundation

// "A group waits for all of its child tasks to complete before it returns. Even 
// cancelled tasks must run until completion before this function returns"
func raceN<T>(_ futures: AnySequence<@Sendable () async throws -> T>) async -> T?
    where T: Sendable 
{
    var result: T?
    await withTaskGroup(of: T?.self) { group in
        for fut in futures {
            group.addTask { try? await fut() }
        }
        while let r = await group.next() {
            result = r
            break
        }
        // Marks tasks as cancelled, but this isn't blocking
        group.cancelAll()
        // BLOCK until all children complete
    }
    return result
}

func forever<T>() async throws -> T {
    //ERROR VVVV literally race would not terminate
    //while true  { await Task.yield() }
    while !Task.isCancelled  { await Task.yield() }
    throw CancellationError()
}

func id<T>(_ x: T) -> @Sendable () async -> T 
where 
   T: Sendable {
    { () in x }
}

@main
struct Main {
    static func main() async {
        let timer = Date()
        let n = 42
        let futures = (0...1000).map { i in i == n ? id(i) : forever }
        let res = await raceN(AnySequence(futures))
        assert(res == Optional.some(n))
        let elapsed = Date().timeIntervalSince(timer) * 1_000_000
        print("done \(Int(elapsed))μs")
    }
}
