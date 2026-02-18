import Foundation

func waitNGroup<T>(_ futures: AnySequence<@Sendable () async -> T>) async -> [T] 
    where T: Sendable 
{
    var results: [T] = []
    await withTaskGroup(of: T.self) { group in
        for fut in futures {
            group.addTask { await fut() }
        }
        for await t in group {
            results.append(t)
        }
    }
    return results
}

func waitN<T>(_ futures: AnySequence<Task<T, any Error>>) async -> [T] 
    where T: Sendable 
  {
    var results: [T] = []
    for task in futures {
        do {
            let value = try await task.value
            results.append(value)
        } catch {
            print("Error awaiting task: \(error)")
        }
    }
    return results
}

@main
struct Main {
    static func main() async {
        let timer = Date()
        let futures = (0...1000).map { i in { @Sendable () async in i } }
        let ns = await waitNGroup(AnySequence(futures))
        let res = ns.reduce(0, +)
        assert(res == 500500)
        let elapsed = Date().timeIntervalSince(timer) * 1_000_000
        print("done \(Int(elapsed))μs")
    }
}
