import Foundation
import _Concurrency

func timeout<T: Sendable>(
  duration: Duration,
  f: @Sendable () async throws -> T
) async throws -> T? {
  try await withoutActuallyEscaping(f) { f in
    try await withThrowingTaskGroup(of: T?.self) { group in
      group.addTask { try await f() }
      group.addTask {
        try await Task.sleep(for: duration)
        return nil
      }

      let result = try await group.next()!
      group.cancelAll()
      
      return result
    }
  }
}


print(try! await timeout(duration: .seconds(1)) { 
  try await Task.sleep(for: .seconds(2)) 
  return "HI"
})

print(try! await timeout(duration: .seconds(1)) { 
  try? await Task.sleep(for: .seconds(0.5)) 
  return "HI"
})

let task = Task { 
  try await timeout(duration: .seconds(10)) {
    try await Task.sleep(for: .seconds(1))  
  } 
}
task.cancel()
print(try? await task.value)