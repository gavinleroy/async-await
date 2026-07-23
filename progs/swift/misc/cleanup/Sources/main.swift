// func work() async throws {
//   try await Task.sleep(for: .seconds(60))
//   print("did some work")
// }


func work() async throws {
  func sleepOneSec() async {
  if (Task.isCancelled) {
    print("cancelled on entry")
  }
    _ = try? await Task.sleep(for: .seconds(1))
  }

  while true {
    if (Task.isCancelled) {
      print("i was cancelled, but continuing")
    }
    await sleepOneSec()
  }
}

@main 
struct Main {
  static func main() async {
    let t = Task { _ = try? await work() }
    try! await Task.sleep(for: .seconds(1))
    t.cancel()
    try! await Task.sleep(for: .seconds(1))
  }
}
