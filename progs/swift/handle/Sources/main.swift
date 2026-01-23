import Foundation

actor Counter {
    var i = 0

    func get() async -> Int {
        let c = i
        i += 1
        return c
    }
}

let counter = Counter()

func trulyRandomInt() async -> Int {
    return Int.random(in: 0...1000)
}

func randomInt(loop f: Bool = false) async -> Int {
    if f {
       return await randomInt(loop: true)
    }

    dispatchPrecondition(condition: .notOnQueue(.main))
    let until = Int.random(in: 0...1000)
    let me = await counter.get();
    for _ in 0..<until {
        // NOTE we don't need an await here
        print("[\(me)] waiting")
    }
    return until
}

func sumThreeRandom() async -> Int {
  async let v1: Int = randomInt()
  async let v2: Int = randomInt()
  async let v3: Int = randomInt()
  return await [v1, v2, v3].reduce(0, +)
}

func readDir(_ path: String) async -> [String] { ["foo.txt", "main.swift"] }
func readFile(_ name: String) async -> String { "contents" }

func inGroup<ChildTaskResult>(
    of childTaskResultType: ChildTaskResult.Type = ChildTaskResult.self,
    isolation: isolated (any Actor)? = #isolation,
    body: ((sending @escaping @isolated(any) () async -> ChildTaskResult) -> Void) async -> Void
) async -> [ChildTaskResult] where ChildTaskResult : Sendable {
  return await withTaskGroup(of: ChildTaskResult.self) { group in
    await body { task in group.addTask { await task() }}
    var results: [ChildTaskResult] = []
    for await result in group {
      results.append(result)
    }
    return results
  }
}

func readDirContents(path: String) async -> [String: String] {
  let files = await readDir(path)
  var contents: [String: String] = [:]

  async let tuples = inGroup(of: (String, String).self) { run in 
    for file in files {
      run { await (file, readFile(file)) }
    }
  }

  for (file, content) in await tuples {
    contents[file] = content
  }

  return contents
}

func relateThrowingAsyncs() async throws {
  enum DumbError : Error {
    case wasLazy
  }

  func comp(for x: Duration) async throws -> Int {
    if .seconds(2) < x {
        //return await randomInt(loop: true)
        throw DumbError.wasLazy
    }
    try await Task.sleep(for: x)
    return await trulyRandomInt()
  }

  async let c1 = comp(for: .seconds(1))
  async let c2 = comp(for: .seconds(4))

  print("waiting")
  try await Task.sleep(for: .seconds(1))

  print("still waiting")
  try await Task.sleep(for: .seconds(1))

  try await print(c1)
}

actor Logger {
    static let shared = Logger()
    private var lines: [String] = []

    private init() {}

    func log(message: String) async {
        try? await Task.sleep(for: .milliseconds(10))
        lines.append(message)
    }

    func printLog() {
        print(lines.joined(separator: "\n"))
    }
}

@main
struct Program {
    static func readFile(_ file: String) async -> String {
        try? await Task.sleep(for: .seconds(1))
        return "Contents of " + file
    }

    static func logFiles(_ files: [String]) async {
      await withTaskGroup(of: Void.self) { group in 
          for file in files {
            group.addTask { 
              let contents = await readFile(file)
              await Logger.shared.log(message: contents)
            }
          }
      }
      // files.forEach { file in
      //     let contents = await readFile(file)
      //     await Logger.shared.log(message: contents)
      // }
    }

    static func main() async {
        await logFiles(["file1.txt", "file2.txt", "file3.txt", "file4.txt", "file5.txt"])
        await Logger.shared.log(message: "All files logged.")
        try? await Task.sleep(for: .seconds(1))
        await Logger.shared.printLog()
    }
}

