import Foundation

func worker(name: String, iterations: Int) async {
    for i in 0..<iterations {
        for j in 0..<(iterations*iterations) {
                _ = pow(Double(i), Double(j))
        }
    }
    print("Worker [\(name)] \(iterations) done")
    try? await Task.sleep(for: .milliseconds(10))
    print("Worker \(name) exiting")
}

@main
struct Program {
    static func main() async {
        async let w1 = worker(name: "A", iterations: 100)
        async let w2 = worker(name: "B", iterations: 50)
        print("Main waiting for workers")
        try? await Task.sleep(for: .milliseconds(1))
        await (w1, w2)
        print("Main exiting")
    }
}

