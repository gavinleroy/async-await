import Foundation

enum HaltedError: Error, CustomStringConvertible {
    case halted;
    var description: String {
        "Operation halted"
    }
}

actor HaltSignal {
    private var shouldHalt: Bool = false;

    func setHalt(_ value: Bool) {
        self.shouldHalt = value
    }

    func isHalted() -> Bool {
        return self.shouldHalt
    }

    func reset() {
        self.shouldHalt = false
    }
}

func runWithPeriodicHaltCheck<T: Sendable>(
    work: @escaping @Sendable () async throws -> T,
    haltSignal: HaltSignal,
    checkInterval: Duration
) async throws -> T {
    return try await withThrowingTaskGroup(of: T.self) { group in
        group.addTask {
            return try await work()
        }
        group.addTask {
            while true {
                try await Task.sleep(for: checkInterval)
                    if await haltSignal.isHalted() {
                        throw HaltedError.halted
                    }
            }
        }

        guard let result = try await group.next() else {
            throw CancellationError();
        };
        group.cancelAll();
        return result
    }
}

@Sendable func myAsyncTask() async throws -> String {
    print("Task: Starting work...")
        try await Task.sleep(for: .seconds(1))
        try await Task.sleep(for: .seconds(1))
        print("Task: Finished work.")
        return "Task Completed Successfully"
}


@main
struct MainApp {
    static func main() async {
        let haltSignal = HaltSignal()
            let checkInterval = Duration.seconds(0.5)

            print("Scenario 1: Running task, expecting completion.")
            await haltSignal.reset() // Ensure signal is false

            let task1 = Task { // Run in a separate Task
                do {
                    let result = try await runWithPeriodicHaltCheck(
                            work: myAsyncTask,
                            haltSignal: haltSignal,
                            checkInterval: checkInterval
                            )
                        print("Scenario 1 Result: \(result)")
                } catch {
                    print("Scenario 1 Error: \(error)")
                }
            }
        await task1.value // Wait for scenario 1 to complete

            print("--------------------")

            print("Scenario 2: Running task, expecting halt.")
            await haltSignal.reset() // Reset signal

            // Task that runs the work with periodic check
            let task2 = Task {
                do {
                    let result = try await runWithPeriodicHaltCheck(
                            work: myAsyncTask,
                            haltSignal: haltSignal,
                            checkInterval: checkInterval
                            )
                        print("Scenario 2 Result: \(result)")
                } catch {
                    print("Scenario 2 Error: \(error)") // Will catch HaltedError here
                }
            }

        // Task that sets the halt signal after a delay
        let signalTask = Task {
            try await Task.sleep(for: .seconds(1));
            print("Scenario 2: Setting halt signal!");
            await haltSignal.setHalt(true);
        }

        // Wait for both tasks associated with scenario 2 to complete.
        // We primarily care about task2 finishing its attempt.
        await task2.value;
        // Optionally wait for signalTask too, or cancel it if task2 finishes early.
        signalTask.cancel(); // Cancel the signal task if it's still running (no-op if finished)
                             // await signalTask.value // Or wait for it if needed

        print("--------------------");
    }
}
