using System;
using System.Runtime.CompilerServices;
using System.Threading.Tasks;

public class Program {
    public static async Task Main() {
        Console.WriteLine("Starting the stack dive...");
        await RecursiveDeathSpiral();
    }

    static async Task RecursiveDeathSpiral() {
        for (int i = 0; i < 50000; i++) {
            if (i % 1000 == 0) Console.WriteLine($"Depth: {i}");
            await new BadAwaitable();
        }
    }
}

public struct BadAwaitable {
    public BadAwaiter GetAwaiter() => new BadAwaiter();
}

public struct BadAwaiter : INotifyCompletion {
    // disallow the system from continuing execution
    public bool IsCompleted => false;

    public void GetResult() { /* empty */ }

    public void OnCompleted(Action continuation) {
        continuation();
    }
}
