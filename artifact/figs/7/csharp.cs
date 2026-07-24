// Figure 7 (Destruction): C# destruction is TERMINATED — the unobserved
// task has indefinite extent and keeps running after ShortLived returns,
// but when Main exits the runtime simply terminates it mid-flight: "A"
// prints at t≈1.0s, the process exits at t≈1.5s while the task sleeps
// toward "B".
// Expected output: A (deterministic).

using System;
using System.Threading.Tasks;

class Program
{
    static async Task Work()
    {
        await Task.Delay(1000);
        Console.WriteLine("A");
        await Task.Delay(1000);
        Console.WriteLine("B");
    }

    static async Task ShortLived()
    {
        var t = Work(); // spawn: eager call, handle dropped at scope end
    }

    static async Task Main()
    {
        await ShortLived();
        await Task.Delay(1500);
        // Main returns: the runtime exits, terminating the running task.
    }
}
