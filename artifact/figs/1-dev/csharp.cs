// Figure 1-dev — C# (decision-tree variant).
//
// Three calling contexts, one per dimension group:
//   ex1 START OF LIFE  plain async application, never awaited
//   ex2 END OF LIFE    spawn, extent ends un-awaited (no grace)
//   ex3 CANCELLATION   timeout a parent awaiting its spawned child
//
// spawn      = the eager async call itself
// timeout    = Figlib.Timeout: Task.WhenAny — the loser is NOT cancelled,
//              so timed-out work keeps running
//
// Predicted: ex1 `ABC` (eager AND dynamic suspension: Task.Delay(0) is
// already completed, so the await does not suspend — the whole body runs
// synchronously before C), ex2 `AC` (terminated: the process exits at
// 1 s with the task still sleeping), ex3 `AB` (WhenAny cannot cancel the
// loser; it completes during the grace).

using System;
using System.Threading.Tasks;

class Program
{
    static double Grace()
    {
        return double.Parse(
            Environment.GetEnvironmentVariable("GRACE") ?? "3",
            System.Globalization.CultureInfo.InvariantCulture);
    }

    static async Task Work(double d)
    {
        Console.WriteLine("A");
        // simulate log write
        await Figlib.Sleep(d);
        Console.WriteLine("B");
    }

    static async Task Ex1()
    {
        var t = Work(0); // plain application: the body ran synchronously
        Console.WriteLine("C");
        await Figlib.Sleep(Grace());
    }

    static async Task Ex2()
    {
        var t = Work(2); // spawn, handle dropped at scope end
        await Figlib.Sleep(1); // do other work ...
        Console.WriteLine("C");
        // extent ends: the process exits with the task still sleeping
    }

    static async Task Parent()
    {
        var task = Work(2);
        await task;
    }

    static async Task Ex3()
    {
        await Figlib.Timeout(1, Parent);
        await Figlib.Sleep(Grace());
    }

    static async Task Main(string[] args)
    {
        switch (args[0])
        {
            case "1": await Ex1(); break;
            case "2": await Ex2(); break;
            case "3": await Ex3(); break;
        }
    }
}
