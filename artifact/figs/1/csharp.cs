// Figure 1-dev — C# (decision-tree variant).
//
// Three calling contexts, one per dimension group:
//   ex1 START OF LIFE  plain async application, never awaited
//   ex2 END OF LIFE    spawn detached, extent ends un-awaited
//   ex3 CANCELLATION   timeout a parent awaiting its spawned child
//
// spawn      = the eager async call itself
// timeout    = Figlib.Timeout: Task.WhenAny — the loser is NOT cancelled,
//              so timed-out work keeps running
//
// Predicted: ex1 `ACB` (eager: A prints synchronously inside the call;
// the await on the pending delay suspends, so B lands after C), ex2 `AC`
// (terminated: the process exits at 1 s with the detached task still
// sleeping), ex3 `ACB` (WhenAny cannot cancel the loser; it completes
// during the grace).

using System;
using System.Threading.Tasks;

class Program
{
    static async Task WriteToLog()
    {
        Console.WriteLine("A");
        // simulate log write
        await Figlib.Sleep(2);
        Console.WriteLine("B");
    }

    static async Task ProcessAwait()
    {
        var task = WriteToLog();
        await Figlib.Sleep(0);
        await task;
    }

    static async Task ProcessDetached()
    {
        var task = WriteToLog();
    }

    static async Task Ex1()
    {
        var t = WriteToLog(); // plain application: runs eagerly to its first await
        Console.WriteLine("C");
        await Figlib.Sleep(3);
    }

    static async Task Ex2()
    {
        await ProcessDetached();
        await Figlib.Sleep(1);
        Console.WriteLine("C");
        // extent ends: the process exits with the task still sleeping
    }

    static async Task Ex3()
    {
        await Figlib.Timeout(1, ProcessAwait);
        Console.WriteLine("C");
        await Figlib.Sleep(3);
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
