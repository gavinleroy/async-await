// Figure 1 — C# (timeout variant).
//
// spawn      = the eager async call itself
// timeout    = Figlib.Timeout: Task.WhenAny — the loser is NOT cancelled,
//              so timed-out work keeps running
// isolation  = ONE ex per process (harness passes the ex number as
//              args[0]). Each ex ends with a 3 s grace sleep; with the
//              2 s work-sleep that lets race losers finish before the
//              process exits.
//
// Predicted: ex1 `AB`, ex2 `AB`, ex3 `AB` — WhenAny cannot stop the loser
// and the grace outlives it. Drop the graces to see terminated-at-exit
// behavior (`A` everywhere the loser is still sleeping at exit).

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
        var task = WriteToLog(); // spawn: the eager call starts the task
        await Figlib.Sleep(0); // do other work ...
        await task;
    }

    static async Task ProcessDetach()
    {
        var task = WriteToLog(); // spawn, handle dropped at scope end
        await Figlib.Sleep(0); // do other work ...
    }

    static async Task Ex1()
    {
        await ProcessDetach();
    }

    static async Task Ex2()
    {
        await Figlib.Timeout(0.1, ProcessAwait);
    }

    static async Task Ex3()
    {
        await Figlib.Timeout(0.1, ProcessDetach);
    }

    static async Task Main(string[] args)
    {
        switch (args[0])
        {
            case "1": await Ex1(); break;
            case "2": await Ex2(); break;
            case "3": await Ex3(); break;
        }
        var grace = double.Parse(
            Environment.GetEnvironmentVariable("GRACE") ?? "3",
            System.Globalization.CultureInfo.InvariantCulture);
        await Figlib.Sleep(grace);
    }
}
