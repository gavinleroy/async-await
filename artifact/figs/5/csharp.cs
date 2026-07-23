// Figure 5 (Suspension): C# awaits are DYNAMIC — awaiting an
// already-completed task continues execution past the await without
// yielding. Work completes synchronously, so each Repeat runs to
// completion at its (eager) call site.
// Expected output: A A B B C (deterministic).

using System;
using System.Threading.Tasks;

class Program
{
    static async Task Work(string msg)
    {
        Console.WriteLine(msg);
    }

    static async Task Repeat(string msg)
    {
        await Work(msg);
        await Work(msg);
    }

    static async Task Main()
    {
        var a = Repeat("A"); // spawn: the eager call starts the task
        var b = Repeat("B");
        Console.WriteLine("C");
        await a;
        await b;
    }
}
