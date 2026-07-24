// Figure 4 (Eagerness): C# is EAGER — an async method application runs its
// body on the calling thread until the first await point. Work contains no
// await, so it runs to completion at the call site.
// Expected output: A B C (deterministic).

using System;
using System.Threading.Tasks;

class Program
{
    static async Task Work(string msg)
    {
        Console.WriteLine(msg);
    }

    static async Task Main()
    {
        var a = Work("A");
        var b = Work("B");
        Console.WriteLine("C");
        await a;
        await b;
    }
}
