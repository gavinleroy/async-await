//Destruction: Terminated
using System;
using System.Threading.Tasks;

public class HelloWorld
{
    public static async Task InnerWork() {
        await Task.Delay(10_000);
        Console.Write("done");
    }

    public static async Task Work() {
        var _ = InnerWork();
        await Task.Delay(0);
        Console.Write("exiting");
    }

    public static async Task Main()
    {
        await Work();
    }
}
