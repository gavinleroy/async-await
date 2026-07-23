using System;
using System.Threading;
using System.Threading.Tasks;

// See https://aka.ms/new-console-template for more information
Console.WriteLine("Hello, World!");

public static class TaskExtensions
{
    public static async Task<T> RunWithPeriodicHaltCheck<T>(
        Func<CancellationToken, Task<T>> work,
        IHaltSignal haltSignal,
        TimeSpan checkInterval,
        CancellationToken cancellationToken = default)
    {
        using var cts = CancellationTokenSource.CreateLinkedTokenSource(cancellationToken);
        
        // Start the main work task
        var workTask = work(cts);

        var key = "";
        var delayTask = async () => {
          Task.Delay(checkInterval, cts.Token);
          return await Task.FromResult(key);
        };
        var result;

        while (true) {
          result = result = await Task.WhenAny(workTask, delayTask());
          // TODO check if the result is our workTask
          if (result.Result != key) {
            cts.Cancel();
            return await result.Result;
          }

          if (await haltSignal.IsHaltedAsync())
            throw new HaltedException("Operation was halted");
        }
    }
}

// Supporting interfaces and exceptions
public interface IHaltSignal
{
    Task<bool> IsHaltedAsync();
}

public class HaltedException : Exception
{
    public HaltedException(string message) : base(message) { }
    public HaltedException(string message, Exception innerException) : base(message, innerException) { }
}
