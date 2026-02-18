//Cancellation: None
using System;
using System.Threading.Tasks;

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;

public class Program
{
  static int counter = 0;

  public static async Task<bool> AsyncF() {
    return true;
  }

  public static async Task Print(string s) {
    Console.WriteLine(s);
    await Task.Delay(1);
  }

  public static async Task<int> AsyncInt(CancellationToken ct)
  {
    int me = counter++;
    int until = new Random().Next(0, 1001);
    int i;
    for (i = 0; i < until && !ct.IsCancellationRequested; i++)
      await Print($"[{me}] waiting");
    return i;
  }

  public static async Task Main(string[] args)
  {
    var source = new CancellationTokenSource();
    CancellationToken ct = source.Token;

    Task<int> a = AsyncInt(ct);
    Task<int> b = AsyncInt(ct);
    Console.WriteLine("working");

    // NOTE, there is some potentially interesting behavior here. As written,
    // the tasks will cancel at the beginning of each loop iteration, and
    // when cancellation occurs, the number of iterations is printed. If we
    // modified the program to pass the cancellation token down to the `Task.Delay`
    // operation, then the loop *could* raise an exception if cancellation occurs
    // within the `Task.Delay` and not at a loop boundary.
    await Task.Delay(4);
    source.Cancel();
    int c = await a + await b;
    await Print($"{c}");
  }
}
