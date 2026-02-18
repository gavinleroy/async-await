//Suspension: Dynamic
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

  public static async Task<bool> Continue() {
    return true;
  }

  public static async Task Print(string s) {
    Console.WriteLine(s);
    //await Task.Delay(1);
  }

  public static async Task<int> AsyncInt()
  {
    int me = counter++;
    int until = new Random().Next(0, 1001);
    for (int i = 0; i < until && await Continue(); i++)
      await Print($"[{me}] waiting");
    return until;
  }

  public static async Task Main(string[] args)
  {
    Task<int> a = AsyncInt();
    Task<int> b = AsyncInt();
    Console.WriteLine("working");
    int c = await a + await b;
    await Print($"{c}");
  }
}
