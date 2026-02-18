//Exception: awaited
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
    await Task.Delay(2);
  }

  public static async Task<int> AsyncInt() {
    var inner = async () => {
      throw new Exception("argh");
    };
    inner();
    return 0;
  }

  public static async Task Main(string[] args) {
    Task<int> a = AsyncInt();
    Task<int> b = AsyncInt();
    int c = await a + await b;
    await Print($"{c}");
  }
}
