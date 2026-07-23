using System;
using System.Threading;
using System.Threading.Tasks;
					
public class Program
{
  // static async Task<bool> True() {
  //   await Task.Delay(10);
  //   return true;
  // }

  static async Task Work(string msg) {
    await Task.Delay(10);
    Console.WriteLine(msg);
  }

	public static async Task Main()
	{
		Task t1 = Work("A");
		Task t2 = Work("B");
    Console.WriteLine("C");
		await t1;
		await t2;
	}
}
