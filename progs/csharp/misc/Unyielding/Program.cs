using System;
using System.Threading;
using System.Threading.Tasks;
					
public class Program
{
  static async Task<bool> True() {
    return true;
  }

  static async Task Unyielding(string msg) {
    while (await True()) {
      Console.WriteLine(msg);
    }
  }

	public static async Task Main()
	{
		Task t1 = Unyielding("C1");
		Task t2 = Unyielding("C2");
		await t1;
		await t2;
	}
}
