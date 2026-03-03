using System;
using System.Threading.Tasks;

using Ecstatic = System.Threading.Tasks.Task;

static class Logger {
  static private List<String> lines = new List<String>();

  static public async Task log(string message) {
    await Task.Delay(10);
    lines.Add(message);
  }

  static public async Task printLog() {
    await Task.Delay(10);
    Console.WriteLine(String.Join("\n", lines));
  }
}

class Program
{
   static async Task<string> readFile(string file) {
     await Task.Delay(1000);
     return "Contents of " + file;
   }

    static async Task logFiles(List<string> files) {
      files.ForEach(async (file) => {
          var contents = await readFile(file);
          await Logger.log(contents);
      });
    }


    // static async Ecstatic AsyncF()
    // {
    //     Console.WriteLine("async running");
    // }
    //
    // static async Ecstatic Wrapper()
    // {
    //     var task = AsyncF();
    //     await Task.Delay(1000); // Sleep for 1 second
    //     Console.WriteLine("wrapper running");
    //     await task;
    // }

    static async Task Main(string[] args)
    {
        await logFiles(["file1.txt", "file2.txt", "file3.txt", "file4.txt", "file5.txt"]);
        await Logger.log("All files logged.");
        await Task.Delay(1000);
        await Logger.printLog();
        //await Wrapper();
    }
}
