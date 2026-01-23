using System;
using System.Threading.Tasks;

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;

public class Void { }

public class Ecstatic<T> : Task<T> {
  Ecstatic(Func<T> func) : base(func) { }

  public static Ecstatic<T> New<T>(T result) {
    return Task.FromResult(result) as Ecstatic<T>;
  }

  public static Ecstatic<Void> Void() {
    throw new NotImplementedException();
  }

  public Ecstatic<TV> Then<T, TV>(Func<T, Ecstatic<TV>> then) {
    var task = this as Task<T>;
    var ret = task.ContinueWith(t => then(t.Result));
    //return new Ecstatic(ret);
    throw new NotImplementedException();
  }
}

public class FileReaderEcstatic {
  public static Ecstatic<string[]> ReadDir(string path) {
    throw new NotImplementedException();
  }

  public static Ecstatic<string> ReadFile(string path) {
    throw new NotImplementedException();
  }

  public Ecstatic<Dictionary<string, string>> ReadFileContents(string path) {
    return ReadDir(path).Then((string[] files) => {
        var contents = new Dictionary<string, string>();

        Ecstatic<Void>[] comps  = files.Select(file => ReadFile(file).Then((string content) => {
          contents[file] = content;
          return Ecstatic<Void>.Void();
        })).ToArray();

        var all = comps.Aggregate(
          Ecstatic<Void>.Void(), 
          (Ecstatic<Void> a, Ecstatic<Void> b) => a.Then((Void _void) => b)
        );

        return all.Then((Void _void) => 
          Ecstatic<Dictionary<string, string>>.New(contents));
    });
  }
}

public class FileReaderLevel1
{
    public async Ecstatic<Dictionary<string, string>> ReadFileContents2(string path) {
        var files = await ReadDir(path);
        var contents = new Dictionary<string, string>();

        var readFileTasks = files.Select(
            file => ReadFile(file).Then(content => contents[file] = content)
          ).ToList();

        var task = readFileTasks.Aggregate(
            (e, c) => e.Then(_ => c),
            Ecstatic<Void>.Void()
        );

        return task.Then(_ => 
            Ecstatic<Dictionary<string, string>>.New(contents));
    }

    public async Ecstatic<Dictionary<string, string>> ReadFileContents0(string path) {
        var files = await ReadDir(path);
        foreach (string file in files)
          contents[file] = await ReadFile(File);
        return contents;
    }

    public async Ecstatic<Dictionary<string, string>> ReadFileContents(string path) {
        var readFileTasks = files.Select(file => ReadFile(file)).ToList();
        var fileContents = await Task.WhenAll(readFileTasks);
        var contents = new Dictionary<string, string>();

        for (int i = 0; i < files.Count; i++)
            contents[files[i]] = fileContents[i];

        return Ecstatic<Dictionary<string, string>>.New(contents);
    }

    private async Task<List<string>> ReadDir(string path)
    {
        // Simulate reading directory contents asynchronously
        return await Task.Run(() => Directory.GetFiles(path).ToList());
    }

    private async Task<string> ReadFile(string file)
    {
        // Simulate reading file contents asynchronously
        return await File.ReadAllTextAsync(file);
    }
}

public class Program
{
  static int counter = 0;

  public static async Task AsyncF() {
    Console.WriteLine("Hi");
  }

  public static async Task Print(string s) {
    await Task.Delay(5);
    Console.WriteLine(s);
  }

  public static async Task<int> AsyncInt()
  {
    int me = counter++;
    int until = new Random().Next(0, 1001);
    for (int i = 0; i < until; i++)
      await Print($"[{me}] waiting");
    return until;
  }

  public static async Task Main(string[] args)
  {
    Task<int> a = AsyncInt();
    Task<int> b = AsyncInt();

    Task v = AsyncF();

    int c = await a + await b;

    Console.WriteLine(c);
  }
}
