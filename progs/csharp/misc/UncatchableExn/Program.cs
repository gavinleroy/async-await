using System;
using System.Threading;
using System.Threading.Tasks;

namespace AsyncVoidCLI
{
    class Program
    {
        static bool _isRunning = true;

        static void Main(string[] args)
        {
            AppDomain.CurrentDomain.UnhandledException += (sender, e) =>
            {
                Console.ForegroundColor = ConsoleColor.Red;
                Console.WriteLine("\n\n[CRITICAL SYSTEM FAILURE]");
                Console.WriteLine($"The application crashed due to an unhandled exception: {((Exception)e.ExceptionObject).Message}");
                Console.ResetColor();
                Environment.Exit(1);
            };

            Console.WriteLine("=== Text Editor CLI (Simulated) ===");
            Console.WriteLine("Type 'save' to save the file (triggers background task).");
            Console.WriteLine("Type 'exit' to quit.");
            Console.WriteLine("---------------------------------------------------");

            while (_isRunning)
            {
                Console.Write("\n> ");
                string input = Console.ReadLine();

                if (string.IsNullOrEmpty(input))
                  continue;
                else if (input.Trim().ToLower() == "exit")
                    _isRunning = false;
                else if (input.Trim().ToLower() == "save")
                    OnSaveCommand();
                else
                    Console.WriteLine($"You typed: {input}");
            }
        }

        static void OnSaveCommand()
        {
            try
            {
                Console.ForegroundColor = ConsoleColor.Yellow;
                Console.WriteLine(" [UI] Starting save process...");
                PerformBackgroundSave();
                Console.WriteLine(" [UI] Background save initiated. You can keep typing!");
                Console.ResetColor();
            } catch (Exception ex) {
                Console.WriteLine($" [UI] CAUGHT ERROR: {ex.Message}");
            }
        }

        static async void PerformBackgroundSave()
        {
            await Task.Delay(2000);
            throw new InvalidOperationException("Disk Full - Save Failed");
        }
    }
}
