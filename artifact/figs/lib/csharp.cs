// Figure library — C#.
//
// Sleep(seconds): the lane's sleep, shared by all figure programs.
// Timeout(seconds, fn): Task.WhenAny against a delay. The race only
// settles first — the losing task is NOT cancelled (a bare Task handle has
// no cancel; CancellationTokens are cooperative plumbing the pseudocode
// does not thread), so timed-out work keeps running.

using System;
using System.Threading.Tasks;

static class Figlib
{
    public static Task Sleep(double seconds)
    {
        return Task.Delay(TimeSpan.FromSeconds(seconds));
    }

    public static async Task Timeout(double seconds, Func<Task> fn)
    {
        await Task.WhenAny(fn(), Sleep(seconds));
    }
}
