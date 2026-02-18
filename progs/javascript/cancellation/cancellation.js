//Cancellaton: none
class AbortError extends Error {}

function sleep(s, signal) {
    return new Promise((resolve, reject) => {
        if (signal?.aborted)
            return reject(new AbortError());
        const cleanup = () => {
            signal?.removeEventListener("abort", onAbort);
        };
        const timeoutId = setTimeout(() => {
            cleanup();
            resolve();
        }, s * 1000);
        const onAbort = () => {
            clearTimeout(timeoutId);
            cleanup();
            reject(new AbortError());
        };
        signal?.addEventListener("abort", onAbort);
    });
}

let counter = 0;

async function print(msg, signal) {
  console.log(msg);
  await sleep(1, signal)
}

async function asyncInt(signal) {
  let me = counter++;
  let until = Math.floor(Math.random() * 50);
  for (let i = 0; i < until; i++)
    await print(`[${me}] waiting`, signal);
  return until;
}

async function main() {
  let controller = new AbortController();
  let signal = controller.signal;

  let a = asyncInt(signal);
  let b = asyncInt(signal);
  console.log("working");

  // NOTE, unlike the C# program, this program will exit on error
  // because the signal is passed down to the sleep function
  await sleep(3);
  controller.abort();
  let c = await a + await b;
  await print(c);
}

main().then(() => console.log("exiting"))
