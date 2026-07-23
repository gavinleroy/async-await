function sleep(duration: number): Promise<null> {
  let timerId: number;
  const timer = new Promise<null>((accept, _) => {    
    timerId = setTimeout(() => accept(null), duration);
  })
  return timer.finally(() => clearTimeout(timerId));  
}

// https://developer.mozilla.org/en-US/docs/Web/API/AbortSignal#implementing_an_abortable_api
function sleepCancellable(duration: number, opts?: { signal?: AbortSignal }): Promise<null> {
  let timerId: number;
  let signalHandler: () => void;
  const timer = new Promise<null>((accept, reject) => {
    signalHandler = () => reject(opts?.signal?.reason);
    opts?.signal?.addEventListener("abort", signalHandler, { once: true });
    timerId = setTimeout(() => accept(null), duration);
  })

  return timer.finally(() => {
    clearTimeout(timerId);
    opts?.signal?.removeEventListener("abort", signalHandler);
  });
}

function withTimeout<T>(
  duration: number,
  f: () => Promise<T>
): Promise<T | null> {
  return Promise.race([sleep(duration), f()]);
}

async function withTimeoutCancellable<T>(  
  duration: number,
  controller: AbortController,
  f: (signal: AbortSignal) => Promise<T>,    
): Promise<T | null> {
  const result = await Promise.race([
    sleepCancellable(duration, { signal: controller.signal }), 
    f(controller.signal)
  ]);
  if (result === null) controller.abort();  
  return result;
}

async function main() {
  const controller = new AbortController();
  try {
    console.log("Starting");
    const promise =  withTimeoutCancellable(1000, controller, async (signal) => {
      await sleepCancellable(1500, { signal });
      console.log("Reached end of sleep");
    })
    controller.abort();
    await promise;
  } catch (e: any) {
    console.log("Reached error");
  }
  console.log("Ending");
}

main()
