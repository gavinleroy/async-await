// HaltedError class
class HaltedError extends Error {
  constructor() {
    super('Operation halted');
    this.name = 'HaltedError';
  }
}

// HaltSignal class (similar to Rust's Arc<AtomicBool>)
class HaltSignal {
  constructor() {
    this.halted = false;
  }

  halt() {
    this.halted = true;
  }

  isHalted() {
    return this.halted;
  }

  reset() {
    this.halted = false;
  }
}

function sleep(ms, signal) {
  return new Promise((resolve, reject) => {
    const timeoutId = setTimeout(resolve, ms);

    const abortHandler = () => {
      clearTimeout(timeoutId);
      reject(new Error('Sleep operation cancelled'));
    };

    signal?.addEventListener('abort', abortHandler);
  });
}

async function runWithPeriodicHaltCheck(workPromise, haltSignal, checkIntervalMs) {
  const controller = new AbortController();
  const signal = controller.signal;

  const periodicCheck = async () => {
    while (!signal.aborted) {
      await sleep(checkIntervalMs);
      if (haltSignal.isHalted()) {
        controller.abort();
        throw new HaltedError();
      }
    }
  };

  try {
    return await Promise.race([
      workPromise(signal),
      periodicCheck()
    ]);
  } finally {
    controller.abort();
  }
}

// Async task function (equivalent to my_async_task)
async function myAsyncTask(signal) {
  console.log("Task: Starting work...");
  await sleep(1000, signal);
  await sleep(1000, signal);
  await sleep(1000, signal);
  console.log("Task: Finished work.");
  return "Task Completed Successfully";
}

// Main execution function
async function main() {
  // Scenario 1: Running task, expecting completion
  console.log("Scenario 1: Running task, expecting completion.");
  const haltSignal1 = new HaltSignal();
  const checkInterval = 500; // 500ms

  try {
    const result1 = await runWithPeriodicHaltCheck(
      myAsyncTask,
      haltSignal1,
      checkInterval
    );
    console.log(`Scenario 1 Result: ${result1}`);
  } catch (error) {
    console.log(`Scenario 1 Error: ${error.message}`);
  }
  console.log("--------------------");

  // Scenario 2: Running task, expecting halt
  console.log("Scenario 2: Running task, expecting halt.");
  const haltSignal2 = new HaltSignal();

  // Start the task with halt checking
  const scenario2Promise = (async () => {
    try {
      const result2 = await runWithPeriodicHaltCheck(
        myAsyncTask,
        haltSignal2,
        checkInterval
      );
      console.log(`Scenario 2 Result: ${result2}`);
    } catch (error) {
      console.log(`Scenario 2 Error: ${error.message}`);
    }
  })();

  // Schedule halt signal after 7 seconds
  setTimeout(() => {
    console.log("Scenario 2: Setting halt signal!");
    haltSignal2.halt();
  }, 1000);

  await scenario2Promise;
  console.log("--------------------");
}

// Run the main function
main().catch(error => {
  console.error("Unhandled error:", error);
});
