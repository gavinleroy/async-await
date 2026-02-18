const id = async (n) => {
  return n;
};

const forever = async (signal) => {
  while (signal.aborted === false) {
    await new Promise(resolve => setTimeout(resolve, 50));
  }
  return;
};

const raceN = async (futs, controller) => {
  const res = await Promise.any(futs);
  // Must abort, otherwise program doesn't terminate
  controller.abort();
  return res;
};

const main = async () => {
  const abort = new AbortController();
  const n = 42;
  const timer = process.hrtime.bigint();
  const futs = Array.from({ length: 1001 }, (_, i) => (i === n ? id(i) : forever(abort.signal)));
  const res = await raceN(futs, abort);
  console.assert(res === n, `Result ${res} does not match expected value`);
  const elapsed = Number(process.hrtime.bigint() - timer) / 1000;
  console.log(`done ${elapsed}μs`);
};

main().catch(console.error);
