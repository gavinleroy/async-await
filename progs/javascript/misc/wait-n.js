const id = async (n) => {
  return n;
};

const waitN = async (futs) => {
  return await Promise.all(futs);
};

const main = async () => {
  const timer = process.hrtime.bigint();
  const futs = Array.from({ length: 1001 }, (_, i) => id(i));
  const ns = await waitN(futs);
  const res = ns.reduce((acc, val) => acc + val, 0);
  console.assert(res === 500500, 'Result does not match expected value');
  const elapsed = Number(process.hrtime.bigint() - timer) / 1000;
  console.log(`done ${elapsed}μs`);
};

main().catch(console.error);
