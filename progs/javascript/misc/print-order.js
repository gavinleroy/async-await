// function sleep(s, signal) {
//   return new Promise((resolve, reject) => {
//     if (signal?.aborted)
//       return reject(new AbortError());
//     const cleanup = () => {
//       signal?.removeEventListener("abort", onAbort);
//     };
//     const timeoutId = setTimeout(() => {
//       cleanup();
//       resolve();
//     }, s * 1000);
//     const onAbort = () => {
//       clearTimeout(timeoutId);
//       cleanup();
//       reject(new AbortError());
//     };
//     signal?.addEventListener("abort", onAbort);
//   });
// }
//
// const getTruth = async () => {
//   await sleep(2);
//   return true;
// }

const work = async (msg) => {
  console.log(msg);
}

const main = async () => {
  const p1 = work("A");

  console.log("C")
  const p2 = work("B");
  await Promise.all([p1, p2]);
};

main().catch(console.error);
