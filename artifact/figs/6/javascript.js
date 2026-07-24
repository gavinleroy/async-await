// Figure 6 (Extent): JS extent is INDEFINITE — the unawaited task keeps
// running after main() returns, and node's event loop keeps the process
// alive until its timer fires.
// Expected output: A then (after ~1 s) B.

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function work() {
  await sleep(1000);
  console.log("B");
}

async function main() {
  work(); // spawn: eager call, handle dropped
  console.log("A");
}

main();
