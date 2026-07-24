// Figure 5 (Suspension): JS awaits are STATIC — an await always yields to
// the microtask queue, even when the awaited promise is already settled
// (ECMA-262 §27.7.5.3).
// Expected output: A B C A B (deterministic).

async function work(msg) {
  console.log(msg);
}

async function repeat(msg) {
  await work(msg);
  await work(msg);
}

async function main() {
  const a = repeat("A"); // spawn: the eager call starts the task
  const b = repeat("B");
  console.log("C");
  await a;
  await b;
}

main();
