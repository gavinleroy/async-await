// Figure 1-dev — JavaScript (node, decision-tree variant).
//
// Three calling contexts, one per dimension group:
//   ex1 START OF LIFE  plain async application, never awaited
//   ex2 END OF LIFE    spawn, extent ends un-awaited (no grace)
//   ex3 CANCELLATION   timeout a parent awaiting its spawned child
//
// spawn      = the eager async call itself (a promise starts running when
//              created)
// timeout    = figlib.timeout: Promise.race — the loser is NOT cancelled,
//              so timed-out work keeps running
//
// Predicted: ex1 `ACB` (eager: A prints synchronously inside the call;
// the await ALWAYS suspends — static suspension — so B lands after C),
// ex2 `ACB` (awaited destruction at INDEFINITE extent: the event loop
// drains the pending timer after main returns), ex3 `AB` (nothing is
// cancelled; the race loser completes during the grace).

const { sleep, timeout } = require("./figlib.js");

const GRACE = parseFloat(process.env.GRACE ?? "3");

async function work(d) {
  console.log("A");
  // simulate log write
  await sleep(d);
  console.log("B");
}

async function ex1() {
  const t = work(0); // plain application: the body already ran to its first await
  console.log("C");
  await sleep(GRACE);
}

async function ex2() {
  work(2); // spawn, handle dropped
  await sleep(1); // do other work ...
  console.log("C");
  // extent ends: the loop still drains the pending timer
}

async function parent() {
  const task = work(2);
  await task;
}

async function ex3() {
  await timeout(1, parent);
  await sleep(GRACE);
}

let f = { 1: ex1, 2: ex2, 3: ex3 }[process.argv[2]];
f();
