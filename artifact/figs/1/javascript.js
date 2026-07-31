// Figure 1-dev — JavaScript (node, decision-tree variant).
//
// Three calling contexts, one per dimension group:
//   ex1 START OF LIFE  plain async application, never awaited
//   ex2 END OF LIFE    spawn detached, extent ends un-awaited
//   ex3 CANCELLATION   timeout a parent awaiting its spawned child
//
// spawn      = the eager async call itself (a promise starts running when
//              created)
// timeout    = figlib.timeout: Promise.race — the loser is NOT cancelled,
//              so timed-out work keeps running
//
// Predicted: ex1 `ACB` (eager: A prints synchronously inside the call;
// the await ALWAYS suspends — static suspension — so B lands after C),
// ex2 `ACB` (the event loop drains the detached promise's timer after
// main returns), ex3 `ACB` (nothing is cancelled; the race loser
// completes during the grace).

const { sleep, timeout } = require("./figlib.js");

async function writeToLog() {
  console.log("A");
  // simulate log write
  await sleep(2);
  console.log("B");
}

async function processAwait() {
  const task = writeToLog();
  await sleep(0);
  await task;
}

async function processDetached() {
  const task = writeToLog();
}

async function ex1() {
  const t = writeToLog(); // plain application: the body already ran to its first await
  console.log("C");
  await sleep(3);
}

async function ex2() {
  await processDetached();
  await sleep(1);
  console.log("C");
  // extent ends: the loop still drains the pending timer
}

async function ex3() {
  await timeout(1, processAwait);
  console.log("C");
  await sleep(3);
}

let f = { 1: ex1, 2: ex2, 3: ex3 }[process.argv[2]];
f();
