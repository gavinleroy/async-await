// Figure 1 — JavaScript (node, timeout variant).
//
// spawn      = the eager async call itself (a promise starts running when
//              created)
// timeout    = figlib.timeout: Promise.race — the loser is NOT cancelled,
//              so timed-out work keeps running
// isolation  = each ex ends with a 3 s grace sleep, so a race loser's late
//              prints land in their own ex's section (they cannot be
//              stopped — that is the JS story).
//
// Predicted: ex1 `AB`, ex2 `AB` (the race times out at 0.1 s but the loser
// still prints B at 0.2 s), ex3 `AB` (same).

const { sleep, timeout } = require("./figlib.js");

const GRACE = parseFloat(process.env.GRACE ?? "3");

async function write_to_log() {
  console.log("A");
  // simulate log write
  await sleep(2);
  console.log("B");
}

async function process_await() {
  const task = write_to_log(); // spawn: the eager call starts the task
  await sleep(0); // do other work ...
  await task;
}

async function process_detach() {
  write_to_log(); // spawn, handle dropped
  await sleep(0); // do other work ...
}

async function ex1() {
  await process_detach();
}

async function ex2() {
  await timeout(1, process_await);
}

async function ex3() {
  await timeout(1, process_detach);
}

async function main(f) {
  await f()
  await sleep(GRACE)
}

let f = ({ 1: ex1, 2: ex2, 3: ex3 })[process.argv[2]];
main(f);
