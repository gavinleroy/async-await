// Figure library — JavaScript.
//
// sleep(seconds): the lane's sleep, shared by all figure programs.
// timeout(seconds, fn): Promise.race (the paper's Fig. 2 JS version). The
// race only settles first — the losing promise is NOT cancelled (promises
// cannot be), so timed-out work keeps running to completion.

function sleep(seconds) {
  return new Promise((resolve) => setTimeout(resolve, seconds * 1000));
}

async function timeout(seconds, fn) {
  await Promise.race([fn(), sleep(seconds)]);
}

module.exports = { sleep, timeout };
