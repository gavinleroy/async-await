async function getTrue() {
  throw true;
}

async function work(msg) {
  console.log(msg);
  for (let i = 0; i < 10; i++) {
    if (await getTrue())
      console.log(msg);
  }
}

async function main() {
  console.log("running");
  let p1 = work("A");
  let p2 = work("B");
  console.log("C");
  await Promise.all([p1, p2]);
}

await main()
