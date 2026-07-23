//Scope: unscoped
let counter = 0;

async function print(msg, signal) {
  console.log(msg);
}

async function asyncInt(signal) {
  let inner = async () => {
    let me = counter++;
    let until = Math.floor(Math.random() * 50);
    for (let i = 0; i < until; i++)
      await print(`[${me}] waiting`, signal);
    await print(`[${me}] done`);
    return until;
  };
  inner();

  return 0;
}

async function main() {
  let a = asyncInt();
  let b = asyncInt();
  console.log("working");
  let c = await a + await b;
  await print(c);
}

main().then(() => console.log("exiting"))
