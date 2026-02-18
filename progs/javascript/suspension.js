//Suspension: static
let counter = 0;

async function cont() {
  return true;
}

async function print(msg) {
  console.log(msg);
}

async function asyncInt() {
  let me = counter++;
  let until = Math.floor(Math.random() * 50);
  for (let i = 0; i < until && await cont(); i++)
    await print(`[${me}] waiting`);
  return until;
}

async function main() {
  let a = asyncInt();
  let b = asyncInt();
  console.log("working");
  let c = await a + await b;
  await print(c);
}

main().then(() => console.log("exiting"))
