//Exception: reraise
let counter = 0;

async function print(msg, signal) {
  console.log(msg);
}

async function asyncInt(signal) {
  let inner = async () => {
    throw new Error("argh");
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
