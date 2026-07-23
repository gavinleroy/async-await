//Suspension: static
async function print(msg) {
  console.log(msg);
}

async function work(name) {
  await print(name);
  await print(name);
  await print(name);
}

async function main() {
  let a = work("A");
  let b = work("B");
  await print("C")
  await a; await b
}

await main()
