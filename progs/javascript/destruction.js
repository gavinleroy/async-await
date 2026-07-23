async function inner() {
    await new Promise(r => setTimeout(r, 10_000))
    console.log("done")
}

async function work() {
    let a = inner()
    await new Promise(r => setTimeout(r, 0))
    console.log("exiting")
}

await work()
