async function main() {
    console.log("Starting the stack dive...");
    await recursiveSpiral();
}

async function recursiveSpiral() {
    for (let i = 0; i < 1_000_000; i++) {
        if (i % 1000 === 0) console.log(`Depth: ${i}`);
        // In JS, we 'await' an object with a 'then' method
        await new Awaitable();
    }
}

// NOTE: unlike C#, this is not an issue because the
// continuation gets placed on the microtask queue.
class Awaitable {
    then(resolve) {
        resolve();
    }
}

main().catch(err => console.error(err));
