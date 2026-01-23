class AbortError extends Error {
}
function sleep(s, signal) {
    return new Promise((resolve, reject) => {
        if (signal?.aborted)
            return reject(new AbortError());
        const cleanup = () => {
            signal?.removeEventListener("abort", onAbort);
        };
        const timeoutId = setTimeout(() => {
            cleanup();
            resolve();
        }, s * 1000);
        const onAbort = () => {
            clearTimeout(timeoutId);
            cleanup();
            reject(new AbortError());
        };
        signal?.addEventListener("abort", onAbort);
    });
}
async function work(cancel) {
    try {
        await sleep(60, cancel);
        console.log("did some work");
    }
    catch (e) {
        if (e instanceof AbortError) {
            await sleep(10);
            console.log("sneaky work");
            throw e;
        }
    }
}
async function main() {
    let cancel = new AbortController();
    let t = work(cancel.signal).catch(_ => { });
    await sleep(1);
    cancel.abort();
    await sleep(1);
}
main();
