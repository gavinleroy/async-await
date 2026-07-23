import asyncio
import time

async def id(n):
    return n

async def wait_n(futs):
    return await asyncio.gather(*futs)

async def main():
    timer = time.perf_counter()
    futs = (id(i) for i in range(1001))
    ns = await wait_n(futs)
    res = sum(ns)
    assert res == 500500
    print(f"done {int((time.perf_counter() - timer) * 1_000_000)}μs")

if __name__ == "__main__":
    asyncio.run(main())
