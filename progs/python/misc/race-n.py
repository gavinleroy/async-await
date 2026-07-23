import asyncio
import time

async def id(n):
    return n

async def forever():
    while True:
        await asyncio.sleep(0)

async def race_n(futs):
    # NOTE, no cancellation but the program will terminate
    for fut in asyncio.as_completed(futs):
        result = await fut
        if result is not None:
            return result
    return None

async def main():
    n = 42
    timer = time.perf_counter()
    futs = (id(i) if i == n else forever() for i in range(1001))
    res = await race_n(futs)
    assert res == n
    print(f"done {int((time.perf_counter() - timer) * 1_000_000)}μs")

if __name__ == "__main__":
    asyncio.run(main())
