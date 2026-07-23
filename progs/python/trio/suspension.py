#Suspension: dynamic
import trio
from random import randint

counter = 0

async def cont():
    return True

async def write(msg):
    print(msg)

async def async_int():
    global counter
    me = counter
    counter += 1
    until = randint(0, 50)
    for _ in range(until):
        if not await cont():
            break
        await write(f"{me} waiting")
    return until

async def gather(*async_funcs):
    results = [None] * len(async_funcs)
    async def runner(func, index):
        results[index] = await func()
    async with trio.open_nursery() as nursery:
        for i, func in enumerate(async_funcs):
            nursery.start_soon(runner, func, i)
        await write("working")
    return results

# NOTE, there's no interleaving because there isn't a suspension
async def main():
    [a, b] = await gather(async_int, async_int)
    c = a + b
    await write(c)

trio.run(main)
