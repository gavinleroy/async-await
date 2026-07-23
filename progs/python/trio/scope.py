#Scope: function
import trio
from random import randint

counter = 0

async def write(msg):
    print(msg)
    await trio.sleep(0.5)

async def async_int():
    async def inner():
        global counter
        me = counter
        counter += 1
        until = randint(0, 50)
        for _ in range(until):
            await write(f"{me} waiting")
        print(f"{me} done")
        return until
    async with trio.open_nursery() as nursery:
        nursery.start_soon(inner)
    print(f"async_int done")
    return 0

async def main():
    a = async_int()
    b = async_int()
    print("working")
    c = await a + await b
    await write(c)

trio.run(main)
