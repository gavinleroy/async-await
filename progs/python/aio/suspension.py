#Suspension: dynamic
import asyncio
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

async def main():
    a = asyncio.create_task(async_int())
    b = asyncio.create_task(async_int())
    print("working")
    c = await a + await b
    await write(c)

asyncio.run(main())
