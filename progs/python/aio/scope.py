#Scope: program
import asyncio
from random import randint

counter = 0
background = []

async def write(msg):
    print(msg)
    await asyncio.sleep(0.5)

async def async_int():
    global background
    async def inner():
        global counter
        me = counter
        counter += 1
        until = randint(0, 50)
        for _ in range(until):
            await write(f"{me} waiting")
        print(f"{me} done")
        return until
    background.append(asyncio.create_task(inner()))
    return 0

async def main():
    a = async_int()
    b = async_int()
    print("working")
    c = await a + await b
    await write(c)

asyncio.run(main())
