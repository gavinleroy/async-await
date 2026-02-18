#Eagerness: Lazy
import asyncio
from random import randint

counter = 0

async def write(msg):
    print(msg)

async def async_int():
    global counter
    me = counter
    counter += 1
    until = randint(0, 50)
    for _ in range(until):
        await write(f"{me} waiting")
    return until

async def main():
    a = async_int()
    b = async_int()
    print("working")
    c = await a + await b
    await write(c)

asyncio.run(main())
