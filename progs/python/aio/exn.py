#Exception: reraise
import asyncio
from random import randint

counter = 0
background = []

async def write(msg):
    print(msg)

async def async_int():
    global background
    async def inner():
        raise Exception("argh")
    background.append(asyncio.create_task(inner()))
    return 0

async def main():
    a = async_int()
    b = async_int()
    print("working")
    c = await a + await b
    await write(c)

asyncio.run(main())
