#Exception: reraise
import trio
from random import randint

counter = 0

async def write(msg):
    print(msg)

async def async_int():
    async def inner():
        raise Exception("argh")
    async with trio.open_nursery() as nursery:
        nursery.start_soon(inner)
    return 0

async def main():
    a = async_int()
    b = async_int()
    print("working")
    c = await a + await b
    await write(c)

trio.run(main)
