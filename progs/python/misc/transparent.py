import asyncio

async def append_it():
    print("A", end='')

async def transparent():
    ret = append_it()
    print("B", end='')
    return ret

asyncio.run(transparent())
