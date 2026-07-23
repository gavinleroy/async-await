import asyncio

async def bad():
    # await asyncio.sleep(5)
    raise ValueError("failed")

async def main():
    t = asyncio.create_task(bad())
    await asyncio.sleep(1)
    print("exiting")

asyncio.run(main())
