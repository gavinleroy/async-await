import asyncio
import gc

# Original implementation
# async def work():
#     await asyncio.sleep(60)
#     print("did some work!")

# With Events
# async def work(event: asyncio.Event):
#     try:
#         event.set()
#         await asyncio.sleep(60)
#     finally:
#         await asyncio.sleep(5)
#         print("doing more work!")


# Sneaky Work
# async def work():
#     try:
#         await asyncio.sleep(60)
#         print("did some work!")
#     except asyncio.CancelledError:
#         await asyncio.sleep(10)
#         print("sneaky work done")


# Improperly Shielded Work
# async def work():
#     async def inner():
#         await asyncio.sleep(60)
#         print("did some work!")
#     await asyncio.shield(inner())


# Shielded Work
async def work():
    async def inner():
        await asyncio.sleep(60)
        print("did some work!")
    s = asyncio.create_task(inner())
    try:
        await asyncio.shield(s)
    except asyncio.CancelledError:
        await asyncio.shield(s)


async def main():
    task = asyncio.create_task(work())
    await asyncio.sleep(1)
    task.cancel()
    await asyncio.sleep(1)
    await task
    print("exiting")


asyncio.run(main())
