import asyncio

async def inner_work(name = 0):
    try:
        await asyncio.sleep(10)
    except asyncio.CancelledError:
        print(f"{name} inner work cancelled")
    finally:
        print(f"{name} inner work exiting")

async def work():
    a = asyncio.create_task(inner_work(name = 0))
    b = asyncio.create_task(inner_work(name = 1))
    try:
        await a
        await b
    except asyncio.CancelledError:
        print("work cancelled")
        raise asyncio.CancelledError
    finally:
        print("work exiting")

async def main():
    running = asyncio.create_task(work())
    await asyncio.sleep(3)
    running.cancel()
    try:
        await running
    except asyncio.CancelledError:
        print("main cancelled")
    finally:
        print("main exiting")

asyncio.run(main())
