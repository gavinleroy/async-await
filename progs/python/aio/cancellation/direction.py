import asyncio

async def inner_work(name = 0):
    try:
        await asyncio.sleep(10)
    except asyncio.CancelledError:
        print(f"{name} inner work cancelled")
    finally:
        print(f"{name} inner work exiting")

async def work():
    try:
        await inner_work(name = 0)
        await inner_work(name = 1)
    except asyncio.CancelledError:
        print("work cancelled")
        raise asyncio.CancelledError
    finally:
        print("work exiting")

async def work_concurrently():
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

async def work_together():
    try:
        await asyncio.gather(inner_work(name = 0), inner_work(name = 1))
    except asyncio.CancelledError:
        print("work cancelled")
        raise asyncio.CancelledError
    finally:
        print("work exiting")

async def work_group():
    try:
        async with asyncio.TaskGroup() as tg:
            a = tg.create_task(inner_work(name = 0))
            b = tg.create_task(inner_work(name = 1))
    except asyncio.CancelledError:
        print("work cancelled")
        raise asyncio.CancelledError
    finally:
        print("work exiting")

async def main(coro):
    running = asyncio.create_task(coro())
    await asyncio.sleep(3)
    running.cancel()
    try:
        await running
    except asyncio.CancelledError:
        print("main cancelled")
    finally:
        print("main exiting")

async def runner():
    d = {
        "work": work,
        "concurrently": work_concurrently,
        "together": work_together,
        "group": work_group
    }
    for k, v in d.items():
        print(f"== running  {k} ==")
        await main(v)
        print("")

asyncio.run(runner())
