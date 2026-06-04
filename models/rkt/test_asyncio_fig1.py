import asyncio

async def write_to_log():
    print("A", end="")
    await asyncio.sleep(2)
    print("B", end="")

async def process_ignore():
    _task = asyncio.create_task(write_to_log())
    await asyncio.sleep(0)

async def process_await():
    task = asyncio.create_task(write_to_log())
    await task

async def ex1():
    await process_ignore()

async def ex2():
    task = asyncio.create_task(process_await())
    task.cancel()

async def ex3():
    task = asyncio.create_task(process_ignore())
    await asyncio.sleep(1)
    task.cancel()

# async def main():
#     await ex1()
#     await asyncio.sleep(3)
#     print("")
#     await ex2()
#     await asyncio.sleep(3)
#     print("")
#     await ex3()
#     await asyncio.sleep(3)
#     print("")
# asyncio.run(main())

asyncio.run(ex1())
print("")
asyncio.run(ex2())
print("")
asyncio.run(ex3())
print("")
