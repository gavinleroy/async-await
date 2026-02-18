import asyncio
from asyncio import Task
from types import CoroutineType

async def asyncf():
    print("async running")


async def wrapper() -> None:
    coro = asyncf()
    await asyncio.sleep(1)
    print("wrapper running")
    await coro


if __name__ == "__main__":
    asyncio.run(wrapper())
