# Figure library — asyncio.
#
# sleep(seconds): the lane's sleep, shared by all figure programs.
# timeout(seconds, fn): run fn() with a time limit. asyncio.wait_for wraps
# the coroutine in a task and CANCELS it on expiry; the cancellation is
# delivered as a CancelledError and, if the task is itself awaiting a task,
# propagates down into the awaited future (_fut_waiter).

import asyncio


async def sleep(seconds):
    await asyncio.sleep(seconds)


async def timeout(seconds, fn):
    try:
        await asyncio.wait_for(fn(), seconds)
    except TimeoutError:
        pass
