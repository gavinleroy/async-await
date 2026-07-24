# Figure 1 — Python + asyncio (timeout variant).
#
# spawn      = asyncio.create_task (indefinite extent)
# timeout    = figlib.timeout: asyncio.wait_for — cancels the timed-out
#              task; the cancellation propagates down into whatever future
#              it is awaiting (_fut_waiter)
# isolation  = ONE ex per process: the harness passes the ex number as
#              argv[1] and runs each in a fresh process. Each ex ends with
#              a 3 s grace sleep, so the loop outlives detached work.
#
# Predicted: ex1 `AB` (the grace keeps the loop alive past the detached
# task's sleep), ex2 `A` (wait_for cancels down the await chain at 0.1 s),
# ex3 `AB` (process_detach finishes under the deadline; the detached task
# completes during the grace).

import asyncio
import os
import sys

GRACE = float(os.environ.get("GRACE", "3"))

from figlib import sleep, timeout


async def write_to_log():
    print("A")
    # simulate log write
    await sleep(2)
    print("B")


async def process_await():
    task = asyncio.create_task(write_to_log())
    await sleep(0)  # do other work ...
    await task


async def process_detach():
    task = asyncio.create_task(write_to_log())
    await sleep(0)  # do other work ...


async def ex1():
    await process_detach()


async def ex2():
    await timeout(1, process_await)


async def ex3():
    await timeout(1, process_detach)


async def main(f):
    await f()
    await sleep(GRACE)


f = {"1": ex1, "2": ex2, "3": ex3}[sys.argv[1]]

asyncio.run(main(f))
