# Figure 1-dev — Python + asyncio (decision-tree variant).
#
# Three calling contexts, one per dimension group:
#   ex1 START OF LIFE  plain async application, never awaited
#   ex2 END OF LIFE    spawn detached, extent ends un-awaited
#   ex3 CANCELLATION   timeout a parent awaiting its spawned child
#
# spawn      = asyncio.create_task (indefinite extent)
# timeout    = figlib.timeout: asyncio.wait_for — cancels the timed-out
#              task; propagates down the await chain (_fut_waiter)
#
# Predicted: ex1 `C` (lazy: the coroutine never runs), ex2 `AC` (the
# detached task runs — the loop holds it, not the dropped handle — and is
# cancelled mid-sleep when asyncio.run shuts the loop down), ex3 `AC`
# (at 1 s the parent is awaiting its child, so the cancellation
# propagates into it; both die).

import asyncio
import sys

from figlib import sleep, timeout


async def write_to_log():
    print("A")
    # simulate log write
    await sleep(2)
    print("B")


async def process_await():
    task = asyncio.create_task(write_to_log())
    await sleep(0)
    await task


async def process_detached():
    task = asyncio.create_task(write_to_log())


async def ex1():
    t = write_to_log()  # plain application: a coroutine, never awaited
    print("C")
    await sleep(3)


async def ex2():
    await process_detached()
    await sleep(1)
    print("C")
    # extent ends: the loop shuts down with the task still sleeping


async def ex3():
    await timeout(1, process_await)
    print("C")
    await sleep(3)


f = {"1": ex1, "2": ex2, "3": ex3}[sys.argv[1]]

asyncio.run(f())
