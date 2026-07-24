# Figure 1-dev — Python + asyncio (decision-tree variant).
#
# Three calling contexts, one per dimension group:
#   ex1 START OF LIFE  plain async application, never awaited
#   ex2 END OF LIFE    spawn, extent ends un-awaited (no grace)
#   ex3 CANCELLATION   timeout a parent awaiting its spawned child
#
# spawn      = asyncio.create_task (indefinite extent)
# timeout    = figlib.timeout: asyncio.wait_for — cancels the timed-out
#              task; propagates down the await chain (_fut_waiter)
#
# Predicted: ex1 `C` (lazy: the coroutine never runs), ex2 `AC` (the
# spawned task runs — the ready-queue reference is strong — and is
# cancelled mid-sleep when asyncio.run shuts the loop down), ex3 `A`
# (cancelling the parent propagates into the awaited child; both die at
# 1 s).

import asyncio
import os
import sys

GRACE = float(os.environ.get("GRACE", "3"))

from figlib import sleep, timeout


async def work(d):
    print("A")
    # simulate log write
    await sleep(d)
    print("B")


async def ex1():
    t = work(0)  # plain application: a coroutine, never awaited
    print("C")
    await sleep(GRACE)


async def ex2():
    task = asyncio.create_task(work(2))
    await sleep(1)  # do other work ...
    print("C")
    # extent ends: the loop shuts down with the task still sleeping


async def parent():
    task = asyncio.create_task(work(2))
    await task


async def ex3():
    await timeout(1, parent)
    await sleep(GRACE)


f = {"1": ex1, "2": ex2, "3": ex3}[sys.argv[1]]

asyncio.run(f())
