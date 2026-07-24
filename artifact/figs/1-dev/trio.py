# Figure 1-dev — Python + Trio (decision-tree variant).
#
# Three calling contexts, one per dimension group:
#   ex1 START OF LIFE  plain async application, never awaited
#   ex2 END OF LIFE    spawn, extent ends un-awaited (no grace)
#   ex3 CANCELLATION   timeout a parent awaiting its spawned child
#
# spawn      = nursery.start_soon (dynamic extent; the nursery awaits its
#              children at scope end)
# timeout    = figlib.timeout: trio.move_on_after — a cancel scope with a
#              deadline; cancellation reaches every child structurally
#
# Predicted: ex1 `C` (lazy: the coroutine never runs), ex2 `ACB` (awaited
# destruction at DYNAMIC extent: C prints inside the nursery scope, then
# the nursery waits for B before ex2 returns), ex3 `A` (the cancel scope
# kills the child mid-sleep at 1 s).

import os
import sys

import trio

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
    async with trio.open_nursery() as nursery:
        nursery.start_soon(work, 2)
        await sleep(1)  # do other work ...
        print("C")
        # scope end: the nursery awaits the task


async def parent():
    async with trio.open_nursery() as nursery:
        nursery.start_soon(work, 2)
        # the nursery exit awaits the child


async def ex3():
    await timeout(1, parent)
    await sleep(GRACE)


async def main(f):
    await f()


f = {"1": ex1, "2": ex2, "3": ex3}[sys.argv[1]]

trio.run(main, f)
