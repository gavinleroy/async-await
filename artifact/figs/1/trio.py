# Figure 1-dev — Python + Trio (decision-tree variant).
#
# Three calling contexts, one per dimension group:
#   ex1 START OF LIFE  plain async application, never awaited
#   ex2 END OF LIFE    spawn detached, extent ends un-awaited
#   ex3 CANCELLATION   timeout a parent awaiting its spawned child
#
# spawn      = nursery.start_soon (dynamic extent; the nursery awaits its
#              children at scope end — a task CANNOT detach)
# timeout    = figlib.timeout: trio.move_on_after — a cancel scope with a
#              deadline; cancellation reaches every child structurally
#
# Predicted: ex1 `C` (lazy: the coroutine never runs), ex2 `ABC` (the
# nursery refuses to detach: process_detached returns only after B, then
# C prints), ex3 `AC` (the cancel scope kills the child mid-sleep at
# 1 s).

import sys

import trio

from figlib import sleep, timeout


async def write_to_log():
    print("A")
    # simulate log write
    await sleep(2)
    print("B")


async def process_await():
    async with trio.open_nursery() as nursery:
        nursery.start_soon(write_to_log)
        await sleep(0)
        # the nursery exit awaits the child


async def process_detached():
    async with trio.open_nursery() as nursery:
        nursery.start_soon(write_to_log)
        # the nursery exit awaits the child


async def ex1():
    t = write_to_log()  # plain application: a coroutine, never awaited
    print("C")
    await sleep(3)


async def ex2():
    await process_detached()
    await sleep(1)
    print("C")


async def ex3():
    await timeout(1, process_await)
    print("C")
    await sleep(3)


async def main(f):
    await f()


f = {"1": ex1, "2": ex2, "3": ex3}[sys.argv[1]]

trio.run(main, f)
