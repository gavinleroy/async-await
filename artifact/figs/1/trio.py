# Figure 1 — Python + Trio (timeout variant).
#
# spawn      = nursery.start_soon (trio has no unstructured spawn; the
#              nursery awaits its children at scope end, so process_detach
#              cannot actually detach)
# timeout    = figlib.timeout: trio.move_on_after — a cancel scope with a
#              deadline; cancellation reaches every child structurally
# isolation  = each ex under its own trio.run; each ex ends with a 3 s
#              grace sleep (no-op for trio: children settle at scope end).
#
# Predicted: ex1 `AB` (the "detached" task is awaited by its nursery),
# ex2 `A` (scope cancelled at 0.1 s, mid-sleep), ex3 `A` (process_detach's
# nursery holds the child inside the cancelled scope).

import trio
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
    async with trio.open_nursery() as nursery:
        nursery.start_soon(write_to_log)
        await sleep(0)  # do other work ...
        # (the nursery awaits the task at scope end)


async def process_detach():
    async with trio.open_nursery() as nursery:
        nursery.start_soon(write_to_log)
        await sleep(0)  # do other work ... — but trio cannot detach: the
        # nursery still awaits the task at scope end


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
trio.run(main, f)
