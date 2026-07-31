# Figure 7 (Destruction): Trio destruction is AWAITED — a spawned task is
# tied to a nursery, and the nursery waits at the end of its scope for
# every child to complete.
# Expected output: A then B (deterministic).

import trio


async def work():
    await trio.sleep(2)
    print("A", flush=True)
    await trio.sleep(2)
    print("B", flush=True)


async def short_lived():
    async with trio.open_nursery() as nursery:
        nursery.start_soon(work)  # spawn; the nursery awaits it at scope end


async def main():
    await short_lived()
    await trio.sleep(3)


trio.run(main)
