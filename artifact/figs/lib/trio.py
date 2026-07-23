# Figure library — Trio.
#
# sleep(seconds): the lane's sleep, shared by all figure programs.
# timeout(seconds, fn): run fn() inside a cancel scope with a deadline
# (trio.move_on_after — the paper's Fig. 2 Trio version). On expiry the
# scope is cancelled; cancellation reaches every child nursery/task inside
# fn structurally.

import trio


async def sleep(seconds):
    await trio.sleep(seconds)


async def timeout(seconds, fn):
    with trio.move_on_after(seconds):
        await fn()
