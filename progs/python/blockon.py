import time
from typing import Awaitable


class Nap:
    def __init__(self, secs):
        self.end = time.time() + secs
    def __await__(self):
        while time.time() < self.end:
            yield
        return


def blockon(coro):
    assert isinstance(coro, Awaitable)
    i = coro.__await__()
    looped = 0
    while True:
        try: 
            next(i)
            looped += 1
        except StopIteration as e:
            print(f"blockon looped {looped} times")
            return e.value


async def doadd(x, y):
    await Nap(1)
    return x + y


def add(x, y):
    return blockon(doadd(x, y))


async def dodouble(x):
    await Nap(1)
    return add(x, x)


def double(x):
    return blockon(dodouble(x))


def main():
    n = 10
    start = time.time()
    print(f"2 * {n} = {double(n)} (took {int(time.time() - start)}s)")


if __name__ == "__main__":
    main()
