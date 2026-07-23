import trio

# async def work():
#     await trio.sleep(60)
#     print("did some work!")

async def work():
    try:
        await trio.sleep(60)
        print("did some work!")
    except trio.Cancelled:
        with trio.move_on_after(1000, shield=True):
            await trio.sleep(10)
            print("sneaky work")


async def main():
    async with trio.open_nursery() as scope:
        scope.start_soon(work)
        await trio.sleep(1)
        scope.cancel_scope.cancel()
        await trio.sleep(1)


trio.run(main)
