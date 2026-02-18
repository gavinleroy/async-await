class PleaseStop(Exception):
    def __init__(self, message="Stop requested, politely"):
        self.message = message
        super().__init__(self.message)


async def suspend():
    class _ImmediateAwaitable:
        def __await__(self):
            yield 
            return None
    await _ImmediateAwaitable()


async def work():
    try:
        await suspend()
        print("done")
    except PleaseStop:
        print("ok, because you asked nicely")


c = work()
c.send(None)
c.throw(PleaseStop())
