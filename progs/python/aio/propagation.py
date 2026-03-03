#Propgation: destruction
import asyncio

class Bad(Exception):
    pass

async def inner():
    raise Bad()

async def main():
    i = asyncio.create_task(inner())
    await asyncio.sleep(0)
    print("exiting")

asyncio.run(main())
# Task exception was never retrieved
# Bad
