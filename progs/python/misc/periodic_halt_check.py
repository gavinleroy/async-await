import asyncio
import threading
from dataclasses import dataclass
from typing import TypeVar, Generic, Callable, Awaitable, cast


@dataclass
class HaltedError(Exception):
    def __str__(self) -> str:
        return "Operation halted"


T = TypeVar('T')

async def run_with_periodic_halt_check(
    work: Callable[[], Awaitable[T]],
    halt_signal: threading.Event,
    check_interval: float
) -> T:
    work_task = asyncio.create_task(work())
    while True:
        done, pending = await asyncio.wait([work_task], timeout=check_interval)
        if work_task in done:
            return done.pop().result()
        elif halt_signal.is_set():
            try:
                work_task.cancel()
                await work_task
            finally:
                raise HaltedError()


async def my_async_task() -> str:
    print("Task: Starting work...")
    await asyncio.sleep(1)
    await asyncio.sleep(1)
    await asyncio.sleep(1)
    print("Task: Finished work.")
    return "Task Completed Successfully"


async def main():
    """Run the example scenarios."""
    halt_signal = threading.Event()
    check_interval = 0.5  # 500ms
    
    print("Scenario 1: Running task, expecting completion.")
    try:
        result = await run_with_periodic_halt_check(
            my_async_task,
            halt_signal,
            check_interval
        )
        print(f"Scenario 1 Result: {result}")
    except HaltedError as e:
        print(f"Scenario 1 Error: {e}")
    
    print("--------------------")
    
    print("Scenario 2: Running task, expecting halt.")
    # Reset the halt signal
    halt_signal.clear()
    
    # Create a task to set the halt signal after 7 seconds
    async def set_halt_signal():
        await asyncio.sleep(1)
        print("Scenario 2: Setting halt signal!")
        halt_signal.set()
    
    # Start the task to set the halt signal
    asyncio.create_task(set_halt_signal())
    
    try:
        result = await run_with_periodic_halt_check(
            my_async_task,
            halt_signal,
            check_interval
        )
        print(f"Scenario 2 Result: {result}")
    except HaltedError as e:
        print(f"Scenario 2 Error: {e}")
    
    print("--------------------")
    await asyncio.sleep(2)


if __name__ == "__main__":
    asyncio.run(main())
