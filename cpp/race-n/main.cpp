#include <iostream>
#include <vector>
#include <numeric>
#include <chrono>
#include <coro/coro.hpp>
#include <iterator>

template<typename T>
coro::task<T> ready(T n) {
  co_return n;
}

// NOTE: I'm not fully sure why this needs to 
// use a scheduler. Without, the `raceN` implementation
// wouldn't return. I suspect it had to do with scheduling,
// i.e., because the yield was immediately available the 
// futures would get rescheduled. This is also a peculiarity 
// in Python.
template<typename T>
auto forever(std::shared_ptr<coro::io_scheduler> scheduler) 
  -> coro::task<T> {
  auto millis = std::chrono::milliseconds{50};
  while (true)
    co_await scheduler->schedule_after(millis);
}

template<
std::ranges::range R,
  coro::concepts::awaitable A = std::ranges::range_value_t<R>,
  typename T = typename coro::concepts::awaitable_traits<A>::awaiter_return_type
  >
[[nodiscard]] auto raceN(R futures)
  -> coro::task<std::optional<T>> {
  if (futures.empty())
    co_return std::nullopt;

  auto result = co_await coro::when_any(std::move(futures));
  co_return std::optional(result);
}

int main() {
  auto scheduler = coro::io_scheduler::make_shared();
  auto timer = std::chrono::high_resolution_clock::now();
  auto n = 42;

  std::vector<coro::task<int>> futs;
  for (int i = 0; i <= 1000; ++i)
    futs.push_back(i == n ? ready(i) : forever<int>(scheduler));

  auto res = coro::sync_wait(raceN
    <
      std::vector<coro::task<int>>,
      coro::task<int>,
      int
    >
    (std::move(futs)));

  assert(res == std::optional(n));
  auto elapsed = std::chrono::high_resolution_clock::now() - timer;
  std::cout << "done " << std::chrono::duration_cast<std::chrono::microseconds>(elapsed).count() << "μs" << std::endl;

  return 0;
}
