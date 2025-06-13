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

template<typename T>
coro::task<T> forever() {
    auto nothing = []() -> coro::task<> { co_return; };
    while (true) co_await nothing(); 
}

// FIXME: this fucntion is wrong, when passed forever coroutines it never returns.
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
    co_return std::optional(std::move(result));
}

int main() {
    auto timer = std::chrono::high_resolution_clock::now();
    auto n = 42;

    std::vector<coro::task<int>> futs;
    for (int i = 0; i <= 1000; ++i)
      futs.push_back(i == n ? ready(i) : forever<int>());

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
