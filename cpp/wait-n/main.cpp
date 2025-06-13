#include <iostream>
#include <vector>
#include <numeric>
#include <chrono>
#include <coro/coro.hpp>
#include <iterator>

template<
  std::ranges::range R,
  coro::concepts::awaitable A = std::ranges::range_value_t<R>,
  typename T = typename coro::concepts::awaitable_traits<A>::awaiter_return_type
>
[[nodiscard]] auto waitN(R futures)
    -> coro::task<std::vector<T>> {
    auto results = co_await coro::when_all(std::move(futures));

    std::vector<T> res{};
    for (auto& r : results)
        res.push_back(r.return_value());
    co_return res;
}

coro::task<int> ready(int n) {
    co_return n;
}

int main() {
    auto timer = std::chrono::high_resolution_clock::now();

    std::vector<coro::task<int>> futs;
    for (int i = 0; i <= 1000; ++i)
        futs.push_back(ready(i));

    auto ns = coro::sync_wait(waitN<
        std::vector<coro::task<int>>,
        coro::task<int>,
        int 
    >(std::move(futs)));
    size_t res = std::accumulate(ns.begin(), ns.end(), 0);
    assert(res == 500500);
    auto elapsed = std::chrono::high_resolution_clock::now() - timer;
    std::cout << "done " << std::chrono::duration_cast<std::chrono::microseconds>(elapsed).count() << "μs" << std::endl;

    return 0;
}
