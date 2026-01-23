#include <iostream>
#include <coro/coro.hpp>

std::once_flag seedit;

template<class T>
using bum = coro::task<T>;

auto s_random() -> uint64_t {
  std::call_once(seedit, [](){ srand(static_cast<unsigned int>(time(0))); });
  return rand();
}

[[nodiscard]] auto randoma() -> bum<uint64_t> {
  std::call_once(seedit, [](){ srand(static_cast<unsigned int>(time(0))); });
  co_return rand();
}

auto client() -> bum<void> {
  auto n = co_await randoma();
  std::cout << "Number: " << n << std::endl;
}

int main() {
    coro::sync_wait(client());
    return 0;
}
