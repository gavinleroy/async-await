#include <iostream>
#include <fstream>
#include <vector>
#include <numeric>
#include <chrono>
#include <coro/coro.hpp>
#include <iterator>

std::shared_ptr<coro::io_scheduler> scheduler = coro::io_scheduler::make_shared();

template<class rep_type, class period_type>
[[nodiscard]] auto sleep(std::chrono::duration<rep_type, period_type> amount) -> coro::task<> {
  co_await scheduler->schedule_after(amount);
  co_return;
}

coro::task<> asyncf() {
  std::cout << "async running" << std::endl;
  co_return;
}

coro::task<> wrapper() {
  auto coro = asyncf();
  co_await sleep(std::chrono::seconds(1));
  std::cout << "wrapper running" << std::endl;
  co_await coro;
}

int main() {
    coro::sync_wait(wrapper());
    return 0;
}
