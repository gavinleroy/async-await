#include <iostream>
#include <fstream>
#include <vector>
#include <numeric>
#include <chrono>
#include <coro/coro.hpp>
#include <iterator>

// To mimick how we do it in Rust
// coro::task<std::string> read_to_string(std::string file) { 
// }

coro::generator<char> bytesOf(std::string file) {
  std::ifstream fin(file);
  char byte;
  while (fin.get(byte))
    co_yield byte;
  fin.close();
  co_return;
}

coro::task<uint64_t> lines(std::string file) {
  uint64_t ls = 0;
  for (char byte : bytesOf(file))
    if (byte == '\n')
      ++ls;
  co_return ls;
}

int main() {
    auto timer = std::chrono::high_resolution_clock::now();
    std::string file("../../../assets/shakespeare.txt");
    auto ns = coro::sync_wait(lines(file));
    assert(ns == 65018);
    auto elapsed = std::chrono::high_resolution_clock::now() - timer;
    std::cout << "done " << std::chrono::duration_cast<std::chrono::microseconds>(elapsed).count() << "μs" << std::endl;

    return 0;
}
