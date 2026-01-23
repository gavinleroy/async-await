#include <iostream>
#include <fstream>
#include <vector>
#include <numeric>
#include <chrono>
#include <coro/coro.hpp>
#include <iterator>

struct suspend_maybe {
    bool ready;
    explicit suspend_maybe(bool ready) : ready(ready) { }
    bool await_ready() const noexcept { return ready; }
    void await_suspend(std::coroutine_handle<>) const noexcept { }
    void await_resume() const noexcept { }
};

template<typename T>
class [[nodiscard]] generator {
public:
    struct iterator;
    struct promise_type;
    using handle_type = std::coroutine_handle<promise_type>;
    using range_type = std::ranges::subrange<iterator, std::default_sentinel_t>;

private:
    handle_type handle;

    explicit generator(handle_type handle) : handle(std::move(handle)) { }
public:
    class iterator {
    private:
        handle_type handle;
        friend generator;

        explicit iterator(handle_type handle) noexcept : handle(handle) { }
    public:
        using iterator_concept = std::input_iterator_tag;
        using value_type = std::remove_cvref_t<T>;
        using difference_type = std::ptrdiff_t;

        bool operator==(std::default_sentinel_t) const noexcept {
            return handle.done();
        }

        inline iterator &operator++();
        void operator++(int) { operator++(); }

        inline T const *operator->() const noexcept;
        T const &operator*() const noexcept {
          return *operator->();
        }
    };
    iterator begin() noexcept {
        return iterator{handle};
    }
    std::default_sentinel_t end() const noexcept {
        return std::default_sentinel;
    }

    struct promise_type {
        // invariant: whenever the coroutine is non-finally suspended, this is nonempty
        // either the T const* is nonnull or the range_type is nonempty
        // note that neither of these own the data (T object or generator)
        // the coroutine's suspended state is often the actual owner
        std::variant<T const*, range_type> value = nullptr;

        generator get_return_object() {
            return generator(handle_type::from_promise(*this));
        }
        // initially suspending does not play nice with the conventional asymmetry between begin() and end()
        std::suspend_never initial_suspend() { return {}; }
        std::suspend_always final_suspend() noexcept { return {}; }
        void unhandled_exception() { std::terminate(); }
        std::suspend_always yield_value(T const &x) noexcept {
            value = std::addressof(x);
            return {};
        }
        suspend_maybe await_transform(generator &&source) noexcept {
            range_type range(source);
            value = range;
            return suspend_maybe(range.empty());
        }
        void return_void() { }
    };

    generator(generator const&) = delete;
    generator(generator &&other) noexcept : handle(std::move(other.handle)) {
        other.handle = nullptr;
    }
    ~generator() { if(handle) handle.destroy(); }
    generator& operator=(generator const&) = delete;
    generator& operator=(generator &&other) noexcept {
        // idiom: implementing assignment by swapping means the impending destruction/reuse of other implicitly handles cleanup of the resource being thrown away (which originated in *this)
        std::swap(handle, other.handle);
        return *this;
    }
};

template<typename T>
inline auto generator<T>::iterator::operator++() -> iterator& {
    struct visitor {
        handle_type handle;
        void operator()(T const*) { handle(); }
        void operator()(range_type &r) {
            if(r.advance(1).empty()) handle();
        }
    };
    std::visit(visitor(handle), handle.promise().value);
    return *this;
}
template<typename T>
inline auto generator<T>::iterator::operator->() const noexcept -> T const* {
    struct visitor {
        T const *operator()(T const *x) { return x; }
        T const *operator()(range_type &r) {
            return r.begin().operator->();
        }
    };
    return std::visit(visitor(), handle.promise().value);
}

template<typename T>
struct bin_tree {
  T value;
  bin_tree<T>* left;
  bin_tree<T>* right;

  generator<T> values() {
    if (this->left)
      co_await this->left->values();
    co_yield this->value;
    if (this->right)
      co_await this->right->values();
  }
};


int main() {
  bin_tree<int> tree = {
    11,
    new bin_tree<int>{7, new bin_tree<int>{3, nullptr, nullptr}, new bin_tree<int>{9, nullptr, nullptr}},
    new bin_tree<int>{15, new bin_tree<int>{13, nullptr, nullptr}, new bin_tree<int>{19, new bin_tree<int>{18, nullptr, nullptr}, nullptr}}
  };

  for (auto v : tree.values())
    std::cout << v << std::endl;

  return 0;
}
