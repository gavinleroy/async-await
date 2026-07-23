cmake_minimum_required(VERSION 3.14)
project(Prog)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_subdirectory(libcoro)

add_executable(Prog main.cpp)

target_link_libraries(Prog PRIVATE libcoro)
