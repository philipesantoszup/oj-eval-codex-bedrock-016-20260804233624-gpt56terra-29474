cmake_minimum_required(VERSION 3.16)
project(file_storage_bpt LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_executable(code main.cpp)
target_compile_options(code PRIVATE -O2 -Wall -Wextra -Wshadow)
