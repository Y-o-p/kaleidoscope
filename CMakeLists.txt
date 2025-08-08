cmake_minimum_required(VERSION 3.10)

project(Kaleidoscope)

# Set the c++ standard
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED True)

# Find LLVM
# Reference: https://llvm.org/docs/CMake.html#embedding-llvm-in-your-project
find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

include_directories(${LLVM_INCLUDE_DIRS})
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

add_executable(Kaleidoscope main.cpp)

llvm_map_components_to_libnames(llvm_libs support core irreader)

target_link_libraries(Kaleidoscope ${llvm_libs})
