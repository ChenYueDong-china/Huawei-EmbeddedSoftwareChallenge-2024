project(c++)
cmake_minimum_required(VERSION 3.25)

#设置exe文件输出目录
#string(REGEX REPLACE "(.*)/(.*)/(.*)" "\\1" PROJECT_INIT_PATH ${PROJECT_SOURCE_DIR})
##message("上层目录=" ${PROJECT_INIT_PATH})
#set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${PROJECT_INIT_PATH}")

#保险起见，给栈默认就够了，栈最低也是1m，堆大概率改不了，随便玩玩
MATH(EXPR stack_size "1*1024*1024")
MATH(EXPR heap_size "256*1024*1024")
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O0 -Wl,--stack=${stack_size},--heap=${heap_size}")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -O3 -Wl,--stack=${stack_size},--heap=${heap_size}")
add_subdirectory(pantiqi)
add_subdirectory(shengchengqi)
add_executable(main "main.cpp")