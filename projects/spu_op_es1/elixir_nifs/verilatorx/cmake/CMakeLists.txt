cmake_minimum_required(VERSION 3.16)
project(EXAMPLE)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY $ENV{MIX_BUILD_PATH}/priv)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY $ENV{MIX_BUILD_PATH}/priv)

set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -shared -fPIC -Wall -pthread -I$ENV{ERTS_INCLUDE_DIR}")
set(CMAKE_BUILD_TYPE Release)

function(add_recursive_includes base_dir)
    file(GLOB_RECURSE sub_dirs RELATIVE ${base_dir} ${base_dir}/*)
    foreach(sub_dir ${sub_dirs})
        message(DEBUG:______________"${base_dir}/${sub_dir}")
        if(IS_DIRECTORY "${base_dir}/${sub_dir}")
            include_directories("${base_dir}/${sub_dir}")
        endif()
    endforeach()
endfunction()

# 再帰的にサブディレクトリを探してlink_directoriesを設定する関数
function(add_recursive_link_directories dir)
    file(GLOB_RECURSE all_subdirs LIST_DIRECTORIES true "${dir}/*")
    foreach(subdir ${all_subdirs})
        if(IS_DIRECTORY ${subdir})
            link_directories(${subdir})
        endif()
    endforeach()
endfunction()

# add_subdirectory(hello)
add_subdirectory(spu)
add_subdirectory(spu_nif)

