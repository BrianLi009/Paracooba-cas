set(CADICAL_SANITIZER_OPTIONS "")

if(DEBUG_ENABLE_ADDRESS_SANITIZER)
    set(CADICAL_SANITIZER_OPTIONS "-fsanitize=address")
endif()

ExternalProject_Add(cadical
    PREFIX cadical
    SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/cadical
    BUILD_IN_SOURCE 1
    BUILD_COMMAND bash -c "./configure -q CXX=\"${CMAKE_CXX_COMPILER}\" CXXFLAGS=\"-fPIC ${CADICAL_SANITIZER_OPTIONS} -fvisibility=hidden\" && make -C build libcadical.a"
    UPDATE_COMMAND ""
    INSTALL_COMMAND ""
    CONFIGURE_COMMAND ""
)

ExternalProject_Add_Step (
    cadical CopyHeaders
    COMMAND ${CMAKE_COMMAND} -E copy_directory ${CMAKE_CURRENT_SOURCE_DIR}/cadical/src/ ${CMAKE_CURRENT_BINARY_DIR}/cadical-out/include/src
    COMMAND ${CMAKE_COMMAND} -E copy_directory ${CMAKE_CURRENT_BINARY_DIR}/cadical-out/include/src ${CMAKE_CURRENT_BINARY_DIR}/cadical-out/include/cadical
    COMMAND ${CMAKE_COMMAND} -E copy_if_different ${CMAKE_CURRENT_SOURCE_DIR}/cadical/build/libcadical.a ${CMAKE_CURRENT_BINARY_DIR}/cadical-out/build/libcadical.a
    DEPENDEES build
    BYPRODUCTS ${CMAKE_CURRENT_BINARY_DIR}/cadical-out/build/${CMAKE_STATIC_LIBRARY_PREFIX}cadical${CMAKE_STATIC_LIBRARY_SUFFIX}
)

file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/cadical-out/build/)
file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/cadical-out/include)

set(libcadical_INCLUDE_DIRS "${CMAKE_CURRENT_BINARY_DIR}/cadical-out/include/")
set(libcadical_INCLUDE_DIRS "${libcadical_INCLUDE_DIRS}" PARENT_SCOPE)
set(libcadical_LIBRARIES ${CMAKE_CURRENT_BINARY_DIR}/cadical-out/build/${CMAKE_STATIC_LIBRARY_PREFIX}cadical${CMAKE_STATIC_LIBRARY_SUFFIX})

add_library(libcadical STATIC IMPORTED GLOBAL)
set_property(TARGET libcadical APPEND PROPERTY INTERFACE_INCLUDE_DIRECTORIES ${libcadical_INCLUDE_DIRS})
set_target_properties(libcadical PROPERTIES IMPORTED_LOCATION ${libcadical_LIBRARIES})

add_dependencies(libcadical cadical)
