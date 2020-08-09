#include "ModuleLoader.hpp"
#include "paracooba/module.h"
#include <paracooba/common/log.h>

#include "paracooba/broker/broker.h"
#include "paracooba/communicator/communicator.h"
#include "paracooba/runner/runner.h"
#include "paracooba/solver/solver.h"

#include <boost/asio/coroutine.hpp>

#include <boost/dll.hpp>
#include <boost/dll/shared_library.hpp>
#include <boost/dll/shared_library_load_mode.hpp>
#include <boost/filesystem/operations.hpp>
#include <boost/system/system_error.hpp>

auto
ImportModuleDiscoverFunc(boost::filesystem::path path,
                         const std::string& name) {
  return boost::dll::import<decltype(parac_module_discover)>(
    path / name,
    "parac_module_discover",
    boost::dll::load_mode::append_decorations);
}

struct PathSource : public boost::asio::coroutine {
  PathSource(parac_module_type type)
    : type(type) {}

#include <boost/asio/yield.hpp>
  boost::filesystem::path operator()() {
    reenter(this) {
      yield return boost::filesystem::current_path();
      yield return boost::filesystem::current_path() /
        parac_module_type_to_str(type);
      yield return boost::filesystem::current_path() / "modules" /
        parac_module_type_to_str(type);
      yield return boost::dll::program_location().parent_path();
      yield return boost::dll::program_location().parent_path() /
        parac_module_type_to_str(type);
      yield return boost::dll::program_location().parent_path() / "modules" /
        parac_module_type_to_str(type);
      yield return "/usr/local/lib/paracooba";
      yield return "/usr/local/lib";
      yield return "/usr/lib/paracooba";
      yield return "/usr/lib";
    }
    return "";
  }
#include <boost/asio/unyield.hpp>

  parac_module_type type;
};

namespace paracooba {
ModuleLoader::ModuleLoader() {
  m_handle.userdata = this;
  m_handle.prepare = &ModuleLoader::prepare;
}
ModuleLoader::~ModuleLoader() {}

void
ModuleLoader::load(parac_module_type type) {

  PathSource pathSource(type);
  while(!pathSource.is_complete()) {
    boost::filesystem::path path = pathSource();
    std::string name = std::string("parac_") + parac_module_type_to_str(type);
    try {
      auto imported = ImportModuleDiscoverFunc(path, name);
      parac_log(PARAC_LOADER,
                PARAC_DEBUG,
                "{} loaded with parameter {}",
                parac_module_type_to_str(type),
                (path / name).string());
      imported(&m_handle);
      return;
    } catch(boost::system::system_error& err) {
      (void)err;
      // Ignoring failed loads, because multiple locations are tried.
      parac_log(PARAC_LOADER,
                PARAC_TRACE,
                "{} could not be loaded! Message: {}",
                parac_module_type_to_str(type),
                err.what());
    }
  }

  parac_log(PARAC_LOADER,
            PARAC_FATAL,
            "{} could not be loaded!",
            parac_module_type_to_str(type));
}

void
ModuleLoader::load() {
  for(size_t i = 0; i < PARAC_MOD__COUNT; ++i) {
    parac_module_type type = static_cast<parac_module_type>(i);
    load(type);
  }
}

bool
ModuleLoader::isComplete() {
  return hasSolver() && hasRunner() && hasCommunicator() && hasBroker();
}

bool
ModuleLoader::hasSolver() {
  return m_modules[PARAC_MOD_SOLVER] && m_mod_solver;
}
bool
ModuleLoader::hasBroker() {
  return m_modules[PARAC_MOD_BROKER] && m_mod_broker;
}
bool
ModuleLoader::hasRunner() {
  return m_modules[PARAC_MOD_RUNNER] && m_mod_runner;
}
bool
ModuleLoader::hasCommunicator() {
  return m_modules[PARAC_MOD_COMMUNICATOR] && m_mod_communicator;
}

parac_module*
ModuleLoader::prepare(parac_handle* handle, parac_module_type type) {
  assert(handle);
  assert(handle->userdata);
  ModuleLoader* self = static_cast<ModuleLoader*>(handle->userdata);

  auto& ptr = self->m_modules[type];
  if(ptr) {
    parac_log(PARAC_LOADER,
              PARAC_FATAL,
              "Prepare called more than once for module {}!",
              parac_module_type_to_str(type));
    return nullptr;
  }

  ptr = std::make_unique<parac_module>();

  return ptr.get();
}
}
