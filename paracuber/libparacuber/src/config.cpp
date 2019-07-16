#include "../include/paracuber/config.hpp"
#include <boost/program_options.hpp>
#include <cstddef>
#include <iostream>
#include <random>
#include <thread>

namespace po = boost::program_options;

namespace paracuber {
Config::Config()
  : m_optionsCLI("CLI-only options")
  , m_optionsCommon("CLI and config file options")
  , m_optionsFile("Config file options")
{
  /* CLI ONLY OPTIONS
   * --------------------------------------- */
  // clang-format off
  m_optionsCLI.add_options()
    ("help", "produce help message")
    ;
  // clang-format on

  /* CONFIG FILES ONLY OPTIONS
   * --------------------------------------- */
  // clang-forma // clang-format on

  std::random_device dev;
  std::mt19937_64 rng(dev());
  std::uniform_int_distribution<std::mt19937_64::result_type> dist_mac(
    -((int64_t)1 << 47), ((int64_t)1 << 47) - 1);

  /* COMMON OPTIONS
   * --------------------------------------- */
  // clang-format off
  m_optionsCommon.add_options()
    (GetConfigNameFromEnum(Config::LocalName),
         po::value<std::string>()->default_value("Unnamed"), "local name of this solver node")
    (GetConfigNameFromEnum(Config::InputFile),
         po::value<std::string>()->default_value(""), "input file (problem) to parse")
    (GetConfigNameFromEnum(Config::ThreadCount),
         po::value<uint32_t>()->default_value(std::thread::hardware_concurrency()),
         "number of worker threads to execute tasks on")
    (GetConfigNameFromEnum(Config::UDPPort),
         po::value<uint16_t>()->default_value(18001),
         "udp port for incoming & outgoing control messages")
    (GetConfigNameFromEnum(Config::Id),
         po::value<int64_t>()->default_value(dist_mac(rng)),
         "Unique Number (only 48 Bit) (can be MAC address)")
    ("debug,d", po::bool_switch(&m_debugMode)->default_value(false), "debug mode (all debug output)")
    ("info,i", po::bool_switch(&m_infoMode)->default_value(false), "info mode (more information)")
    ("daemon", po::bool_switch(&m_daemonMode)->default_value(false), "daemon mode")
    ;
  // clang-format on
}

Config::~Config() {}

bool
Config::parseParameters(int argc, char** argv)
{
  po::positional_options_description positionalOptions;
  positionalOptions.add("input-file", 1);

  po::options_description cliGroup;
  cliGroup.add(m_optionsCommon).add(m_optionsCLI);
  po::variables_map vm;
  po::store(po::command_line_parser(argc, argv)
              .options(cliGroup)
              .positional(positionalOptions)
              .run(),
            vm);
  po::notify(vm);

  if(vm.count("help")) {
    std::cout << m_optionsCLI << std::endl;
    std::cout << m_optionsCommon << std::endl;
    std::cout << m_optionsFile << std::endl;
    return false;
  }
  return processCommonParameters(vm);
}

bool
Config::parseConfigFile(std::string_view filePath)
{
  return true;
}

template<typename T>
inline void
conditionallySetConfigOptionToArray(
  const boost::program_options::variables_map& vm,
  std::any* arr,
  Config::Key key)
{
  if(vm.count(GetConfigNameFromEnum(key))) {
    arr[key] = vm[GetConfigNameFromEnum(key)].as<T>();
  }
}

bool
Config::processCommonParameters(const boost::program_options::variables_map& vm)
{
  conditionallySetConfigOptionToArray<std::string>(
    vm, m_config.data(), Config::LocalName);
  conditionallySetConfigOptionToArray<std::string>(
    vm, m_config.data(), Config::InputFile);
  conditionallySetConfigOptionToArray<uint32_t>(
    vm, m_config.data(), Config::ThreadCount);
  conditionallySetConfigOptionToArray<uint16_t>(
    vm, m_config.data(), Config::UDPPort);
  conditionallySetConfigOptionToArray<int64_t>(
    vm, m_config.data(), Config::Id);

  return true;
}
}
