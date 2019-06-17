#ifndef PARACUBER_CONFIG_HPP

#include <any>
#include <array>
#include <boost/program_options/options_description.hpp>
#include <boost/program_options/variables_map.hpp>
#include <cstddef>
#include <string_view>

namespace paracuber {
/** @brief Store for communication options specific for each node.
 *
 */
class Config
{
  public:
  /** Configuration variable differentiator enumeration.
   */
  enum Key
  {
    Debug,
    LocalName,

    _KEY_COUNT
  };

  /** @brief Constructor
   */
  Config();
  /** @brief Destructor.
   */
  ~Config();

  /** @brief Parse command line parameters and also process provided
   * configuration files.
   *
   * @return True if program execution may continue, false if program should be
   * terminated.
   */
  bool parseParameters(int argc, char* argv[]);
  /** @brief Parse command line parameters and also process provided
   * configuration files.
   *
   * @return True if program execution may continue, false if program should be
   * terminated.
   */
  bool parseConfigFile(std::string_view filePath);

  /** @brief Get a configuration variable with type and key.
   */
  template<typename T>
  inline T& get(Key key)
  {
    return std::any_cast<T&>(m_config[key]);
  }
  /** @brief Get a std::string configuration variable.
   */
  inline std::string_view getString(Key key)
  {
    std::string& str = get<std::string>(key);
    return std::string_view{ str.c_str(), str.size() };
  }
  /** @brief Get an int32 configuration variable.
   */
  inline int32_t getInt32(Key key) { return get<int32_t>(key); }
  /** @brief Get an int64 configuration variable.
   */
  inline int64_t getInt64(Key key) { return get<int64_t>(key); }
  /** @brief Get a bool configuration variable.
   */
  inline bool getBool(Key key) { return get<bool>(key); }

  /** @brief Get a configuration variable which can be cast in any way.
   */
  inline std::any get(Key key) { return m_config[key]; }
  /** @brief Set a configuration variable.
   */
  inline void set(Key key, std::any val) { m_config[key] = val; }

  /** @brief Get a configuration variable which can be cast in any way.
   */
  std::any operator[](Key key) { return get(key); }

  private:
  bool processCommonParameters(
    const boost::program_options::variables_map& map);

  using ConfigArray =
    std::array<std::any, static_cast<std::size_t>(_KEY_COUNT)>;
  ConfigArray m_config;

  boost::program_options::options_description m_optionsCLI;
  boost::program_options::options_description m_optionsCommon;
  boost::program_options::options_description m_optionsFile;
};

constexpr const char*
GetConfigNameFromEnum(Config::Key key)
{
  switch(key) {
    case Config::Debug:
      return "debug";
    case Config::LocalName:
      return "local-name";
    default:
      return "";
  }
}
}

#endif
