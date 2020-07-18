#include <cstdlib>
#include <iostream>
#include <memory>
#include <stdexcept>

#include <boost/filesystem.hpp>
#include <boost/filesystem/operations.hpp>
#include <boost/program_options.hpp>

#include <gtkmm-3.0/gtkmm/application.h>

#include "mainwindow.hpp"
#include "tracefile.hpp"

namespace po = boost::program_options;
namespace fs = boost::filesystem;
using std::cerr;
using std::clog;
using std::cout;
using std::endl;
using namespace paracooba;
using namespace paracooba::tracealyzer;

int
main(int argc, char* argv[])
{
  po::options_description desc("Allowed options");
  po::positional_options_description posDesc;
  // clang-format off
  desc.add_options()
    ("help", "produce help message")
    ("force-sort", po::value<bool>(), "force re-sorting the events")
    ("trace", po::value<std::string>(), "concatenated trace file")
  ;
  posDesc.add("trace", -1);
  // clang-format on
  po::variables_map vm;
  po::store(po::command_line_parser(argc, argv)
              .options(desc)
              .positional(posDesc)
              .allow_unregistered()
              .run(),
            vm);
  po::notify(vm);

  if(vm.count("help")) {
    cout << "This tool helps analyzing traces of the parac SAT solver." << endl;
    cout << "First, concatenate all logs into one file using cat." << endl;
    cout << "A script to help with that task is provided in "
            "scripts/concatenate_traces.sh"
         << endl;
    cout << "Then, the file can be sorted and analyzed." << endl << endl;
    cout << desc << endl;
    return EXIT_SUCCESS;
  }

  if(!vm.count("trace")) {
    cerr << "!! Requires a trace file!" << endl;
    return EXIT_FAILURE;
  }

  std::string trace = vm["trace"].as<std::string>();
  if(!fs::exists(trace)) {
    cerr << "!! Trace file \"" << trace << "\" does not exist!" << endl;
    return EXIT_FAILURE;
  }
  if(fs::is_directory(trace)) {
    cerr << "!! File \"" << trace << "\" no file, but a directory!" << endl;
    return EXIT_FAILURE;
  }

  TraceFile traceFile(trace);

  if(vm.count("force-sort") && vm["force-sort"].as<bool>()) {
    traceFile.sort();
  }

  auto app =
    Gtk::Application::create("at.jku.fmv.paracooba.tracealyzer");

  MainWindow mainWindow(traceFile);

  return app->run(mainWindow);
}
