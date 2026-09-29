#ifndef STP_PARSER_SMT2OUTPUT_H
#define STP_PARSER_SMT2OUTPUT_H

#include "stp/Util/Output.h"
#include <fstream>
#include <memory>
#include <optional>
#include <string>

namespace stp
{
// A script's channels sit inside the caller's output route. Standard channel
// names refer to the caller's sinks; filenames are opened in append mode.
// The route lives only while parsing, including execution of its commands.
class SMT2Output
{
  using Sink = std::function<void(std::string_view)>;
  Sink inherited_out, inherited_err;
  std::string regular_name = "stdout", diagnostic_name = "stderr";
  std::unique_ptr<std::ofstream> regular_file, diagnostic_file;
  Sink out = [this](std::string_view s) { write(false, s); };
  Sink err = [this](std::string_view s) { write(true, s); };
  api::detail::OutputSinks sinks{&out, &err, nullptr};
  std::optional<api::detail::OutputRoute> route;

  void write(bool diagnostic, std::string_view text);

public:
  void begin();
  void end();
  void reset();
  bool set(bool diagnostic, const std::string& name);
  const std::string& name(bool diagnostic) const
  {
    return diagnostic ? diagnostic_name : regular_name;
  }
};
}

#endif
