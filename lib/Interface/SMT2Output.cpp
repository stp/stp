#include "stp/Parser/SMT2Output.h"
#include <iostream>

namespace stp
{
void SMT2Output::begin()
{
  const auto* outer = api::detail::current_output_route();
  if (outer)
  {
    inherited_out = outer->out ? *outer->out : Sink();
    inherited_err = outer->err ? *outer->err : Sink();
  }
  else
  {
    inherited_out = [](std::string_view s) {
      std::cout << s;
      if (s.empty()) std::cout.flush();
    };
    inherited_err = [](std::string_view s) { std::cerr << s; };
  }
  route.emplace(&sinks, true);
}

void SMT2Output::end()
{
  if (regular_file) regular_file->flush();
  if (diagnostic_file) diagnostic_file->flush();
  route.reset();
}

void SMT2Output::reset()
{
  regular_file.reset();
  diagnostic_file.reset();
  regular_name = "stdout";
  diagnostic_name = "stderr";
}

bool SMT2Output::set(bool diagnostic, const std::string& name)
{
  std::unique_ptr<std::ofstream> file;
  if (name != "stdout" && name != "stderr")
  {
    file.reset(new std::ofstream(name, std::ios::out | std::ios::app));
    if (!*file)
      return false;
  }
  (diagnostic ? diagnostic_file : regular_file) = std::move(file);
  (diagnostic ? diagnostic_name : regular_name) = name;
  return true;
}

void SMT2Output::write(bool diagnostic, std::string_view text)
{
  auto& file = diagnostic ? diagnostic_file : regular_file;
  if (file)
  {
    file->write(text.data(), static_cast<std::streamsize>(text.size()));
    if (text.empty() || diagnostic)
      file->flush();
    return;
  }
  const auto& channel = diagnostic ? diagnostic_name : regular_name;
  const Sink& sink = channel == "stdout" ? inherited_out : inherited_err;
  if (sink)
    sink(text);
}
}
