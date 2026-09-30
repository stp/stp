#ifndef STP_UTIL_SMTLIBSTRING_H
#define STP_UTIL_SMTLIBSTRING_H

#include <string>

namespace stp
{
// SMT-LIB 2.7 section 3.1: double a quote inside a string literal.
// Backslashes, newlines and non-ASCII characters keep their literal meaning.
inline std::string quoteSMTLibString(const std::string& value)
{
  std::string result = "\"";
  result.reserve(value.size() + 2);
  for (char c : value)
  {
    result += c;
    if (c == '"')
      result += '"';
  }
  result += '"';
  return result;
}
}

#endif
