#ifndef STP_PARSER_SMT2ATTRIBUTE_H
#define STP_PARSER_SMT2ATTRIBUTE_H

#include <string>

namespace stp
{
struct SMT2AttributeValue
{
  enum class Kind { Missing, Symbol, String, Numeral, Constant, Reserved, List };
  Kind kind = Kind::Missing;
  std::string text;
};

struct SMT2Attribute
{
  std::string name;
  SMT2AttributeValue value;
};
}

#endif
