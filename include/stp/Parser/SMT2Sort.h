#ifndef STP_PARSER_SMT2SORT_H
#define STP_PARSER_SMT2SORT_H

#include "stp/AST/SourceSort.h"
#include <vector>

namespace stp
{
// A sort abbreviation is expanded while its defining signature is in scope.
// Only local parameter slots remain to be substituted at an application.
struct SMT2Sort
{
  enum class Kind { Concrete, Parameter, Array };
  Kind kind = Kind::Concrete;
  SourceSort sort;
  unsigned parameter = 0;
  std::vector<SMT2Sort> children;

  explicit SMT2Sort(const SourceSort& value) : sort(value) {}
  static SMT2Sort param(unsigned slot)
  {
    SMT2Sort result(SourceSort::unknown());
    result.kind = Kind::Parameter;
    result.parameter = slot;
    return result;
  }
  static SMT2Sort array(const SMT2Sort& index, const SMT2Sort& element)
  {
    SMT2Sort result(SourceSort::unknown());
    result.kind = Kind::Array;
    result.children = {index, element};
    return result;
  }
  SMT2Sort substitute(const std::vector<SMT2Sort>& arguments) const
  {
    if (kind == Kind::Parameter)
      return arguments.at(parameter);
    if (kind == Kind::Array)
      return array(children[0].substitute(arguments),
                   children[1].substitute(arguments));
    return *this;
  }
  SourceSort sourceSort() const
  {
    if (kind == Kind::Parameter)
      throw std::invalid_argument("unbound sort parameter");
    if (kind == Kind::Concrete)
      return sort;
    const SourceSort index = children[0].sourceSort();
    const SourceSort element = children[1].sourceSort();
    if (!index.isScalar() || !element.isScalar())
      throw std::invalid_argument("unsupported array index or element sort");
    return SourceSort::array(index, element);
  }
};

struct SMT2SortDefinition
{
  unsigned arity;
  SMT2Sort body;
};
}

#endif
