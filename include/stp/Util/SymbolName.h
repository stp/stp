/********************************************************************
 * AUTHORS: Andrew Teylu
 *
 * BEGIN DATE: September, 2026
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#ifndef STP_UTIL_SYMBOL_NAME_H
#define STP_UTIL_SYMBOL_NAME_H

#include <string_view>

namespace stp
{
// SMT-LIB 2.6 section 3.1: quoted symbols contain printable characters and
// whitespace, but have no escape for '|' or '\\'. Check bytes independently
// of the locale: non-ASCII bytes (including UTF-8) are allowed, as are tab,
// newline and carriage return. The empty string is valid content for a
// fresh-name prefix; callers decide whether a complete name may be empty.
inline bool isSMTLIBSymbolContent(std::string_view name)
{
  for (const unsigned char c : name)
    if (c == '|' || c == '\\' || c == 0x7f ||
        (c < 0x20 && c != '\t' && c != '\n' && c != '\r'))
      return false;
  return true;
}
} // namespace stp

#endif
