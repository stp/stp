/*
Please see LICENSE-CPOL.html in the root directory for the licencing of this file.
Originally by: cppnow
Link: http://www.codeproject.com/KB/cpp/smallptr.aspx
*/

#include "SmallPtr.h"

namespace MINISAT
{
using namespace MINISAT;

uintptr_t sptr_base::_segs = 1;
//boost::mutex sptr_base::_m;
uintptr_t sptr_base::_seg_map[sptr_base::ALIGNMENT] = { 0 };

}; //NAMESPACE MINISAT
