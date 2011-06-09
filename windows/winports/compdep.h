#ifndef __COMPDEP_H__
#define __COMPDEP_H__   1

//some compiler related functions for porting
/************************************************************************/
#ifdef _MSC_VER
#include <cmath>
// msvc missed the log2 function
inline long double log2(long double x)
{
  return log(x)/log((long double)2);
}
// strtoull is missing too
#define strtoull _strtoui64
#endif

/************************************************************************/
#endif

