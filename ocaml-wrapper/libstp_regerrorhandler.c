//////////////////////////////////////////////////////////
//
// Owned and copyright BitBlaze, 2007. All rights reserved.
// 
//////////////////////////////////////////////////////////

#include <caml/mlvalues.h>
#include <caml/fail.h>
#include "../c_interface.h"

value libstp_regerrorhandler(value _unit)
{
  // could be caml_invalid_argument or caml_failwith...
  // which is more appropriate?
  vc_registerErrorHandler(caml_invalid_argument);
  return Val_unit;
}
