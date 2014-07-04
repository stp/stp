// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
#ifndef STP_PROGRAM_GLOBALS_H
#define STP_PROGRAM_GLOBALS_H

#include <iostream>
#include <sstream>
#include <string>
#include <algorithm>
#include <ctime>
#include <unistd.h>
#include <signal.h>
#include <stdio.h>
#include <unistd.h>
#include <vector>

namespace BEEV
{
  //Some constant global vars for the Main function. Once they are
  //set, these globals will remain constants. These vars are not used
  //in the STP library.
  extern const char * prog;
  extern int linenum;
  extern const char * usage;
  extern std::string helpstring;

} //end of namespace BEEV

#endif
