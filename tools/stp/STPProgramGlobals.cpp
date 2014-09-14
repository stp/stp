/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#include <string>

namespace BEEV
{
  //Some constant global vars for the Main function. Once they are
  //set, these globals will remain constants. These vars are not used
  //in the STP library.
  const char * prog = "stp";
  int linenum  = 1;
  const char * usage = "Usage: %s [-option] [infile]\n";
  std::string helpstring = "\n";
} //end of namespace BEEV
