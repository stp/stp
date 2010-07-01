// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: June, 2010
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef BBNODEAIG_H_
#define BBNODEAIG_H_

#include "../../extlib-abc/aig.h"

namespace BEEV
{

  // This class wraps around a pointer to an AIG (provided by the ABC tool).
class BBNodeAIG
{

public:
	Aig_Obj_t * n;

	BBNodeAIG()
	{
		n = NULL;
	}

	BBNodeAIG(Aig_Obj_t * _n)
	{
		n = _n;
	}

	bool IsNull() const
	{
		return n == NULL;
	}

	bool operator==(const BBNodeAIG &other) const
	{
		return n == other.n;
	}

	bool operator!=(const BBNodeAIG &other) const
	{
		return !(n == other.n);
	}


	bool operator<(const BBNodeAIG &other) const
	{
		return n < other.n;
	}

};
std::ostream& operator<<(std::ostream& output, const BBNodeAIG& h)
{
  FatalError("This isn't implemented  yet sorry;");
  return output;
}
}
;

#endif
