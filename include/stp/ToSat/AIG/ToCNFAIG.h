#ifndef TOCNFAIG_H_
#define TOCNFAIG_H_

#include "extlib-abc/aig.h"
#include "extlib-abc/cnf_short.h"
#include "extlib-abc/dar.h"
#include "stp/ToSat/ToSATBase.h"
#include "stp/ToSat/AIG/BBNodeManagerAIG.h"
#include <boost/utility.hpp>

namespace BEEV {

class ToCNFAIG : boost::noncopyable
{
	UserDefinedFlags& uf;

public:
	ToCNFAIG(UserDefinedFlags& _uf):
		uf(_uf)
	{
	}

	void toCNF(const BBNodeAIG& top, Cnf_Dat_t*& cnfData,
			ToSATBase::ASTNodeToSATVar& nodeToVar,
			bool needAbsRef,  BBNodeManagerAIG& _mgr);
};

}
#endif /* TOCNFAIG_H_ */
