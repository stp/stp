#ifndef TOCNFAIG_H_
#define TOCNFAIG_H_

#include "../../extlib-abc/aig.h"
#include "../../extlib-abc/cnf_short.h"
#include "../../extlib-abc/dar.h"
#include "../ToSATBase.h"
#include "BBNodeManagerAIG.h"

namespace BEEV {

class ToCNFAIG{

    // no copy. no assignment.
	ToCNFAIG&  operator = (const ToCNFAIG& other);
	ToCNFAIG(const ToCNFAIG& other);

	UserDefinedFlags& uf;

public:
	ToCNFAIG(UserDefinedFlags& _uf):
		uf(_uf)
	{
	}

	~ToCNFAIG()
	{
	}

	void toCNF(const BBNodeAIG& top, Cnf_Dat_t*& cnfData,
			ToSATBase::ASTNodeToSATVar& nodeToVar,
			bool needAbsRef,  BBNodeManagerAIG& _mgr);
};

}
#endif /* TOCNFAIG_H_ */
