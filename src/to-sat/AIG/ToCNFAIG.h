#ifndef TOCNFAIG_H_
#define TOCNFAIG_H_

#include "../../extlib-abc/aig.h"
#include "../../extlib-abc/cnf_short.h"
#include "../../extlib-abc/dar.h"
#include "../ToSATBase.h"
#include "BBNodeManagerAIG.h"

namespace BEEV {

class ToCNFAIG {
	Cnf_Dat_t* priorCnfData;

    // no copy. no assignment.
	ToCNFAIG&  operator = (const ToCNFAIG& other);
	ToCNFAIG(const ToCNFAIG& other);

	const UserDefinedFlags& uf;


public:
	ToCNFAIG(const UserDefinedFlags& _uf):
		uf(_uf)
	{
		priorCnfData = NULL;
	}

	~ToCNFAIG() {
		if (NULL != priorCnfData)
			Cnf_DataFree(priorCnfData);
	}

	void toCNF(const BBNodeAIG& top, Cnf_Dat_t*& cnfData,
			ToSATBase::ASTNodeToSATVar& nodeToVar,
			bool needAbsRef,  BBNodeManagerAIG& _mgr);

	// assumes the above function was called first.
	void toCNF_renter(const BBNodeAIG& top, Cnf_Dat_t*& cnfData,
			ToSATBase::ASTNodeToSATVar& nodeToVar, BBNodeManagerAIG& _mgr);

	// The piror must be set before toCNF_reenter is called.
	void setPrior(Cnf_Dat_t* prior)
	{
		priorCnfData = prior;
	}

};

}
#endif /* TOCNFAIG_H_ */
