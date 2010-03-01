#ifndef BBNodeManager_H_
#define BBNodeManager_H_

#include "BBNode.h"
#include "../STPManager/STPManager.h"

namespace BEEV {
class ASTNode;
typedef std::vector<ASTNode> ASTVec;

extern BBNodeVec _empty_BBNodeVec;

class BBNodeManager {
	ASTNode ASTTrue, ASTFalse;
	STPMgr *stp;

public:
	BBNodeManager(STPMgr *_stp) {
		stp = _stp;
		ASTTrue = stp->CreateNode(TRUE);
		ASTFalse = stp->CreateNode(FALSE);
	}

	~BBNodeManager() {
	}

	BBNode getFalse() {
		return ASTFalse;
	}

	BBNode CreateSymbol(const ASTNode& n, unsigned i) {
		if (n.GetType() == BOOLEAN_TYPE) {
			assert(i == 0);
			return n;
		} else
			return stp->CreateNode(BVGETBIT, n, stp->CreateBVConst(32, i));
	}

	BBNode getTrue() {
		return ASTTrue;
	}

	// CreateSimpForm removes IFF which aren't handled by the cnf converter.
	BBNode CreateNode(Kind kind, BBNodeVec& children) {
		return stp->CreateSimpForm(kind, children);
	}

	BBNode CreateNode(Kind kind, const BBNode& child0) {
		return stp->CreateSimpForm(kind, child0);
	}

	BBNode CreateNode(Kind kind, const BBNode& child0, const BBNode& child1) {
		return stp->CreateSimpForm(kind, child0, child1);
	}

	BBNode CreateNode(Kind kind, const BBNode& child0, const BBNode& child1,
			const BBNode& child2) {
		return stp->CreateSimpForm(kind, child0, child1, child2);
	}
};

}
;

#endif /* BBNodeManager_H_ */
