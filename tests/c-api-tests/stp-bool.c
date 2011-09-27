#include <stdio.h>
#include "c_interface.h"

int main ()
{
	VC vc;
	int query_result;
	int count = 0;

	vc = vc_createValidityChecker ();


	Type type64 = vc_boolType (vc);


	vc_Destroy (vc);
}
