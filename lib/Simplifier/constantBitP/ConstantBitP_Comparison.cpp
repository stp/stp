// -*- c++ -*-
/********************************************************************
 * AUTHORS: Unknown
 *
 * BEGIN DATE: November, 2005
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ********************************************************************/

#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_Utility.h"
// FIXME: External library
#include "extlib-constbv/constantbv.h"


// The signed and unsigned versions of the four comparison operations: > < >= <=

// Establishes consistency over the intervals of the operations. Then
// increase the minimum value by turning on the highest unfixed bit.
// If that takes us past the other value's maximum. Then that bit
// must be zero.

// Trevor Hansen. BSD License.

namespace simplifier
{
namespace constantBitP
{

Result bvSignedLessThanBothWays(FixedBits& c0, FixedBits &c1, FixedBits& output);
Result bvSignedLessThanEqualsBothWays(FixedBits& c0, FixedBits &c1, FixedBits& output);

Result bvSignedLessThanBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	assert(children.size() == 2);
	return bvSignedLessThanBothWays(*children[0], *children[1], output);
}

Result bvSignedGreaterThanBothWays(FixedBits & c0, FixedBits & c1, FixedBits& output)
{
	return bvSignedLessThanBothWays(c1, c0, output);
}

Result bvSignedGreaterThanBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	assert(children.size() == 2);
	return bvSignedLessThanBothWays(*children[1], *children[0], output);
}

Result bvSignedLessThanEqualsBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	assert(children.size() == 2);
	return bvSignedLessThanEqualsBothWays(*children[0], *children[1], output);
}

Result bvSignedGreaterThanEqualsBothWays(FixedBits & c0, FixedBits & c1, FixedBits& output)
{
	return bvSignedLessThanEqualsBothWays(c1, c0, output);
}

Result bvSignedGreaterThanEqualsBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	assert(children.size() == 2);
	return bvSignedLessThanEqualsBothWays(*children[1], *children[0], output);
}

///////// UNSIGNED.

Result bvLessThanBothWays(FixedBits& c0, FixedBits &c1, FixedBits& output);
Result bvLessThanEqualsBothWays(FixedBits& c0, FixedBits &c1, FixedBits& output);

Result bvLessThanBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	assert(children.size() == 2);
	return bvLessThanBothWays(*children[0], *children[1], output);
}

Result bvGreaterThanBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	assert(children.size() == 2);
	return bvLessThanBothWays(*children[1], *children[0], output);
}

Result bvGreaterThanBothWays(FixedBits& c0, FixedBits &c1, FixedBits& output)
{
	return bvLessThanBothWays(c1, c0, output);
}

Result bvGreaterThanEqualsBothWays(vector<FixedBits*>& children, FixedBits& result)
{
	assert(children.size() == 2);
	return bvLessThanEqualsBothWays(*children[1], *children[0], result);
}

Result bvGreaterThanEqualsBothWays(FixedBits& c0, FixedBits &c1, FixedBits& output)
{
	return bvLessThanEqualsBothWays(c1, c0, output);
}

Result bvLessThanEqualsBothWays(vector<FixedBits*>& children, FixedBits& output)
{
	assert(children.size() == 2);
	return bvLessThanEqualsBothWays(*children[0], *children[1], output);
}

typedef unsigned int* CBV;

void destroy(CBV a, CBV b, CBV c, CBV d)
{
	CONSTANTBV::BitVector_Destroy(a);
	CONSTANTBV::BitVector_Destroy(b);
	CONSTANTBV::BitVector_Destroy(c);
	CONSTANTBV::BitVector_Destroy(d);
}

// Fast exit. Without creating min/max.
bool
fast_exit(FixedBits& c0, FixedBits& c1)
{
  assert(c0.getWidth() == c1.getWidth());
  for (int i = (int)c0.getWidth() - 1; i >= 0; i--) {
      const char c_0 = c0[i];
      const char c_1 = c1[i];

      if (c_0 == '0') {
          if (c_1 == '0')
            continue;
      } else if (c_0 == '1') {
          if (c_1 == '1')
            continue;
      } else if (c_0 == '*' && c_1 == '*') {
          return true;
      }
      return false;
   }
}


///////// Signed operations.


Result bvSignedLessThanBothWays(FixedBits& c0, FixedBits& c1, FixedBits& output)
{
	assert(c0.getWidth() == c1.getWidth());

	if (!output.isFixed(0) && fast_exit(c0,c1))
          return NO_CHANGE;

	CBV c0_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
	CBV c0_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
	CBV c1_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
	CBV c1_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);

	setSignedMinMax(c0, c0_min, c0_max);
	setSignedMinMax(c1, c1_min, c1_max);

	// EG. [0,5] < [6,8]. i.e. max of first is less than min of second.
	if (signedCompare(c0_max, c1_min) < 0)
	{
		if (output.isFixed(0) && !output.getValue(0)) // output is fixed to false.
		{
			destroy(c0_min, c0_max, c1_min, c1_max);
			return CONFLICT;
		}

		if (!output.isFixed(0))
		{
			output.setFixed(0, true);
			output.setValue(0, true);
		}
	}

	// EG. [3,5] < [0,1].
	if (signedCompare(c0_min, c1_max) >= 0)
	{
		// min is greater than max.
		if (output.isFixed(0) && output.getValue(0))
		{
			destroy(c0_min, c0_max, c1_min, c1_max);
			return CONFLICT;
		}

		if (!output.isFixed(0))
		{
			output.setFixed(0, true);
			output.setValue(0, false);
		}
	}

	if (output.isFixed(0) && !output.getValue(0))
	{
		FixedBits t(1, true);
		t.setFixed(0, true);
		t.setValue(0, true);
		destroy(c0_min, c0_max, c1_min, c1_max);
		return bvSignedGreaterThanEqualsBothWays(c0, c1, t);
	}

	const int msb = c0.getWidth() - 1;

	// The signed case.
	if (output.isFixed(0) && output.getValue(0))
	{
		//////////// MSB
		// turn off the sign bit of c0's minimum.
		// If that value is greater or equal to c1's max. SEt it.
		if (!c0.isFixed(msb))
		{
			// turn it on in the minimum.
			CONSTANTBV::BitVector_Bit_Off(c0_min, msb);
			if (signedCompare(c0_min, c1_max) >= 0)
			{
				c0.setFixed(msb, true);
				c0.setValue(msb, true);
				setSignedMinMax(c0, c0_min, c0_max);
			}
			else
			{
				CONSTANTBV::BitVector_Bit_On(c0_min, msb);
			}
		}

		if (!c1.isFixed(msb))
		{
			CONSTANTBV::BitVector_Bit_On(c1_max, msb);
			if (signedCompare(c1_max, c0_min) <= 0)
			{
				c1.setFixed(msb, true);
				c1.setValue(msb, false);
				setSignedMinMax(c1, c1_min, c1_max);
			}
			else
			{
				CONSTANTBV::BitVector_Bit_Off(c1_max, msb);
			}
		}

		///////////// Bits other than the MSB

		if (output.isFixed(0) && output.getValue(0))
		{
			for (int i = (int)c0.getWidth() - 1 - 1; i >= 0; i--)
			{
				if (!c0.isFixed(i))
				{
					// turn it on in the minimum.
					CONSTANTBV::BitVector_Bit_On(c0_min, i);
					if (signedCompare(c0_min, c1_max) >= 0)
					{
						c0.setFixed(i, true);
						c0.setValue(i, false);
						setSignedMinMax(c0, c0_min, c0_max);
					}
					else
					{
						CONSTANTBV::BitVector_Bit_Off(c0_min, i);
						break;
					}
				}
			}

			for (int i = (int)c1.getWidth() - 1 - 1; i >= 0; i--)
			{
				if (!c1.isFixed(i))
				{
					CONSTANTBV::BitVector_Bit_Off(c1_max, i);
					if (signedCompare(c1_max, c0_min) <= 0)
					{
						c1.setFixed(i, true);
						c1.setValue(i, true);
						setSignedMinMax(c1, c1_min, c1_max);
					}
					else
					{
						CONSTANTBV::BitVector_Bit_On(c1_max, i);
						break;
					}
				}
			}
		}
	}
	destroy(c0_min, c0_max, c1_min, c1_max);
	return NOT_IMPLEMENTED;
}


Result bvSignedLessThanEqualsBothWays(FixedBits& c0, FixedBits &c1, FixedBits& output)
{
	assert(c0.getWidth() == c1.getWidth());

        if (!output.isFixed(0) && fast_exit(c0,c1))
          return NO_CHANGE;

	CBV c0_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
	CBV c0_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
	CBV c1_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
	CBV c1_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);

	setSignedMinMax(c0, c0_min, c0_max);
	setSignedMinMax(c1, c1_min, c1_max);

	if (signedCompare(c0_max, c1_min) <= 0)
	{
		if (output.isFixed(0) && !output.getValue(0))
		{
			destroy(c0_min, c0_max, c1_min, c1_max);
			return CONFLICT;
		}

		if (!output.isFixed(0))
		{
			output.setFixed(0, true);
			output.setValue(0, true);
		}
	}

	if (signedCompare(c0_min, c1_max) > 0)
	{
		if (output.isFixed(0) && output.getValue(0))
		{
			destroy(c0_min, c0_max, c1_min, c1_max);
			return CONFLICT;
		}

		if (!output.isFixed(0))
		{
			output.setFixed(0, true);
			output.setValue(0, false);
		}
	}

	// If true. Reverse and send to the other..
	if (output.isFixed(0) && !output.getValue(0))
	{
		FixedBits t(1, true);
		t.setFixed(0, true);
		t.setValue(0, true);
		destroy(c0_min, c0_max, c1_min, c1_max);
		return bvSignedGreaterThanBothWays(c0, c1, t);
	}

       const int msb = c0.getWidth() - 1;

	if (output.isFixed(0) && output.getValue(0))
	{
		//////////// MSB
		// turn off the sign bit of c0's minimum.
		// If that value is greater or equal to c1's max. SEt it.
		if (!c0.isFixed(msb))
		{
			// turn it on in the minimum.
			CONSTANTBV::BitVector_Bit_Off(c0_min, msb);
			if (signedCompare(c0_min, c1_max) > 0)
			{
				c0.setFixed(msb, true);
				c0.setValue(msb, true);
				setSignedMinMax(c0, c0_min, c0_max);
			}
			else
			{
				CONSTANTBV::BitVector_Bit_On(c0_min, msb);
			}
		}

		if (!c1.isFixed(msb))
		{
			CONSTANTBV::BitVector_Bit_On(c1_max, msb);
			if (signedCompare(c1_max, c0_min) < 0)
			{
				c1.setFixed(msb, true);
				c1.setValue(msb, false);
				setSignedMinMax(c1, c1_min, c1_max);
			}
			else
			{
				CONSTANTBV::BitVector_Bit_Off(c1_max, msb);
			}
		}
		//////////// Others.


		// Starting from the high order. Turn on each bit in turn. If it being turned on pushes it past the max of the other side
		// then we know it must be turned off.
		for (int i = (int)c0.getWidth() - 1 - 1; i >= 0; i--)
		{
			if (!c0.isFixed(i)) // bit is variable.
			{
				// turn it on in the minimum.
				CONSTANTBV::BitVector_Bit_On(c0_min, i);
				if (signedCompare(c0_min, c1_max) > 0)
				{
					c0.setFixed(i, true);
					c0.setValue(i, false);
					setSignedMinMax(c0, c0_min, c0_max);
				}
				else
				{
					CONSTANTBV::BitVector_Bit_Off(c0_min, i);
					break;
				}
			}
		}

		// Starting from the high order. Turn on each bit in turn. If it being turned on pushes it past the max of the other side
		// then we know it must be turned off.
		for (int i = (int)c0.getWidth() - 1 - 1; i >= 0; i--)
		{
			if (!c1.isFixed(i)) // bit is variable.
			{
				// turn it on in the minimum.
				CONSTANTBV::BitVector_Bit_Off(c1_max, i);
				if (signedCompare(c1_max, c0_min) < 0)
				{
					c1.setFixed(i, true);
					c1.setValue(i, true);
					setSignedMinMax(c1, c1_min, c1_max);
				}
				else
				{
					CONSTANTBV::BitVector_Bit_On(c1_max, i);
					break;
				}
			}
		}
	}

	destroy(c0_min, c0_max, c1_min, c1_max);
	return NOT_IMPLEMENTED;
}

///////////////////////// UNSIGNED.




// UNSIGNED!!
Result bvLessThanBothWays(FixedBits& c0, FixedBits &c1, FixedBits& output)
{
	assert(c0.getWidth() == c1.getWidth());

        if (!output.isFixed(0) && fast_exit(c0,c1))
          return NO_CHANGE;

	CBV c0_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
	CBV c0_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
	CBV c1_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
	CBV c1_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);

	setUnsignedMinMax(c0, c0_min, c0_max);
	setUnsignedMinMax(c1, c1_min, c1_max);

	// EG. [0,5] < [6,8]. i.e. max of first is less than min of second.
	if (unsignedCompare(c0_max, c1_min) < 0)
	{
		if (output.isFixed(0) && !output.getValue(0)) // output is fixed to false.
		{
			destroy(c0_min, c0_max, c1_min, c1_max);
			return CONFLICT;
		}

		if (!output.isFixed(0))
		{
			output.setFixed(0, true);
			output.setValue(0, true);
		}
	}

	// EG. [3,5] < [0,1].
	if (unsignedCompare(c0_min, c1_max) >= 0)
	{
		// min is greater than max.
		if (output.isFixed(0) && output.getValue(0))
		{
			destroy(c0_min, c0_max, c1_min, c1_max);
			return CONFLICT;
		}

		if (!output.isFixed(0))
		{
			output.setFixed(0, true);
			output.setValue(0, false);
		}
	}

	// If true. Reverse and send to the other.
	if (output.isFixed(0) && !output.getValue(0))
	{
		FixedBits t(1, true);
		t.setFixed(0, true);
		t.setValue(0, true);
		destroy(c0_min, c0_max, c1_min, c1_max);
		return bvGreaterThanEqualsBothWays(c0, c1, t);
	}

	if (output.isFixed(0) && output.getValue(0))
	{
		// Starting from the high order. Turn on each bit in turn. If it being turned on pushes it past the max of the other side
		// then we know it must be turned off.
		for (int i = (int)c0.getWidth() - 1; i >= 0; i--)
		{
			if (!c0.isFixed(i)) // bit is variable.
			{
				// turn it on in the minimum.
				CONSTANTBV::BitVector_Bit_On(c0_min, i);
				if (unsignedCompare(c0_min, c1_max) >= 0)
				{
					c0.setFixed(i, true);
					c0.setValue(i, false);
					setUnsignedMinMax(c0, c0_min, c0_max);
				}
				else
				{
					CONSTANTBV::BitVector_Bit_Off(c0_min, i);
					break;
				}
			}
		}

		for (int i = (int)c1.getWidth() - 1; i >= 0; i--)
		{
			if (!c1.isFixed(i)) // bit is variable.
			{
				CONSTANTBV::BitVector_Bit_Off(c1_max, i);
				if (unsignedCompare(c1_max, c0_min) <= 0)
				{
					c1.setFixed(i, true);
					c1.setValue(i, true);
					setUnsignedMinMax(c1, c1_min, c1_max);
				}
				else
				{
					CONSTANTBV::BitVector_Bit_On(c1_max, i);
					break;
				}
			}
		}
	}

	destroy(c0_min, c0_max, c1_min, c1_max);
	return NOT_IMPLEMENTED;
}

Result bvLessThanEqualsBothWays(FixedBits& c0, FixedBits &c1, FixedBits& output)
{
	assert(c0.getWidth() == c1.getWidth());

        if (!output.isFixed(0) && fast_exit(c0,c1))
          return NO_CHANGE;

	CBV c0_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
	CBV c0_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
	CBV c1_min = CONSTANTBV::BitVector_Create(c0.getWidth(), true);
	CBV c1_max = CONSTANTBV::BitVector_Create(c0.getWidth(), true);

	setUnsignedMinMax(c0, c0_min, c0_max);
	setUnsignedMinMax(c1, c1_min, c1_max);

	// EG. [0,5] <= [6,8]. i.e. max of first is less than min of second.
	if (unsignedCompare(c0_max, c1_min) <= 0)
	{
		if (output.isFixed(0) && !output.getValue(0)) // output is fixed to false.
		{
			destroy(c0_min, c0_max, c1_min, c1_max);
			return CONFLICT;
		}

		if (!output.isFixed(0))
		{
			output.setFixed(0, true);
			output.setValue(0, true);
		}
	}

	// EG. [3,5] <= [0,1].
	if (unsignedCompare(c0_min, c1_max) > 0)
	{
		if (output.isFixed(0) && output.getValue(0))
		{
			destroy(c0_min, c0_max, c1_min, c1_max);
			return CONFLICT;
		}

		if (!output.isFixed(0))
		{
			output.setFixed(0, true);
			output.setValue(0, false);
		}
	}

	// If true. Reverse and send to the other..
	if (output.isFixed(0) && !output.getValue(0))
	{
		FixedBits t(1, true);
		t.setFixed(0, true);
		t.setValue(0, true);
		destroy(c0_min, c0_max, c1_min, c1_max);
		return bvGreaterThanBothWays(c0, c1, t);
	}

	// We only deal with the true case in this function.

	if (output.isFixed(0) && output.getValue(0))
	{
		// Starting from the high order. Turn on each bit in turn. If it being turned on pushes it past the max of the other side
		// then we know it must be turned off.
		for (int i = (int)c0.getWidth() - 1; i >= 0; i--)
		{
			if (!c0.isFixed(i)) // bit is variable.
			{
				// turn it on in the minimum.
				CONSTANTBV::BitVector_Bit_On(c0_min, i);
				if (unsignedCompare(c0_min, c1_max) > 0)
				{
					c0.setFixed(i, true);
					c0.setValue(i, false);
					setUnsignedMinMax(c0, c0_min, c0_max);
				}
				else
				{
					CONSTANTBV::BitVector_Bit_Off(c0_min, i);
					break;
				}
			}
		}

		// Starting from the high order. Turn on each bit in turn. If it being turned on pushes it past the max of the other side
		// then we know it must be turned off.
		for (int i = c0.getWidth() - 1; i >= 0; i--)
		{
			if (!c1.isFixed(i)) // bit is variable.
			{
				// turn it on in the minimum.
				CONSTANTBV::BitVector_Bit_Off(c1_max, i);
				if (unsignedCompare(c1_max, c0_min) < 0)
				{
					c1.setFixed(i, true);
					c1.setValue(i, true);
					setUnsignedMinMax(c1, c1_min, c1_max);
				}
				else
				{
					CONSTANTBV::BitVector_Bit_On(c1_max, i);
					break;
				}
			}
		}
	}
	destroy(c0_min, c0_max, c1_min, c1_max);
	return NOT_IMPLEMENTED;
}

}
}
