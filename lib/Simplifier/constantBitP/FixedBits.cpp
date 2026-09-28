/********************************************************************
 *
 * BEGIN DATE: November, 2005
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/AST/AST.h"

#include "stp/Simplifier/constantBitP/ConstantBitP_Utility.h"

// To reduce the memory I tried using the constantbv stuff. But because it is
// not
// inlined it took about twice as long per propagation as does using a boolean
// array.
// Other options to reduce memory usage are: vector<bool>, dynamic_bitset, or
// bitMagic.

namespace simplifier
{
namespace constantBitP
{

std::ostream& operator<<(std::ostream& output, const FixedBits& h)
{
  output << "<";
  for (int i = (int)h.getWidth() - 1; i >= 0; i--)
  {
    if (h.isFixed(i))
      output << h.getValue(i);
    else
      output << "-";
  }

  output << ">";

  return output;
}

void FixedBits::fixToZero()
{
  for (unsigned w = 0; w < numWords(); w++)
  {
    fixedW_[w] = (w == numWords() - 1) ? topMask() : ~0ULL;
    valueW_[w] = 0;
  }
}

stp::CBV FixedBits::GetMinBVConst() const
{
  stp::CBV result = CONSTANTBV::BitVector_Create(width, true);

  for (unsigned i = 0; i < width; i++)
  {
    if (isFixedToOne(i))
      CONSTANTBV::BitVector_Bit_On(result, i);
  }

  return result;
}

stp::CBV FixedBits::GetMaxBVConst() const
{
  stp::CBV result = CONSTANTBV::BitVector_Create(width, true);

  for (unsigned i = 0; i < width; i++)
  {
    if (!isFixed(i) || getValue(i))
      CONSTANTBV::BitVector_Bit_On(result, i);
  }

  return result;
}


stp::CBV FixedBits::GetBVConst() const
{
  assert(isTotallyFixed());

  stp::CBV result = CONSTANTBV::BitVector_Create(width, true);

  for (unsigned i = 0; i < width; i++)
  {
    if (getValue(i))
      CONSTANTBV::BitVector_Bit_On(result, i);
  }

  return result;
}

// inclusive
stp::CBV FixedBits::GetBVConst(unsigned to, unsigned from) const
{
  assert(to >= from);
  unsigned resultWidth = to - from + 1;

  stp::CBV result = CONSTANTBV::BitVector_Create(resultWidth, true);

  for (unsigned i = from; i <= to; i++)
  {
    if (getValue(i))
      CONSTANTBV::BitVector_Bit_On(result, i - from);
  }

  return result;
}

void FixedBits::init(const FixedBits& copy)
{
  width = copy.width;
  representsBoolean = copy.representsBoolean;
  allocate();

  memcpy(fixedW_, copy.fixedW_, numWords() * sizeof(uint64_t));
  memcpy(valueW_, copy.valueW_, numWords() * sizeof(uint64_t));
}

bool FixedBits::isTotallyFixed() const
{
  for (unsigned w = 0; w < numWords(); w++)
  {
    const uint64_t mask = (w == numWords() - 1) ? topMask() : ~0ULL;
    if (fixedW_[w] != mask)
      return false;
  }

  return true;
}

bool FixedBits::isTotallyUnfixed() const
{
  for (unsigned w = 0; w < numWords(); w++)
  {
    if (fixedW_[w] != 0)
      return false;
  }

  return true;
}

FixedBits::FixedBits(unsigned n, bool isbool)
{
  assert(n > 0);

  width = n;
  allocate();

  for (unsigned w = 0; w < numWords(); w++)
  {
    fixedW_[w] = 0;
    valueW_[w] = 0; // stops it printing out junk.
  }

  representsBoolean = isbool;
  if (isbool)
    assert(1 == width);
}

// There is no way to represent bottom. So we assume a and b are already at
// least
// one step up the lattice.
FixedBits FixedBits::meet(const FixedBits& a, const FixedBits& b)
{
  assert(a.getWidth() == b.getWidth());
  assert(a.isBoolean() == b.isBoolean());

  FixedBits result(a.getWidth(), a.isBoolean());

  for (unsigned i = 0; i < a.getWidth(); i++)
  {
    if (a.isFixed(i) != b.isFixed(i))
    {
      result.setFixed(i, false);
    }
    else if (a.isFixed(i) && b.isFixed(i) && (a.getValue(i) != b.getValue(i)))
    {
      result.setFixed(i, false);
    }
    else if (a.isFixed(i) && b.isFixed(i))
    { // fixed to the same value.
      result.setFixed(i, true);
      result.setValue(i, a.getValue(i));
    }
  }
  return result;
}

void FixedBits::join(const FixedBits& a)
{
  assert(a.getWidth() == getWidth());
  assert(a.isBoolean() == isBoolean());

  for (unsigned i = 0; i < a.getWidth(); i++)
  {
    if (a.isFixed(i) && isFixed(i) && (a.getValue(i) == getValue(i)))
    {
      // nothind.
    }
    else
    {
      setFixed(i, false);
    }
  }
}

void FixedBits::join(unsigned int a)
{
  for (unsigned i = 0; i < getWidth(); i++)
  {
    if (isFixed(i))
    {
      if ((((a >> i) & 1) == 1) && !getValue(i))
        setFixed(i, false);
      else if ((((a >> i) & 1) == 0) && getValue(i))
        setFixed(i, false);
    }
  }
}

FixedBits FixedBits::createRandom(const unsigned length,
                                  const unsigned probabilityOfSetting,
                                  std::mt19937& trand)
{
  assert(100 >= probabilityOfSetting);

  FixedBits result(length, false);

  unsigned i = 0;
  unsigned randomV = trand();

  int pool = 32;

  while (i < length)
  {
    if (pool < 8)
    {
      randomV = trand();
      pool = 32;
    }

    unsigned val = (randomV & 127);
    randomV >>= 7;
    pool = pool - 7;

    if (val >= 100)
      continue;

    if (val < probabilityOfSetting)
    {
      switch (randomV & 1)
      {
        case 0:
          result.setFixed(i, true);
          result.setValue(i, false);
          break;

        case 1:
          result.setFixed(i, true);
          result.setValue(i, true);
          break;

        default:
          stp::FatalError(LOCATION "never.");
      }
      randomV >>= 1;
    }
    i++;
  }

  return result;
}

// In the world of static analysis this is ALPHA.
FixedBits FixedBits::concreteToAbstract(const stp::ASTNode& n)
{
  // cout << n;

  unsigned bitWidth;
  if (stp::BITVECTOR_TYPE == n.GetType())
    bitWidth = n.GetValueWidth();
  else
    bitWidth = 1;

  FixedBits output(bitWidth, stp::BOOLEAN_TYPE == n.GetType());

  if (stp::BITVECTOR_TYPE == n.GetType())
  {
    // loop through testing each of the bits.
    stp::CBV cbv = n.GetBVConst();

    for (unsigned j = 0; j < bitWidth; j++)
    {
      output.setFixed(j, true);
      output.setValue(j, CONSTANTBV::BitVector_bit_test(cbv, j));
    }
  }
  else
  {
    if (n.GetKind() == stp::TRUE)
    {
      output.setFixed(0, true);
      output.setValue(0, true);
    }
    else if (n.GetKind() == stp::FALSE)
    {
      output.setFixed(0, true);
      output.setValue(0, false);
    }
    else
      stp::FatalError("Unexpected", n);
  }
  return output;
}

FixedBits FixedBits::fromUnsignedInt(unsigned width, unsigned val)
{
  FixedBits output(width, false);

  const unsigned maxWidth = std::max((unsigned)sizeof(unsigned) * 8, width);
  for (unsigned i = 0; i < maxWidth; i++)
  {
    if (i < width && i < sizeof(unsigned) * 8)
    {
      output.setFixed(i, true);
      output.setValue(i, (val & (1u << i)));
    }
    else if (i < width)
    {
      output.setFixed(i, true);
      output.setValue(i, false);
    }
    else // The unsigned value is bigger than the bitwidth of this.
    {    // so it can't be represented.
      if (val & (1u << i))
      {
        stp::FatalError(LOCATION "Cant be represented.");
      }
    }
  }
  return output;
}

bool FixedBits::updateOK(const FixedBits& o, const FixedBits& n, const int upTo)
{
  assert((int)n.getWidth() >= upTo);
  assert((int)o.getWidth() >= upTo);

  for (int i = 0; i < upTo; i++)
  {
    if (n.isFixed(i) && o.isFixed(i))
    {
      if (n.getValue(i) != o.getValue(i))
      {
        return false;
      }
    }
    else if (o.isFixed(i) && !n.isFixed(i))
    {
      return false;
    }
  }

  return true;
}

// If the oldBits can't become the new bits. While respecting the lattice rules.
// That's bad.
// For example. A transfer function shouldn't unfix bits. Or chance the fixed
// bits value.
bool FixedBits::updateOK(const FixedBits& o, const FixedBits& n)
{
  if (n.getWidth() != o.getWidth())
    return false;

  for (unsigned i = 0; i < n.getWidth(); i++)
  {
    if (n.isFixed(i) && o.isFixed(i))
    {
      if (n.getValue(i) != o.getValue(i))
      {
        return false;
      }
    }
    else if (o.isFixed(i) && !n.isFixed(i))
    {
      return false;
    }
  }
  return true;
}

// a is "IN" b.
bool FixedBits::in(const FixedBits& a, const FixedBits& b)
{
  assert(a.getWidth() == b.getWidth());

  for (unsigned i = 0; i < a.getWidth(); i++)
  {
    if (a.isFixed(i) && b.isFixed(i) && (a.getValue(i) != b.getValue(i)))
    {
      return false;
    }
    if (!a.isFixed(i) && b.isFixed(i))
      return false;
  }
  return true;
}

bool FixedBits::equals(const FixedBits& a, const FixedBits& b)
{
  if (a.getWidth() != b.getWidth())
    return false;

  for (unsigned i = 0; i < a.getWidth(); i++)
  {
    if (a.isFixed(i) != b.isFixed(i))
    {
      return false;
    }
    if (a.isFixed(i))
      if (a.getValue(i) != b.getValue(i))
        return false;
  }
  return true;
}

// a is "IN" the fixed bits..
bool FixedBits::in(stp::CBV a)
{
  for (unsigned i = 0; i < width; i++)
  {
    if (!isFixed(i))
      continue;

    if (!getValue(i) != !CONSTANTBV::BitVector_bit_test(a,i))
      return false;
  }
  return true;
}


}
}
