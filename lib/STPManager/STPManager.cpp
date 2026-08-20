/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
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

// to get the PRIu64 macro from inttypes, this needs to be defined.
#include "stp/STPManager/STPManager.h"
#include "stp/Extensionality/ExtensionalityContext.h"
#include "stp/FloatBlaster/rounding_modes.h"
#include "stp/Printer/SMTLIBPrinter.h"
#include "stp/Util/CBVOps.h"
#include "stp/Util/NodeIterator.h"
#include <cmath>
#include <cstdint>

namespace stp
{
using std::cout;
using std::endl;

// Probe the unique table with a non-owning (kind, borrowed children) key. On
// a hit nothing is built; only on a miss is the tail-allocated node created.
ASTInterior* STPMgr::LookupOrCreateInterior(Kind kind, ASTChildren children)
{
  const ASTInteriorSet::iterator it =
      _interior_unique_table.find(ASTInterior::Probe{kind, children});
  if (it != _interior_unique_table.end())
    return *it;

  if (kind == NOT)
  {
    // The internal node can't be a NOT, because then we'd add
    // 1 to the NOT's node number, meaning we'd hit an even number,
    // which could duplicate the next newNodeNum().
    assert(children[0].GetKind() != NOT);
  }

  ASTInterior* n_ptr = ASTInterior::create(this, kind, children);
  _interior_unique_table.insert(n_ptr);
  return n_ptr;
}

ostream& operator<<(ostream& os, const ASTNodeMap& nmap)
{
  ASTNodeMap::const_iterator iend = nmap.end();
  for (ASTNodeMap::const_iterator i = nmap.begin(); i != iend; i++)
  {
    os << "Key: " << i->first << endl;
    os << "Value: " << i->second << endl;
  }
  return os;
}

////////////////////////////////////////////////////////////////
// STPMgr member functions to create ASTSymbol and ASTBVConst
////////////////////////////////////////////////////////////////
ASTNode STPMgr::LookupOrCreateSymbol(const char* const name)
{
  // This legacy entry point has no sort parameter. Preserve its historical
  // name lookup semantics for internal clients, while all typed public
  // declarations go through CreateSourceSymbol instead.
  ASTNode existing;
  if (LookupSymbol(name, existing))
    return existing;

  ASTSymbol temp_sym(this, name);
  ASTNode n(LookupOrCreateSymbol(temp_sym));
  return n;
}

ASTNode STPMgr::CreateSourceSymbol(const char* const name,
                                   const SourceSort& source_sort)
{
  if (!source_sort.isKnown())
    FatalError("CreateSourceSymbol requires a known source sort");
  if (source_sort.containsFloatingPoint())
    noteFloatingPoint();
  else if (source_sort.usesFloatingPointTheory())
    noteFloatingPointTheory();
  ASTSymbol temp_sym(this, name, source_sort);
  return ASTNode(LookupOrCreateSymbol(temp_sym));
}

// FIXME: _name is now a constant field, and this assigns to it
// because it tries not to copy the string unless it needs to.  How
// do I avoid copying children in ASTInterior?  Perhaps I don't!

// Note: There seems to be a limitation of std::unordered_set, in that insert
// returns a const iterator to the value.  That prevents us from
// modifying the name (in a hash-preserving way) after the symbol is
// inserted.  FIXME: Is there a way to do this with insert?  Need a
// function to make a new object in the middle of insert.  Read STL
// documentation.
ASTSymbol* STPMgr::LookupOrCreateSymbol(ASTSymbol& s)
{
  ASTSymbol* s_ptr = &s; // it's a temporary key.

  //_symbol_unique_table.insert(s_ptr);
  // return s_ptr;
  // Do an explicit lookup to see if we need to create a copy of the
  // string.
  ASTSymbolSet::const_iterator it = _symbol_unique_table.find(s_ptr);
  if (it == _symbol_unique_table.end())
  {
    // Make a new ASTSymbol with duplicated string (can't assign
    // _name because it's const).  Can cast the iterator to
    // non-const -- carefully.
    // std::string strname(s_ptr->GetName());
    ASTSymbol* s_ptr1 =
        new ASTSymbol(this, strdup(s_ptr->GetName()), s_ptr->_source_sort);
    s_ptr1->_value_width = s_ptr->_value_width;
    s_ptr1->_index_width = s_ptr->_index_width;
    s_ptr1->_exp_width = s_ptr->_exp_width;
    s_ptr1->_sig_width = s_ptr->_sig_width;
    std::pair<ASTSymbolSet::const_iterator, bool> p =
        _symbol_unique_table.insert(s_ptr1);
    indexSymbolName(s_ptr1);
    return *p.first;
  }
  else
  {
    // return symbol found in table.
    return *it;
  }
}

ASTNode STPMgr::introducedSymbol(const std::string& name,
                                 unsigned index_width, unsigned value_width)
{
  const std::map<std::string, ASTNode>::const_iterator found =
      _introduced_by_name.find(name);
  if (found != _introduced_by_name.end())
    return found->second;

  // Only ever on the first request, and only reachable if a public boundary
  // let a reserved name through, which is precisely what they refuse. Adopting
  // the existing symbol instead -- which is what the name-only lookup below
  // does unaided -- makes a user's declaration into one of STP's own objects.
  if (LookupSymbol(name.c_str()))
    FatalError("introducedSymbol: a symbol STP reserves for itself has "
               "already been declared: ",
               ASTUndefined, 0);

  const ASTNode symbol =
      defaultNodeFactory->CreateSymbol(name.c_str(), index_width, value_width);
  noteIntroducedSymbol(symbol);
  _introduced_by_name[name] = symbol;
  return symbol;
}

void STPMgr::indexSymbolName(ASTSymbol* symbol)
{
  _symbol_name_index[symbol->GetName()].push_back(symbol);
}

void STPMgr::unindexSymbolName(ASTSymbol* symbol)
{
  const SymbolNameIndex::iterator entry =
      _symbol_name_index.find(symbol->GetName());
  if (entry == _symbol_name_index.end())
    return;

  std::vector<ASTSymbol*>& declared = entry->second;
  for (size_t i = 0; i < declared.size(); i++)
  {
    if (declared[i] == symbol)
    {
      declared.erase(declared.begin() + i);
      break;
    }
  }

  if (declared.empty())
    _symbol_name_index.erase(entry);
}

bool STPMgr::LookupSymbol(ASTSymbol& s)
{
  ASTSymbol* s_ptr = &s; // it's a temporary key.

  if (_symbol_unique_table.find(s_ptr) == _symbol_unique_table.end())
    return false;
  else
    return true;
}

// The two name-only lookups. A symbol's sort is part of its identity, so
// these cannot probe the unique table; they go through the name index, which
// is maintained alongside it (see _symbol_name_index).
bool STPMgr::LookupSymbol(const char* const name)
{
  return _symbol_name_index.find(name) != _symbol_name_index.end();
}

bool STPMgr::LookupSymbol(const char* const name, ASTNode& output)
{
  const SymbolNameIndex::const_iterator entry = _symbol_name_index.find(name);
  if (entry == _symbol_name_index.end())
    return false;

  // The first symbol declared under the name, where the old scan returned
  // whichever the table happened to iterate first. Only a name declared at
  // two different sorts can tell the difference, and then a deterministic
  // answer is the better one.
  assert(!entry->second.empty());
  output = ASTNode(entry->second.front());
  return true;
}

// Create a ASTBVConst node
ASTNode STPMgr::CreateBVConst(unsigned int width,
                              uint64_t bvconst)
{
  if (width == 0)
    FatalError("CreateBVConst: "
               "trying to create bvconst using "
               "uint64_t of width: ",
               ASTUndefined, width);

  // We create a single bvconst that gets reused.
  if (NULL == CreateBVConstVal)
    CreateBVConstVal = CONSTANTBV::BitVector_Create(65, true);
  CreateBVConstVal = CONSTANTBV::BitVector_Resize(CreateBVConstVal, width);
  CONSTANTBV::BitVector_Empty(CreateBVConstVal);

  // Copy the value into the bitvector 32 bits at a time, low chunk first.
  //
  // 32 rather than the width of a machine word: Chunk_Store takes its value
  // as an "unsigned long", which is 32 bits on i386 and on 64-bit Windows,
  // so a wider chunk would be silently truncated there. This loop stores the
  // same chunks on every target, and needs no shift by the word size -- which
  // is what the old version suppressed -Wshift-count-overflow for.
  //
  // Any width above 64 keeps the zeroes BitVector_Empty just wrote, because
  // the source value has no bits up there.
  const unsigned chunk = 32;
  for (unsigned offset = 0; offset < width && offset < 64; offset += chunk)
  {
    const unsigned size = (width - offset < chunk) ? (width - offset) : chunk;
    const unsigned long c_val =
        static_cast<uint32_t>(bvconst >> offset);
    CONSTANTBV::BitVector_Chunk_Store(CreateBVConstVal, size, offset, c_val);
  }

  ASTBVConst temp_bvconst(this, CreateBVConstVal, width, true);
  return ASTNode(LookupOrCreateBVConst(temp_bvconst));
}

ASTNode STPMgr::charToASTNode(unsigned char* strval, int base, int bit_width)
{
  if (base != 2 && base != 10 && base != 16)
  {
    FatalError("Base must be 2, 10, or 16");
  }
  assert((2 == base || 10 == base || 16 == base));
  if (bit_width <= 0)
  {
    FatalError("Bit width of constant must be greater than 0");
  }
  assert(bit_width > 0);

  // We create a single bvconst that gets reused.
  if (NULL == CreateBVConstVal)
    CreateBVConstVal = CONSTANTBV::BitVector_Create(65, true);
  CreateBVConstVal = CONSTANTBV::BitVector_Resize(CreateBVConstVal, bit_width);
  CONSTANTBV::BitVector_Empty(CreateBVConstVal);

  CONSTANTBV::ErrCode e;
  if (2 == base)
  {
    e = CONSTANTBV::BitVector_from_Bin(CreateBVConstVal, strval);
  }
  else if (10 == base)
  {
    e = CONSTANTBV::BitVector_from_Dec(CreateBVConstVal, strval);
  }
  else // (16 == base)
  {
    e = CONSTANTBV::BitVector_from_Hex(CreateBVConstVal, strval);
  }

  if (0 != e)
  {
    std::cerr << "CreateBVConst: " << BitVector_Error(e);
    FatalError("", ASTUndefined);
  }

  ASTBVConst temp_bvconst(this, CreateBVConstVal, bit_width, true);
  ASTNode n(LookupOrCreateBVConst(temp_bvconst));
  return n;
}

ASTNode STPMgr::CreateBVConst(string strval, int base, int bit_width)
{
  if (bit_width <= 0)
  {
    FatalError("Bit width of constant must be greater than 0");
  }
  assert(bit_width > 0);

  return charToASTNode((unsigned char*)strval.c_str(), base, bit_width);
}

// Create a ASTBVConst node from a char*
ASTNode STPMgr::CreateBVConst(const char* const strval, int base)
{
  assert((2 == base || 10 == base || 16 == base));

  size_t width = strlen((const char*)strval);

  // FIXME Tim: Earlier versions of the code assume that the length of
  // binary strings is 32 bits.
  if (10 == base)
    width = 32;
  if (16 == base)
    width = width * 4;

  return charToASTNode((unsigned char*)strval, base, width);
}

// NB Assumes that it will destroy the bitvector passed to it
ASTNode STPMgr::CreateBVConst(CBV bv, unsigned width)
{
  ASTBVConst temp_bvconst(this, bv, width, true);
  ASTNode n(LookupOrCreateBVConst(temp_bvconst));
  CONSTANTBV::BitVector_Destroy(bv);
  return n;
}

void STPMgr::noteFloatingPoint()
{
  has_floating_point = true;
  has_floating_point_theory = true;
}

ASTNode STPMgr::CreateFPConst(const stp::ASTNode& bvconst,
                              unsigned exp_width, unsigned sig_width)
{
  assert(bvconst.GetKind() == BVCONST);
  assert(exp_width + sig_width == bvconst.GetValueWidth());

  // Temporary key sharing the source's CBV; interning clones it.
  ASTBVConst* src = (ASTBVConst*)bvconst._int_node_ptr;

  // Every NaN pattern interns as the one canonical quiet NaN. SMT-LIB's
  // FloatingPoint sort has a single NaN, and no operation can recover a
  // payload (fp.to_ieee_bv canonicalises; symfpu carries none) -- but the
  // node-creation-time simplifiers do compare constants by identity and by
  // bit pattern (chaseRead's "definately different" skip, CreateSimpleEQ's
  // constant case), and they run before any pass could quotient NaN. Two
  // NaN literals with different payloads used as array indexes would be
  // "proved" to address different cells. Baking the quotient into the
  // constant itself makes those comparisons exact: distinct floating-point
  // constants of one format now denote distinct values.
  {
    CBV b = src->GetBVConst();
    const unsigned stored_sig = sig_width - 1; // the hidden bit is not stored
    bool exp_all_ones = true;
    for (unsigned i = 0; exp_all_ones && i < exp_width; i++)
      exp_all_ones = CONSTANTBV::BitVector_bit_test(b, stored_sig + i);
    bool sig_nonzero = false;
    for (unsigned i = 0; !sig_nonzero && i < stored_sig; i++)
      sig_nonzero = CONSTANTBV::BitVector_bit_test(b, i);

    if (exp_all_ones && sig_nonzero)
    {
      // Already canonical -- positive, and only the quiet bit set -- means
      // stop, or the CreateFPSpecialConst below would recurse forever.
      bool low_payload_zero = true;
      for (unsigned i = 0; low_payload_zero && i + 1 < stored_sig; i++)
        low_payload_zero = !CONSTANTBV::BitVector_bit_test(b, i);
      const bool canonical =
          low_payload_zero &&
          CONSTANTBV::BitVector_bit_test(b, stored_sig - 1) &&
          !CONSTANTBV::BitVector_bit_test(b, exp_width + sig_width - 1);
      if (!canonical)
        return CreateFPSpecialConst(FPSpecial::NaN, exp_width, sig_width);
    }
  }

  ASTFPConst temp(this, src->GetBVConst(), exp_width, sig_width);

  noteFloatingPoint();

  ASTNode n(LookupOrCreateFPConst(temp));
  assert(n.GetKind() == BVCONST);
  return n;
}

// As LookupOrCreateBVConst. The same table holds both flavours of constant:
// the equality functor compares the format widths too, so a floating-point
// constant never unifies with a plain bitvector constant of the same bits.
ASTFPConst* STPMgr::LookupOrCreateFPConst(ASTFPConst& s)
{
  ASTBVConstSet::const_iterator it = _bvconst_unique_table.find(&s);
  if (it != _bvconst_unique_table.end())
    return static_cast<ASTFPConst*>(*it);

  ASTFPConst* s_copy = new ASTFPConst(s);
  _bvconst_unique_table.insert(s_copy);
  return s_copy;
}

ASTNode STPMgr::CreateRMConst(unsigned mode)
{
  using namespace symbolic_fp;
  switch (mode)
  {
    case ROUND_NEAREST_TIES_TO_EVEN:
    case ROUND_TOWARD_POSITIVE:
    case ROUND_TOWARD_NEGATIVE:
    case ROUND_TOWARD_ZERO:
    case ROUND_NEAREST_TIES_TO_AWAY:
      break;
    default:
      FatalError("CreateRMConst requires one of the five rounding modes");
  }

  // A rounding mode has no format, so noteFloatingPoint is never reached for
  // it -- but it still needs FpTotalise's pinning pass to run.
  noteFloatingPointTheory();

  const ASTNode bits = CreateBVConst(5, mode);
  ASTBVConst* src = static_cast<ASTBVConst*>(bits._int_node_ptr);
  ASTRMConst temp(this, src->GetBVConst());
  return ASTNode(LookupOrCreateRMConst(temp));
}

ASTRMConst* STPMgr::LookupOrCreateRMConst(ASTRMConst& s)
{
  const ASTBVConstSet::const_iterator it = _bvconst_unique_table.find(&s);
  if (it != _bvconst_unique_table.end())
    return static_cast<ASTRMConst*>(*it);

  ASTRMConst* copy = new ASTRMConst(s);
  _bvconst_unique_table.insert(copy);
  return copy;
}

ASTNode STPMgr::LiftSourceValue(const ASTNode& carrier,
                                const SourceSort& source_sort)
{
  switch (source_sort.kind())
  {
    case SourceSort::Kind::FloatingPoint:
      if (carrier.GetKind() != BVCONST ||
          carrier.GetValueWidth() != source_sort.packedWidth())
        FatalError("LiftSourceValue: invalid floating-point carrier: ",
                   carrier);
      return CreateFPConst(carrier, source_sort.exponentWidth(),
                           source_sort.significandWidth());
    case SourceSort::Kind::RoundingMode:
      if (carrier.GetKind() != BVCONST || carrier.GetValueWidth() != 5)
        FatalError("LiftSourceValue: invalid RoundingMode carrier: ", carrier);
      return CreateRMConst(carrier.GetUnsignedConst());
    case SourceSort::Kind::Bool:
      if (carrier != ASTTrue && carrier != ASTFalse)
        FatalError("LiftSourceValue: invalid Boolean carrier: ", carrier);
      return carrier;
    case SourceSort::Kind::BitVector:
      if (carrier.GetKind() != BVCONST ||
          carrier.GetValueWidth() != source_sort.bitVectorWidth())
        FatalError("LiftSourceValue: invalid bitvector carrier: ", carrier);
      return carrier;
    default:
      FatalError("LiftSourceValue: cannot lift this source sort");
  }
}

ASTNode STPMgr::roundingModeValidConstraint(const ASTNode& s)
{
  using namespace symbolic_fp;
  ASTVec one_of;
  for (const unsigned mode :
       {ROUND_NEAREST_TIES_TO_EVEN, ROUND_TOWARD_POSITIVE,
        ROUND_TOWARD_NEGATIVE, ROUND_TOWARD_ZERO, ROUND_NEAREST_TIES_TO_AWAY})
  {
    one_of.push_back(
        defaultNodeFactory->CreateNode(EQ, s, CreateRMConst(mode)));
  }
  return defaultNodeFactory->CreateNode(OR, one_of);
}

bool STPMgr::isRoundingModeSortedTerm(const ASTNode& n) const
{
  return n.GetSourceSort().kind() == SourceSort::Kind::RoundingMode;
}

ASTNode STPMgr::arrayBaseSymbol(const ASTNode& arr) const
{
  ASTNode n = arr;
  while (true)
  {
    switch (n.GetKind())
    {
      case SYMBOL:
        return n;
      case WRITE:
        n = n[0];
        break;
      case ITE:
      {
        // Both branches type as arrays of one bit layout; requiring one
        // *sort* keeps a read from being canonicalised under one branch's
        // index sort and taken raw under the other's.
        const ASTNode left = arrayBaseSymbol(n[1]);
        const ASTNode right = arrayBaseSymbol(n[2]);
        if (left.IsNull())
          return right;
        if (!right.IsNull() && left.GetSourceSort() != right.GetSourceSort())
          FatalError("arrayBaseSymbol: an if-then-else mixes arrays whose "
                     "index or element sorts differ: ",
                     n);
        return left;
      }
      default:
        return ASTNode();
    }
  }
}

bool STPMgr::arrayHasFpIndex(const ASTNode& arr, unsigned& exp_width,
                             unsigned& sig_width) const
{
  const SourceSort sort = arr.GetSourceSort();
  if (sort.kind() != SourceSort::Kind::Array ||
      sort.index().kind() != SourceSort::Kind::FloatingPoint)
    return false;
  exp_width = sort.index().exponentWidth();
  sig_width = sort.index().significandWidth();
  return true;
}

bool STPMgr::arrayHasRmIndex(const ASTNode& arr) const
{
  const SourceSort sort = arr.GetSourceSort();
  return sort.kind() == SourceSort::Kind::Array &&
         sort.index().kind() == SourceSort::Kind::RoundingMode;
}

bool STPMgr::arrayHasRmElement(const ASTNode& arr) const
{
  const SourceSort sort = arr.GetSourceSort();
  return sort.kind() == SourceSort::Kind::Array &&
         sort.element().kind() == SourceSort::Kind::RoundingMode;
}

ASTNode STPMgr::CreateFPSpecialConst(FPSpecial which, unsigned exp_width,
                                     unsigned sig_width)
{
  if (exp_width == 0 || sig_width == 0)
    FatalError("CreateFPSpecialConst: a floating-point format needs nonzero "
               "exponent and significand widths");

  const unsigned width = exp_width + sig_width;
  const unsigned stored_sig = sig_width - 1; // the hidden bit is not stored

  // Packed layout, LSB first: [significand | exponent | sign].
  CBV bits = CONSTANTBV::BitVector_Create(width, true);

  const bool negative =
      which == FPSpecial::MinusInfinity || which == FPSpecial::MinusZero;
  const bool exp_all_ones = which == FPSpecial::NaN ||
                            which == FPSpecial::PlusInfinity ||
                            which == FPSpecial::MinusInfinity;

  if (negative)
    CONSTANTBV::BitVector_Bit_On(bits, width - 1);
  for (unsigned i = 0; exp_all_ones && i < exp_width; i++)
    CONSTANTBV::BitVector_Bit_On(bits, stored_sig + i);
  // symfpu's canonical NaN: exponent all ones and only the top stored-
  // significand bit set (pack() emits nanPattern(packedSigWidth) =
  // 1 << (stored_sig - 1), the quiet-bit convention). Matching it keeps the
  // interned constant bit-identical to the NaN every blasted operation
  // produces. Semantically either way is a NaN; bit-identical is tidier.
  if (which == FPSpecial::NaN && stored_sig > 0)
    CONSTANTBV::BitVector_Bit_On(bits, stored_sig - 1);

  // CreateBVConst destroys `bits`.
  ASTNode packed = CreateBVConst(bits, width);
  return CreateFPConst(packed, exp_width, sig_width);
}

ASTNode STPMgr::CreateZeroConst(unsigned width)
{
  assert(width > 0);
  if (zeroes.size() == 0)
  {
    zeroes.push_back(ASTNode()); // null
    for (int i = 1; i < 65; i++)
      zeroes.push_back(CreateZeroConst(i));
  }

  if (width < zeroes.size())
    return zeroes[width];
  else
  {
    CBV z = mkZero(width);
    return CreateBVConst(z, width);
  }
}

ASTNode STPMgr::CreateOneConst(unsigned width)
{
  assert(width > 0);
  if (ones.size() == 0)
  {
    ones.push_back(ASTNode()); // null
    for (int i = 1; i < 65; i++)
      ones.push_back(CreateOneConst(i));
  }

  if (width < ones.size())
    return ones[width];
  else
  {
    CBV o = mkOne(width);

    return CreateBVConst(o, width);
  }
}

ASTNode STPMgr::CreateTwoConst(unsigned width)
{
  // Truncating, as the repeated increments were: two is zero at width 1.
  CBV two = cbvFromU64(width, 2);

  return CreateBVConst(two, width);
}

ASTNode STPMgr::CreateMaxConst(unsigned width)
{
  assert(width > 0);
  if (max.size() == 0)
  {
    max.push_back(ASTNode()); // null
    for (int i = 1; i < 65; i++)
      max.push_back(CreateMaxConst(i));
  }

  if (width < max.size())
    return max[width];
  else
  {
    CBV max = allOnes(width);

    return CreateBVConst(max, width);
  }
}

// To ensure unique BVConst nodes, lookup the node in unique-table
// before creating a new one.
ASTBVConst* STPMgr::LookupOrCreateBVConst(ASTBVConst& s)
{
  ASTBVConst* s_ptr = &s; // it's a temporary key.

  // Do an explicit lookup to see if we need to create a copy of the string.
  ASTBVConstSet::const_iterator it;
  if ((it = _bvconst_unique_table.find(s_ptr)) == _bvconst_unique_table.end())
  {
    // Make a new ASTBVConst with duplicated constant.

    ASTBVConst* s_copy = new ASTBVConst(s);

    std::pair<ASTBVConstSet::const_iterator, bool> p =
        _bvconst_unique_table.insert(s_copy);
    return *p.first;
  }
  else
  {
    // return constant found in table.
    return *it;
  }
}

////////////////////////////////////////////////////////////////
//
//  IO manipulators for Lisp format printing of AST.
//
////////////////////////////////////////////////////////////////

// FIXME: Additional controls
//   * Print node numbers  (addresses/nums)
//   * Printlength limit
//   * Printdepth limit

/** Print a vector of ASTNodes in lisp format */
ostream& LispPrintVec(ostream& os, const ASTVec& v, int indentation = 0)
{
  printer::Lisp_AlreadyPrintedSet.clear();
  // Print the children
  ASTVec::const_iterator iend = v.end();
  for (ASTVec::const_iterator i = v.begin(); i != iend; i++)
  {
    i->LispPrint_indent(os, indentation);
  }
  return os;
}

// add an assertion to the current logical context
void STPMgr::AddAssert(const ASTNode& assert)
{
  if (!(is_Form_kind(assert.GetKind()) && BOOLEAN_TYPE == assert.GetType()))
  {
    FatalError("AddAssert:Trying to assert a non-formula:", assert);
  }

  if (_asserts.empty())
    _asserts.push_back(new ASTVec());

  ASTVec& v = *_asserts.back();
  v.push_back(assert);
}

void STPMgr::Push(void)
{
  _asserts.push_back(new ASTVec());
}

void STPMgr::Pop(void)
{
  if (_asserts.empty())
    FatalError("POP on empty.");

  ASTVec* c = _asserts.back();
  delete c;
  _asserts.pop_back();
}

//BUG this is most probably wrongly handled. It gets propagated and messed up
//with the state. On the next query, this mixed state then causes trouble
void STPMgr::SetQuery(const ASTNode& q)
{
  _current_query = q;
}

const ASTNode STPMgr::GetQuery()
{
  return _current_query;
}

// return a vector of the levels.
// before returning any vector with >1 nodes is turned into a conjunct.
const ASTVec STPMgr::getVectorOfAsserts()
{
  vector<ASTVec*>::iterator it = _asserts.begin();
  vector<ASTVec*>::iterator itend = _asserts.end();

  ASTVec result;
  for (; it != itend; it++)
  {
    ASTVec& a = (**it);
    if (a.size() == 0)
      a.push_back(ASTTrue);
    else if (a.size() > 1)
    {
      ASTNode conjunct = defaultNodeFactory->CreateNode(AND, a);
      a.resize(0);
      a.push_back(conjunct);
    }

    result.push_back(a[0]);
  }

  return result;
}

const ASTVec STPMgr::GetAsserts(void)
{
  vector<ASTVec*>::iterator it = _asserts.begin();
  vector<ASTVec*>::iterator itend = _asserts.end();

  ASTVec v;
  for (; it != itend; it++)
  {
    if (!(*it)->empty())
      v.insert(v.end(), (*it)->begin(), (*it)->end());
  }
  return v;
}

// prints statistics for the ASTNode
void STPMgr::ASTNodeStats(const char* c, const ASTNode& a)
{
  if (!UserFlags.stats_flag)
    return;

  cout << "[" << GetRunTimes()->getDifference() << "]" << c;
  if (UserFlags.print_nodes_flag)
    cout << a << endl;

  cout << "Node size is: " << NodeSize(a) << endl;
}

unsigned int STPMgr::NodeSize(const ASTNode& a)
{
  unsigned int result = 0;
  NodeIterator ni(a, ASTUndefined, *this);
  ASTNode current;
  while ((current = ni.next()) != ni.end())
  {
    result++;
  }
  return result;
}

bool STPMgr::VarSeenInTerm(const ASTNode& var, const ASTNode& term)
{
  // A read-over-write term answers "not seen" WITHOUT walking inside:
  // occurrences of `var` under the write are invisible to this check.
  // (The condition once depended on a remove-writes flag whose other
  // arm returned true; the flag is long gone and the second branch was
  // unreachable, so it has been removed.) Callers using this as an
  // occurs check must therefore refuse array-carrying terms before
  // asking, as the incremental driver's definition harvests do.
  if (READ == term.GetKind() && WRITE == term[0].GetKind())
  {
    return false;
  }

  ASTNodeMap::iterator it;
  if ((it = TermsAlreadySeenMap.find(term)) != TermsAlreadySeenMap.end())
  {
    if (it->second == var)
    {
      return false;
    }
  }

  if (var == term)
  {
    return true;
  }

  for (auto it = term.begin(), itend = term.end();
       it != itend; it++)
  {
    if (VarSeenInTerm(var, *it))
    {
      return true;
    }
    else
    {
      TermsAlreadySeenMap[*it] = var;
    }
  }

  TermsAlreadySeenMap[term] = var;
  return false;
}

ASTNode STPMgr::NewParameterized_BooleanVar(const ASTNode& var,
                                            const ASTNode& constant)
{
  std::ostringstream outVar;
  std::ostringstream outNum;
  // Get the name of Boolean Var
  var.PL_Print(outVar, this);
  constant.PL_Print(outNum, this);
  std::string str(outVar.str());
  str += "(";
  str += outNum.str();
  str += ")";
  ASTNode CurrentSymbol = CreateSymbol(str.c_str(), 0, 0);
  return CurrentSymbol;
}

// If ASTNode remain with references (somewhere), this will segfault.
ExtensionalityContext* STPMgr::getExtensionality()
{
  if (extensionality == NULL)
    extensionality = new ExtensionalityContext(this);
  return extensionality;
}

STPMgr::~STPMgr()
{
  ClearAllTables();

  delete extensionality;
  extensionality = NULL;

  printer::NodeLetVarMap.clear();
  printer::NodeLetVarVec.clear();
  printer::NodeLetVarMap1.clear();
  printer::Lisp_AlreadyPrintedSet.clear();

  delete runTimes;
  runTimes = NULL;
  ASTFalse = ASTNode(0);
  ASTTrue = ASTNode(0);
  ASTUndefined = ASTNode(0);
  _current_query = ASTNode(0);
  // dummy_node = ASTNode(0);

  zeroes.clear();
  ones.clear();
  max.clear();

  if (NULL != CreateBVConstVal)
    CONSTANTBV::BitVector_Destroy(CreateBVConstVal);

  // Released here, in the body, for the same reason as every other member
  // above: destroying a node reaches back into this manager (ASTSymbol::CleanUp
  // unindexes its name, ASTInterior::CleanUp erases from the interior table),
  // and the implicit member-destruction phase runs after those tables are gone.
  distinctGroups.clear();

  Introduced_SymbolsSet.clear();
  _symbol_unique_table.clear();
  _symbol_name_index.clear();
  _bvconst_unique_table.clear();

  vector<ASTVec*>::iterator it = _asserts.begin();
  vector<ASTVec*>::iterator itend = _asserts.end();

  for (; it != itend; it++)
  {
    ASTVec* j = (*it);
    j->clear();
    delete j;
  }
  _asserts.clear();

  delete hashingNodeFactory;

  _interior_unique_table.clear();
}
} // end namespace beev
