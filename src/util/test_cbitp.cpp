// Runs some of the constant bit propagators and compares their results against the maximally precise transformer.
// Those that aren't maximally precise have the super-set relationship checked.

// NB: This is testing code that I don't expect anyone else will use, it's hard to follow what it does!


#include "../simplifier/constantBitP/ConstantBitPropagation.h"
#include "../simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "../simplifier/constantBitP/ConstantBitP_MaxPrecision.h"
#include "../simplifier/constantBitP/FixedBits.h"
#include "../simplifier/constantBitP/MersenneTwister.h"
#include <cstdlib>
#include <ctime>
#include <cmath>
#include "../AST/AST.h"
#include "../AST/AST.h"

#include "../STPManager/STPManager.h"
#include "../to-sat/AIG/ToSATAIG.h"
#include "../sat/MinisatCore.h"
#include "../STPManager/STP.h"
#include "../cpp_interface/cpp_interface.h"

using simplifier::constantBitP::FixedBits;
using namespace simplifier::constantBitP;


namespace simplifier
{
  namespace constantBitP
  {

    using namespace BEEV;

    STPMgr * beev;
    bool isDivide = false;

    const bool debug_printAll = false;

    void
    error(Kind kind, vector<FixedBits*> initialChildren, FixedBits initialOutput, //
        vector<FixedBits*> autoChildren, FixedBits autoOutput, //
        vector<FixedBits*> manualChildren, FixedBits manualOutput)
    {

      cerr << "difference(kind:" << kind << ")" << endl;
      const int size = initialChildren.size();

      cerr << "--------------The Initial Values that were passed to the function" << endl;
      for (int i = 0; i < size; i++)
        cerr << ":" << *(initialChildren[i]) << endl;
      cerr << "result:" << initialOutput << endl;

      cerr << "--------------Values from the Solver" << endl;
      for (int i = 0; i < size; i++)
        cerr << ":" << *(autoChildren[i]) << endl;
      cerr << "result:" << autoOutput << endl;

      cerr << "--------------Values from the Implemented Transfer Function" << endl;
      for (int i = 0; i < size; i++)
        cerr << ":" << *(manualChildren[i]) << endl;
      cerr << "result:" << manualOutput << endl;

      FatalError("As described");
    }

// Set the given fixed bit to one of three values.
    void
    setV(FixedBits& result, int id, int val)
    {
      assert(val >=0 && val <=2);

      switch (val)
        {
      case 0:
        result.setFixed(id, false);
        break;
      case 1:
        result.setFixed(id, true);
        result.setValue(id, false);
        break;
      case 2:
        result.setFixed(id, true);
        result.setValue(id, true);
        break;
        }
    }

    void
    print(const vector<FixedBits*> children, const FixedBits& output, Kind k)
    {
      if (2 == children.size())
        cout << "(" << *(children[0]) << " " << k << " " << *(children[1]) << ")" << " == " << output << endl;
      else
        {
        cout << "(" << k << " ";
        for (unsigned i = 0; i < children.size(); i++)
          cout << *(children[i]) << " ";
        cout << ")" << " == " << output << endl;
        }
    }

    void
    checkEqual(vector<FixedBits*>& initialChildren, FixedBits& initialOutput, Result
    (*transfer)(vector<FixedBits*>&, FixedBits&), Kind kind, bool imprecise)
    {
      // Make two copies of the initial values. One to send to the maximum Precision.
      // The other to send to the manually built transfer functions.
      vector<FixedBits*> manualChildren;
      vector<FixedBits*> autoChildren;

      for (int i = 0; i < (int) initialChildren.size(); i++)
        {
        manualChildren.push_back(new FixedBits(*(initialChildren[i])));
        autoChildren.push_back(new FixedBits(*(initialChildren[i])));
        }

      FixedBits manualOutput(initialOutput);
      FixedBits autoOutput(initialOutput);

      Result manualResult = transfer(manualChildren, manualOutput);

      // Make a copy of the manualResult so we can check if it varies after calling the transfer function a second time.

      FixedBits tempOutput(manualOutput);
      vector<FixedBits*> tempChildren;

      for (int i = 0; i < (int) initialChildren.size(); i++)
        {
        tempChildren.push_back(new FixedBits(*(manualChildren[i])));
        }

      Result tempResult = transfer(tempChildren, tempOutput);

      // First and second time should have the same conflict status.
      if ((manualResult == CONFLICT) != (tempResult == CONFLICT))
        {
        cerr << "One conflict, both conflict";
        error(kind, initialChildren, initialOutput, autoChildren, autoOutput, manualChildren, manualOutput);
        }

      bool different = !FixedBits::equals(tempOutput, manualOutput);
      for (int i = 0; i < (int) initialChildren.size(); i++)
        {
        if (!FixedBits::equals(*tempChildren[i], *manualChildren[i]))
          different = true;
        }

      // running it immediately afterwards with the same input/output should cause no changes.
      if (manualResult != CONFLICT && (CHANGED == tempResult || different))
        {
        cerr << "Result varied after second call" << endl;
        cerr << "first";
        print(manualChildren, manualOutput, kind);
        cerr << "second";
        print(tempChildren, tempOutput, kind);
        error(kind, initialChildren, initialOutput, autoChildren, autoOutput, manualChildren, manualOutput);
        }
      for (int i = 0; i < (int) initialChildren.size(); i++)
        {
        delete tempChildren[i];
        }

      // find if the values have changed. If they've changed, ensure they follow the lattice.
      bool changed = false;
      if (!FixedBits::equals(initialOutput, manualOutput))
        {
        if (!FixedBits::updateOK(initialOutput, manualOutput))
          {
          // BAD UPDATE.
          cerr << "bad update." << "Value changed not according to the lattice" << endl;
          print(manualChildren, manualOutput, kind);
          error(kind, initialChildren, initialOutput, autoChildren, autoOutput, manualChildren, manualOutput);

          }
        changed = true;
        }

      for (int i = 0; i < (int) initialChildren.size(); i++)
        {
        if (!FixedBits::equals(*manualChildren[i], *initialChildren[i]))
          {
          assert(FixedBits::updateOK(*initialChildren[i],*manualChildren[i]));
          changed = true;
          }
        }

      // if they've changed the status should have changed.
      if (changed && manualResult != NOT_IMPLEMENTED)
        {
        // if changed then manualResult should be conflict or changed.
        if (!(CHANGED == manualResult || CONFLICT == manualResult))
          {
          cerr << "result should be changed or conflict" << endl;
          error(kind, initialChildren, initialOutput, autoChildren, autoOutput, manualChildren, manualOutput);
          }
        }

      // If the status is changed. Then there should have been a change.
      if (CHANGED == manualResult)
        {
        assert(changed);
        }

      bool first = maxPrecision(autoChildren, autoOutput, kind, beev);
      beev->ClearAllTables();

      if (debug_printAll)
        {
        cout << "initial: ";
        print(initialChildren, initialOutput, kind);

        cout << "  manual:";
        print(manualChildren, manualOutput, kind);

        cout << "    auto:";
        print(autoChildren, autoOutput, kind);
        }

      // if we failed on the first time through. Then the generated equation is impossible.
      // For example: (= (bvand 1 0) 1)
      // If it's bad, then the transfer function should have reported it.

      if (first)
        {
        if (!imprecise && CONFLICT != manualResult)
          {
          cerr << "TRANSFER FUNCTION DIDN'T DETECT IT WAS BAD" << endl;
          cerr << "result was:" << manualResult << endl;
          error(kind, initialChildren, initialOutput, autoChildren, autoOutput, manualChildren, manualOutput);
          }
        }
      else
        {
        // if it wasn't bad, then the transfer function shouldn't say it is.
        if (CONFLICT == manualResult)
          {
          cerr << "TRANSFER FUNCTION REPORTED CONFLICT WHEN THERE WAS NONE." << endl;
          cerr << "result was:" << manualResult << endl;
          error(kind, initialChildren, initialOutput, autoChildren, autoOutput, manualChildren, manualOutput);
          }

        if (imprecise)
          {
          if (!FixedBits::in(autoOutput, manualOutput))
            {
            error(kind, initialChildren, initialOutput, autoChildren, autoOutput, manualChildren, manualOutput);
            }
          }
        else if (!FixedBits::equals(autoOutput, manualOutput))
          error(kind, initialChildren, initialOutput, autoChildren, autoOutput, manualChildren, manualOutput);

        for (int i = 0; i < (int) initialChildren.size(); i++)
          {
          if (imprecise)
            {
            if (!FixedBits::in(*(autoChildren[i]), *(manualChildren[i])))
              error(kind, initialChildren, initialOutput, autoChildren, autoOutput, manualChildren, manualOutput);
            }
          else if (!FixedBits::equals(*(autoChildren[i]), *(manualChildren[i])))
            error(kind, initialChildren, initialOutput, autoChildren, autoOutput, manualChildren, manualOutput);
          }
        }
      for (int i = 0; i < (int) initialChildren.size(); i++)
        {
        delete manualChildren[i];
        delete autoChildren[i];
        }
    }

// Exhaustively generate all the bitpatterns for the number of inputs.
// For each input compare the solver's result to the manual Transfer functions result.
    void
    exhaustive(Result
    (*transfer)(vector<FixedBits*>&, FixedBits&), Signature signature)
    {
      cout << "trying:" << signature.kind << endl;

      assert(signature.maxInputWidth >0);
      if (signature.inputType == BOOL_TYPE)
        assert(signature.maxInputWidth =1);

      for (int length = 1; length <= signature.maxInputWidth; length++)
        {
        int totalLength;
        int resultLength;

        vector<FixedBits*> children;
        for (int i = 0; i < signature.numberOfInputs; i++)
          {
          children.push_back(new FixedBits(length, signature.inputType == BOOL_TYPE));
          }

        if (signature.resultType == BOOL_TYPE)
          {
          resultLength = 1;
          totalLength = (length * signature.numberOfInputs + 1);
          }

        else
          {
          resultLength = length;
          totalLength = (length * (signature.numberOfInputs + 1));

          }

          {

          for (long j = 0; j < pow(3, totalLength); j++)
            {
            FixedBits output(resultLength, signature.resultType == BOOL_TYPE);

            int current = j;

            for (int k = 0; k < totalLength; k++)
              {
              if (k < resultLength)
                {
                setV(output, k, current % 3);
                }
              else
                {
                int id = (k - resultLength) / length;
                setV(*(children[id]), k - resultLength - (id * length), current % 3);
                }
              current /= 3;
              }

            if (isDivide && children[1]->containsZero())
              {
              continue;
              }

            checkEqual(children, output, transfer, signature.kind, signature.imprecise);
            }
          }

        for (unsigned i = 0; i < children.size(); i++)
          delete children[i];
        }
    }

// Random.
    void
    runSomeRandom(Result
    (*transfer)(vector<FixedBits*>&, FixedBits&), const Kind kind, const vector<FixedBits*> late, FixedBits out)
    {
      const int PROBABILITY_OF_SETTING = 5;

      cout << "Running Random:" << kind << endl;
      assert(late.size() ==2);
      MTRand mtrand;

      vector<FixedBits*> children;

      for (int i = 0; i < 2000; i++)
        {
        children.clear();
        FixedBits a = FixedBits::createRandom(out.getWidth(), PROBABILITY_OF_SETTING, mtrand);
        children.push_back(&a);
        FixedBits b = FixedBits::createRandom(out.getWidth(), PROBABILITY_OF_SETTING, mtrand);
        children.push_back(&b);
        FixedBits output = FixedBits::createRandom(out.getWidth(), PROBABILITY_OF_SETTING, mtrand);

        checkEqual(children, output, transfer, kind, false);
        cout << ".";
        }
      return;
    }

// Exhaustively generate all the bitpatterns for the number of inputs.
// For each input compare the solver's result to the manual Transfer functions result.
    void
    newExhaustive(Result
    (*transfer)(vector<FixedBits*>&, FixedBits&), const Kind kind, const vector<FixedBits*> temp,
        const FixedBits tempOutput)
    {
      cout << "trying:" << kind << endl;

      int numberOfInputParams = temp.size();
      assert(numberOfInputParams >0);

      vector<int> lengths;
      int totalLength = 0;
      vector<FixedBits*> children;
      for (int i = 0; i < numberOfInputParams; i++)
        {
        children.push_back(new FixedBits(temp[i]->getWidth(), temp[i]->isBoolean()));
        totalLength += children[i]->getWidth();
        lengths.push_back(children[i]->getWidth());
        }

      int resultLength = tempOutput.getWidth();
      FixedBits output(resultLength, tempOutput.isBoolean());

      lengths.push_back(resultLength);
      totalLength += resultLength;

      for (long j = 0; j < pow(3, totalLength); j++)
        {
        int current = j;

        int id = 0;
        int usedUp = 0;

        for (int k = 0; k < totalLength; k++)
          {
          if (k < resultLength)
            {
            setV(output, k, current % 3);
            }
          else
            {
            int working = (k - resultLength - usedUp);
            if (working == lengths[id])
              {
              usedUp += lengths[id];
              id++;
              working = 0;
              }
            setV(*(children[id]), working, current % 3);
            }
          current /= 3;
          }

        checkEqual(children, output, transfer, kind, false);
        }

      for (unsigned i = 0; i < children.size(); i++)
        delete children[i];

    }

  }

}

Result
multiply(vector<FixedBits*>& children, FixedBits& output)
{
  return bvMultiplyBothWays(children, output, simplifier::constantBitP::beev, 0);
}

Result
unsignedDivide(vector<FixedBits*>& children, FixedBits& output)
{
  return bvUnsignedDivisionBothWays(children, output, simplifier::constantBitP::beev);
}

Result
signedDivide(vector<FixedBits*>& children, FixedBits& output)
{
  return bvSignedDivisionBothWays(children, output, simplifier::constantBitP::beev);
}

Result
signedRemainder(vector<FixedBits*>& children, FixedBits& output)
{
  return bvSignedRemainderBothWays(children, output, simplifier::constantBitP::beev);
}

Result
signedModulus(vector<FixedBits*>& children, FixedBits& output)
{
  return bvSignedModulusBothWays(children, output, simplifier::constantBitP::beev);
}

Result
unsignedModulus(vector<FixedBits*>& children, FixedBits& output)
{
  return bvUnsignedModulusBothWays(children, output, simplifier::constantBitP::beev);
}

struct D
{
  int a, b, c;
  void
  print()
  {
    cerr << a << " " << b << " " << c << endl;
  }
};

void
exhaustively_check(const int bitwidth)
{
  vector<D> list;

  const Kind kind = BVPLUS;
  const int numberOfInputParams = 2;
  Result (*transfer)(vector<FixedBits*>&, FixedBits&) = &bvAddBothWays;

  assert(numberOfInputParams >0);
  const int mask = pow(2, bitwidth) - 1;


  // Create all the possible inputs, and apply the function.
  for (int i = 0; i < pow(2, bitwidth * numberOfInputParams); i++)
    {
    D d;
    d.a = i & mask;
    d.b = (i >> bitwidth) & mask;
    d.c = (d.a + d.b) & mask;
    list.push_back(d);
    }

  FixedBits a(bitwidth, false);
  FixedBits b(bitwidth, false);
  vector<FixedBits*> temp;
  temp.push_back(&a);
  temp.push_back(&b);
  FixedBits tempOutput(bitwidth, false);

  vector<int> lengths;
  int totalLength = 0;
  vector<FixedBits*> children;
  for (int i = 0; i < numberOfInputParams; i++)
    {
    children.push_back(new FixedBits(temp[i]->getWidth(), temp[i]->isBoolean()));
    totalLength += children[i]->getWidth();
    lengths.push_back(children[i]->getWidth());
    }

  int resultLength = tempOutput.getWidth();
  FixedBits output(resultLength, tempOutput.isBoolean());

  lengths.push_back(resultLength);
  totalLength += resultLength;

  const int to_iterate = pow(3, totalLength);
  for (long j = 0; j < to_iterate; j++)
    {
    int current = j;

    if (j% 5000 == 0)
      cerr << j << " of " << to_iterate << endl;

    int id = 0;
    int usedUp = 0;

    for (int k = 0; k < totalLength; k++)
      {
      if (k < resultLength)
        {
        setV(output, k, current % 3);
        }
      else
        {
        int working = (k - resultLength - usedUp);
        if (working == lengths[id])
          {
          usedUp += lengths[id];
          id++;
          working = 0;
          }
        setV(*(children[id]), working, current % 3);
        }
      current /= 3;
      }

    FixedBits c_a(bitwidth, false), c_b(bitwidth, false), c_o(bitwidth, false);
    bool first = true;
    for (int j = 0; j < list.size(); j++)
      {
      D& d = list[j];
      if (children[0]->unsignedHolds(d.a) && children[1]->unsignedHolds(d.b) && output.unsignedHolds(d.c))
        {
        if (first)
          {
          c_a = FixedBits::fromUnsignedInt(bitwidth, d.a);
          c_b = FixedBits::fromUnsignedInt(bitwidth, d.b);
          c_o = FixedBits::fromUnsignedInt(bitwidth, d.c);
          first = false;
          }
        else
          {
           c_a.join(d.a);
           c_b.join(d.b);
           c_o.join(d.c);
          }
        }
      }

    Result r = transfer(children, output);
    if (r == CONFLICT)
      {
      assert(first);
      }
    else
      {
      assert(FixedBits::equals(*children[0],c_a));
      assert(FixedBits::equals(*children[1],c_b));
      assert(FixedBits::equals(output,c_o));
      }
    }

}

int
main(void)
{
  beev = new BEEV::STPMgr();
  beev->UserFlags.disableSimplifications();

  Cpp_interface interface(*beev, beev->defaultNodeFactory);
  interface.startup();
  srand(time(NULL));
  BEEV::ParserBM = beev;

  #ifdef NDEBUG
    cerr << "needs debug please.";
    exit(1);
  #endif


  const int bits = 4;
  exhaustively_check(bits);


  if (true)
    {
    Signature signature;
    signature.resultType = VALUE_TYPE;
    signature.inputType = VALUE_TYPE;
    signature.numberOfInputs = 2;
    signature.imprecise = true;
    signature.kind = BVMULT;
    signature.maxInputWidth = 2;
    exhaustive(&multiply, signature);

    signature.maxInputWidth = bits;
    signature.imprecise = true;
    exhaustive(&multiply, signature);

    signature.imprecise = true;
    isDivide = true;
    signature.kind = SBVMOD;
    exhaustive(&signedModulus, signature);
    signature.kind = SBVREM;
    exhaustive(&signedRemainder, signature);
    signature.kind = BVMOD;
    exhaustive(&unsignedModulus, signature);
    signature.kind = BVDIV;
    exhaustive(&unsignedDivide, signature);
    signature.kind = SBVDIV;
    exhaustive(&signedDivide, signature);
    isDivide = false;
    }

    { //TWO INPUT. (value, value)->value
    Signature signature;

    signature.resultType = VALUE_TYPE;
    signature.inputType = VALUE_TYPE;
    signature.maxInputWidth = bits;
    signature.numberOfInputs = 2;

    // BVADD
    signature.kind = BVPLUS;
    exhaustive(&bvAddBothWays, signature);

    // BVRIGHTSHIFT
    signature.kind = BVRIGHTSHIFT;
    exhaustive(&bvRightShiftBothWays, signature);

    // BVaritmeticRIGHTSHIFT
    signature.kind = BVSRSHIFT;
    exhaustive(&bvArithmeticRightShiftBothWays, signature);

    // BVLEFTSHIFT
    signature.kind = BVLEFTSHIFT;
    exhaustive(&bvLeftShiftBothWays, signature);

    // BVSUB
    signature.kind = BVSUB;
    exhaustive(&bvSubtractBothWays, signature);

    // BVXOR.
    signature.kind = BVXOR;
    exhaustive(&bvXorBothWays, signature);

    // BVAND.
    signature.kind = BVAND;
    exhaustive(&bvAndBothWays, signature);

    // BVOR
    signature.kind = BVOR;
    exhaustive(&bvOrBothWays, signature);
    }

  // n Params at most. (Bool,Bool) -> Bool
    {
    Signature signature;
    signature.resultType = BOOL_TYPE;
    signature.inputType = BOOL_TYPE;
    signature.numberOfInputs = 2;
    signature.maxInputWidth = 1;
    signature.kind = IMPLIES;
    exhaustive(&bvImpliesBothWays, signature);
    }

  // One input (value -> value)
    {
    Signature signature;
    signature.resultType = VALUE_TYPE;
    signature.inputType = VALUE_TYPE;
    signature.maxInputWidth = bits;
    signature.numberOfInputs = 1;

    // BVUMINUS
    signature.kind = BVUMINUS;
    exhaustive(&bvUnaryMinusBothWays, signature);

    // BVNOT --- Same function as NOT.
    signature.kind = BVNEG;
    exhaustive(&bvNotBothWays, signature);

    }

  // bvConcat
    {
    if (bits >= 2)
      for (int i = 1; i < bits; i++)
        {
        vector<FixedBits*> children;
        FixedBits a(bits - i, false);
        FixedBits b(i, false);

        children.push_back(&a);
        children.push_back(&b);
        FixedBits output(bits, false);
        newExhaustive(&bvConcatBothWays, BVCONCAT, children, output);
        }
    }

  // bvSignedComparisons
    {
    Signature signature;
    signature.resultType = BOOL_TYPE;
    signature.inputType = VALUE_TYPE;
    signature.numberOfInputs = 2;
    signature.maxInputWidth = bits;
    signature.kind = BVSLT;
    exhaustive(&bvSignedLessThanBothWays, signature);
    signature.kind = BVSLE;
    exhaustive(&bvSignedLessThanEqualsBothWays, signature);
    signature.kind = BVSGT;
    exhaustive(&bvSignedGreaterThanBothWays, signature);
    signature.kind = BVSGE;
    exhaustive(&bvSignedGreaterThanEqualsBothWays, signature);
    }

  // bvUnSignedComparisons
    {
    Signature signature;
    signature.resultType = BOOL_TYPE;
    signature.inputType = VALUE_TYPE;
    signature.numberOfInputs = 2;
    signature.maxInputWidth = bits;
    signature.kind = BVGT;
    exhaustive(&bvGreaterThanBothWays, signature);
    signature.kind = BVLT;
    exhaustive(&bvLessThanBothWays, signature);
    signature.kind = BVLE;
    exhaustive(&bvLessThanEqualsBothWays, signature);
    signature.kind = BVGE;
    exhaustive(&bvGreaterThanEqualsBothWays, signature);
    }

  // BVEQ.
    {
    Signature signature;
    signature.kind = EQ;
    signature.resultType = BOOL_TYPE;
    signature.inputType = VALUE_TYPE;
    signature.maxInputWidth = bits;
    signature.numberOfInputs = 2;
    exhaustive(&bvEqualsBothWays, signature);
    }

  // 2 Params at most. (Bool,Bool) -> Bool
    {
    Signature signature;
    signature.resultType = BOOL_TYPE;
    signature.inputType = BOOL_TYPE;
    signature.maxInputWidth = 1;
    signature.numberOfInputs = 2;

    // IFF.
    signature.kind = IFF;
    exhaustive(&bvEqualsBothWays, signature);

    // XOR.
    signature.kind = XOR;
    exhaustive(&bvXorBothWays, signature);
    }

  // n Params at most. (Bool,Bool) -> Bool
    {
    Signature signature;
    signature.resultType = BOOL_TYPE;
    signature.inputType = BOOL_TYPE;
    signature.maxInputWidth = 1;

    // AND.
    signature.kind = AND;
    signature.numberOfInputs = 3;
    exhaustive(&bvAndBothWays, signature);
    signature.numberOfInputs = 2;
    exhaustive(&bvAndBothWays, signature);

    // OR.
    signature.kind = OR;
    signature.numberOfInputs = 3;
    exhaustive(&bvOrBothWays, signature);
    signature.numberOfInputs = 2;
    exhaustive(&bvOrBothWays, signature);
    }

  // NOT
    {
    Signature signature;
    signature.kind = NOT;
    signature.resultType = BOOL_TYPE;
    signature.inputType = BOOL_TYPE;
    signature.numberOfInputs = 1;
    signature.maxInputWidth = 1;
    exhaustive(&bvNotBothWays, signature);
    }

  // Term ITE.
    {
    vector<FixedBits*> children;
    FixedBits a(1, true);
    FixedBits b(bits, false);
    FixedBits c(bits, false);

    children.push_back(&a);
    children.push_back(&b);
    children.push_back(&c);
    FixedBits output(bits, false);
    newExhaustive(&bvITEBothWays, ITE, children, output);
    }

  // Propositional ITE.
    {
    vector<FixedBits*> children;
    FixedBits a(1, true);
    FixedBits b(1, true);
    FixedBits c(1, true);

    children.push_back(&a);
    children.push_back(&b);
    children.push_back(&c);
    FixedBits output(1, true);
    newExhaustive(&bvITEBothWays, ITE, children, output);
    }

    {
    if (bits >= 2)
      {
      FixedBits output(bits, false);
      for (int i = 1; i < bits; i++)
        {
        vector<FixedBits*> children;
        FixedBits a(i, false);
        children.push_back(&a);
        children.push_back(&a); // To type check needs a second argument. Ignored.

        newExhaustive(&bvZeroExtendBothWays, BVZX, children, output);
        newExhaustive(&bvSignExtendBothWays, BVSX, children, output);
        }
      }
    }

  // Add had a defect effecting bithWidth > 90.
  // Shifting had a defect effecting bitWidth > 64.
    {
    vector<FixedBits*> children;
    FixedBits a(150, false);
    FixedBits b(150, false);

    children.push_back(&a);
    children.push_back(&b);
    FixedBits output(150, false);
    runSomeRandom(&bvAndBothWays, BVAND, children, output);
    runSomeRandom(&bvRightShiftBothWays, BVRIGHTSHIFT, children, output);
    runSomeRandom(&bvLeftShiftBothWays, BVLEFTSHIFT, children, output);
    runSomeRandom(&bvAddBothWays, BVPLUS, children, output);
    runSomeRandom(&bvOrBothWays, BVOR, children, output);
    }

  cout << "Done" << endl;

  return 1;
}

