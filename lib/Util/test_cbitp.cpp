// Runs some of the constant bit propagators and compares their results against the maximally precise transformer.
// Those that aren't maximally precise have the super-set relationship checked.

// NB: This is testing code that I don't expect anyone else will use, it's hard to follow what it does!


#include "stp/Simplifier/constantBitP/ConstantBitPropagation.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_TransferFunctions.h"
#include "stp/Simplifier/constantBitP/ConstantBitP_MaxPrecision.h"
#include "stp/Simplifier/constantBitP/FixedBits.h"
#include "stp/Simplifier/constantBitP/MersenneTwister.h"
#include <cstdlib>
#include <ctime>
#include <cmath>
#include "stp/AST/AST.h"

#include "stp/STPManager/STPManager.h"
#include "stp/ToSat/AIG/ToSATAIG.h"
#include "stp/Sat/MinisatCore.h"
#include "stp/STPManager/STP.h"
#include "stp/cpp_interface.h"

#include "stp/Util/StopWatch.h"
#include "stp/Util/Relations.h"
#include "stp/UtilBBAsProp.h"
#include "stp/Util/Functions.h"

using simplifier::constantBitP::FixedBits;
using namespace simplifier::constantBitP;


namespace simplifier
{
  namespace constantBitP
  {

    using namespace BEEV;

    STPMgr * mgr;
    bool isDivide = false;

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

#include "checkEqual.include"

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

            Detail d;
            checkEqual(children, output, transfer, signature.kind, signature.imprecise,d);
            }
          }

        for (unsigned i = 0; i < children.size(); i++)
          delete children[i];
        }
    }

// Random.
    void
    runSomeRandom(Result
    (*transfer)(vector<FixedBits*>&, FixedBits&), const Kind kind, int prob)
    {
      vector<FixedBits*> children;

      int conflicts =0;
      int initial =0;
      int transferC =0;
      int max =0;

      int count = 1000;
      const int width =32;

      Relations r(count,width,kind, mgr, prob);

      Stopwatch s;
      list<Relations::Relation>::iterator it = r.relations.begin();
      while(it != r.relations.end())
        {
        Relations::Relation& rel = *it;
        FixedBits& a = rel.a;
        FixedBits& b = rel.b;
        FixedBits& output = rel.output;

        children.clear();
        children.push_back(&a);
        children.push_back(&b);

        Detail d;
        bool imprecise = false;
        if (kind == BVDIV || kind == BVMULT || kind == BVMOD || kind == SBVDIV || kind == SBVREM)
          imprecise = true;
        checkEqual(children, output, transfer, kind, imprecise,d);

        assert(!d.conflict);

        initial += d.initial;
        transferC += d.transferFixed;
        max += d.maxFixed;

        it++;
        }

      assert(max >= transferC);
      assert(transferC >= initial);

      int percent = 100* ((float)transferC - initial) / (max - initial);
      if ((max-initial) ==0)
        percent = 100;
      clock_t t = s.stop2();
      cerr.setf(ios::fixed);
      cerr << "% Count" << count << " prob" << prob << " bits" << width << endl;
      cerr << "&" << setprecision(2) << (float(t) / CLOCKS_PER_SEC) << "s";
      cerr << "&" << initial << "&" << transferC << "&" << max << "&" << percent << "\\%\n" ;

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

        Detail d;
        checkEqual(children, output, transfer, kind, false,d);
        }

      for (unsigned i = 0; i < children.size(); i++)
        delete children[i];

    }

  }

}

Result
multiply(vector<FixedBits*>& children, FixedBits& output)
{
  return bvMultiplyBothWays(children, output, simplifier::constantBitP::mgr, 0);
}

Result
unsignedDivide(vector<FixedBits*>& children, FixedBits& output)
{
  return bvUnsignedDivisionBothWays(children, output, simplifier::constantBitP::mgr);
}


Result
signedDivide(vector<FixedBits*>& children, FixedBits& output)
{
  return bvSignedDivisionBothWays(children, output, simplifier::constantBitP::mgr);
}

Result
signedRemainder(vector<FixedBits*>& children, FixedBits& output)
{
  return bvSignedRemainderBothWays(children, output, simplifier::constantBitP::mgr);
}

Result
signedModulus(vector<FixedBits*>& children, FixedBits& output)
{
  return bvSignedModulusBothWays(children, output, simplifier::constantBitP::mgr);
}

Result
unsignedModulus(vector<FixedBits*>& children, FixedBits& output)
{
  return bvUnsignedModulusBothWays(children, output, simplifier::constantBitP::mgr);
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
exhaustively_check(const int bitwidth, Kind k, Result (*transfer)(vector<FixedBits*>&, FixedBits&), int (*op)(int a, int b))
{
  vector<D> list;

  int transferBad =0;
  int BBBad =0;

  const int numberOfInputParams = 2;

  int resultLength = (is_Form_kind(k) ) ? 1:bitwidth;

  const int input_mask = pow(2, bitwidth) - 1;
  const int output_mask = resultLength ==1 ? 1: (pow(2, bitwidth)-1);

  // Create all the possible inputs, and apply the function.
  for (int i = 0; i < pow(2, bitwidth * numberOfInputParams); i++)
    {
    D d;
    d.a = i & input_mask;
    d.b = (i >> bitwidth) & input_mask;
    d.c = op(d.a,d.b) & output_mask;
    list.push_back(d);
    }

  FixedBits a(bitwidth, false);
  FixedBits b(bitwidth, false);
  vector<FixedBits*> temp;
  temp.push_back(&a);
  temp.push_back(&b);


  FixedBits tempOutput(resultLength, false);

  vector<int> lengths;
  int totalLength = 0;
  vector<FixedBits*> children;
  for (int i = 0; i < numberOfInputParams; i++)
    {
    children.push_back(new FixedBits(temp[i]->getWidth(), temp[i]->isBoolean()));
    totalLength += children[i]->getWidth();
    lengths.push_back(children[i]->getWidth());
    }


  FixedBits output(resultLength, tempOutput.isBoolean());

  lengths.push_back(resultLength);
  totalLength += resultLength;

  FixedBits empty(bitwidth, false);
  FixedBits c_a(bitwidth, false), c_b(bitwidth, false), c_o(resultLength, false);

  BBAsProp BBP(k,mgr,bitwidth);

  const int to_iterate = pow(3, totalLength);
  for (long j = 0; j < to_iterate; j++)
    {
    int current = j;

    //if (j% 100000 == 0)
    //  cerr << j << " of " << to_iterate << endl;

    int id = 0;
    int usedUp = 0;

    for (int k_it = 0; k_it < totalLength; k_it++)
      {
      if (k_it < resultLength)
        {
        setV(output, k_it, current % 3);
        }
      else
        {
        int working = (k_it - resultLength - usedUp);
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

    bool max_conflict = true;
    for (int j = 0; j < list.size(); j++)
      {
      D& d = list[j];
      if (children[0]->unsignedHolds(d.a) && children[1]->unsignedHolds(d.b) && output.unsignedHolds(d.c))
        {
        if (max_conflict)
          {
          c_a.fromUnsigned(d.a);
          c_b.fromUnsigned(d.b);
          c_o.fromUnsigned(d.c);
          max_conflict = false;
          }
        else
          {
           c_a.join(d.a);
           c_b.join(d.b);
           c_o.join(d.c);
          }
        }
      }

    const int initialFixed = children[0]->countFixed() + children[1]->countFixed() + output.countFixed();
    const int maxFixed = c_a.countFixed() + c_b.countFixed() + c_o.countFixed();


    BBP.toAssumptions(*children[0], *children[1], output);
    bool bb_conflict = !BBP.unitPropagate();
    const int BBFixed = BBP.fixedCount();

    bool transfer_conflict = (transfer(children, output) == CONFLICT) ;
    const int transferFixed = children[0]->countFixed() + children[1]->countFixed() + output.countFixed();


    if (transfer_conflict && !max_conflict)
      FatalError("!!");
    if (bb_conflict && !max_conflict)
      FatalError("~~");

    if (!max_conflict &&  !bb_conflict)
    {
        assert( maxFixed >= BBFixed);
        assert( initialFixed <= BBFixed);
    }

    //cerr << "----";
   // cerr << *children[0] << *children[1] << output << endl;
  //  cerr << c_a << c_b << c_o << endl;

    if (!max_conflict && !transfer_conflict)
      {
        assert( maxFixed >= transferFixed);
        assert( initialFixed <= transferFixed);
      }

    assert( initialFixed <= maxFixed);

    if (max_conflict && !transfer_conflict)
      transferBad++;
    else if (max_conflict && !bb_conflict)
        BBBad++;
    else if (max_conflict)
      {

      }
    else if (transferFixed != maxFixed)
      transferBad++;
    else if (BBFixed != maxFixed)
        BBBad++;


    if (!transfer_conflict && (k != BVMULT) && (k != BVDIV) && (k != BVMOD) )
      {
      if(!FixedBits::equals(*children[0],c_a))
        FatalError("First");
      if(!FixedBits::equals(*children[1],c_b))
        FatalError("Second");
      if(!FixedBits::equals(output,c_o))
        FatalError("Third");
      }
    }
  for (int i=0; i < children.size();i++)
    delete children[i];

  cerr.setf(ios::fixed);
  cerr << setprecision(1);
  cerr  << "& " <<     100 *(transferBad/ (float)to_iterate) << "\\%";
  cerr  << "& " <<     100 *(BBBad/ (float)to_iterate) << "\\%";
  transferBad= 0; BBBad = 0;

}

void
go(Result (*transfer)(vector<FixedBits*>&, FixedBits&), const Kind kind)
{
    runSomeRandom(transfer, kind, 1 );
    runSomeRandom(transfer, kind, 5 );
    runSomeRandom(transfer, kind, 50 );
    cerr << "\\\\";
}

void g()
{
        FixedBits a(3,false);
        FixedBits b(3,false);
        a.setFixed(0,true);
        a.setValue(0,true);

        b.setFixed(1,true);
        b.setValue(1,true);

        vector<FixedBits*> c;
        c.push_back(&a);
        c.push_back(&b);

        FixedBits output(3,false);
        output.setFixed(0,true);
        output.setValue(0,true);
        output.setFixed(2,true);
        output.setValue(2,true);


        multiply(c,output);
}


int
main(void)
{
  BEEV::STPMgr stp;
  mgr = &stp;
  mgr->UserFlags.disableSimplifications();
  mgr->UserFlags.division_by_zero_returns_one_flag  = true;
  Cpp_interface interface(*mgr);
  srand(time(NULL));


  // Add had a defect effecting bithWidth > 90.
  // Shifting had a defect effecting bitWidth > 64.

  ostream& output = cerr;

  const int bits = 5;

  if (false)
    {
    output << "signed greater than equals" << endl;
    go(&bvSignedGreaterThanEqualsBothWays, BVSGE);

    output << "unsigned less than" << endl;
    go(&bvLessThanEqualsBothWays, BVLT);

    output << "equals" << endl;
    go(&bvEqualsBothWays, EQ);

    output << "bit-vector xor" << endl;
    go(&bvXorBothWays, BVXOR);

    output << "bit-vector or" << endl;
      go(&bvOrBothWays, BVOR);

      output << "bit-vector and" << endl;
      go(&bvAndBothWays, BVAND);

      output << "right shift" << endl;
      go(&bvRightShiftBothWays, BVRIGHTSHIFT);

      output << "left shift" << endl;
      go(&bvLeftShiftBothWays, BVLEFTSHIFT);

      output << "arithmetic shift" << endl;
      go(&bvArithmeticRightShiftBothWays, BVSRSHIFT);

      output << "addition" << endl;
      go(&bvAddBothWays, BVPLUS);

      output << "multiplication" << endl;
      go(&multiply, BVMULT);
      output << "unsigned division" << endl;
      go(&unsignedDivide, BVDIV);

      output << "unsigned remainder" << endl;
      go(&unsignedModulus, BVMOD);

      output << "signed division" << endl;
      go(&signedDivide, SBVDIV);

      output << "signed remainder" << endl;
      go(&signedRemainder, SBVREM);

      exit(1);
    }


  const int exhaustive_bits = 5;

  Functions f;
  cerr << "% Automatically generated!!" << endl;
  cerr << "\\begin{figure} \\centering" <<endl;
  cerr << "\\begin{tabular}{|c|";

  for (int i = 1; i <= exhaustive_bits; i++)
    cerr << "c|c|";

  cerr << "} \\hline" << endl;

  cerr << "Operation";

  for (int i = 1; i <= exhaustive_bits; i++)
    cerr << "& \\multicolumn{2}{c|}{"<< i <<" bits}";
  cerr << "\\\\ \\hline" << endl;



  for (int i = 1; i <= exhaustive_bits; i++)
    cerr << "& Prop& BB";

  cerr << "\\\\ \\hline" << endl;

  std::list<Functions::Function>::iterator it = f.l.begin();
  while (it != f.l.end())
    {
      Functions::Function& f = *it;
      cerr << f.name << endl;
      for (int i = 1; i <= exhaustive_bits; i++)
        exhaustively_check(i, f.k,  f.fn, f.op);
      cerr << "\\\\ " << endl;
      it++;
    }
cerr << "\\hline" ;

  cerr << "\\end{tabular}" <<endl;
  cerr <<  "\\caption{Percentage of all the assignments at different bit-widths. Where the Bitblasted encoding and the propagators did missed bits to fix, or missed a conflicting assignment.}" << endl;
  cerr << "\\end{figure}" <<endl;


exit(1);


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

    // BVaritmeticRIGHTSHIFT
    signature.kind = BVSRSHIFT;
    exhaustive(&bvArithmeticRightShiftBothWays, signature);

    // BVXOR.
    signature.kind = BVXOR;
    exhaustive(&bvXorBothWays, signature);
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


  cout << "Done" << endl;

  return 1;
}

