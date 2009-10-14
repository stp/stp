/* ############################################################################### */
/* # STP/CVC code generator for constraint-based ILP RNA prediction method from: */
/* # */
/* # "Prediction of RNA secondary structure with pseudoknots using
   # interger programming" Poolsap, Kato, Akutsu, BMC Bioinformatics
   # 2009 */
/* # */
/* # */
/* # --17aug09 : cwo  */
/* ############################################################################### */

/* ############################################################################### */
/* # Parameter rename (paper->this paper): */
/* #     e_kl      =>   E   , E_idx   */
/* #     x_i       =>   X   , X_idx   */
/* #     x_ij      =>   X2  , X2_idx   */
/* #     y_i       =>   Y   , Y_idx   */
/* #     y_ij      =>   Y2  , Y2_idx   */
/* #     z_x_ij    =>   ZX  , ZX_idx   */
/* #     z_y_ij    =>   ZY  , ZY_idx  */
/* #     L_x_i     =>   LX  , LX_idx  */
/* #     L_y_i     =>   LY  , LY_idx  */
/* #     R_x_i     =>   RX  , RX_idx  */
/* #     R_y_i     =>   RY  , RY_idx  */
/* #     L_t_ij    =>   LT  , LT_idx  */
/* #     R_t_ij    =>   RT  , RT_idx  */
/* ############################################################################### */

// ############ Compilation instructions ##############
//
// g++ -m32 -DEXT_HASH_MAP biosat-rna.cpp -IPATH_TO_c_interface.h -LPATH_TO_STP_LIBRARY -lstp -lm -o biosat-rna.out
//
//

#include <iostream>
#include <stdio.h>
#include <stdlib.h>
#include <cstring>
#include <cmath>
#include <ext/hash_set>
#include "c_interface.h"

#define E_BITS 16
#define TOT_E_BITS 24
#define UNKNOWN_CONST 6

using namespace std;
using namespace __gnu_cxx;

struct eqint
{
  bool operator()(int s1, int s2) const {
	return (s1 == s2);
  }	
};

int req_bits(int dec_num) {
  int num_bits = (int)ceil(log(dec_num)/log(2));
  //printf("the required number of bits is: %d\n", num_bits);
  return num_bits;
} //End of req_bits()

int get_pairtype(char * seq, int i, int j) {
  int seq_len = strlen(seq);
  if (i>=seq_len or j>=seq_len or i<0 or j<0) {
    //printf("DEBUG: get_pairtype(%s,%d,%d)=-1\n" % (seq,i,j));
    return -1;
  }

  if (seq[i]=='A' and seq[j]=='U') {
    //printf("DEBUG: get_pairtype(%s,%d,%d)=0\n" % (seq,i,j));
    return 0;
  } 
  else if (seq[i]=='C' and seq[j]=='G') {
    //printf("DEBUG: get_pairtype(%s,%d,%d)=1\n" % (seq,i,j));
    return 1;
  }
  else if (seq[i]=='G' and seq[j]=='C') {
    //printf("DEBUG: get_pairtype(%s,%d,%d)=2\n" % (seq,i,j));
    return 2;
  }
  else if (seq[i]=='G' and seq[j]=='U') {
    //printf("DEBUG: get_pairtype(%s,%d,%d)=3\n" % (seq,i,j));
    return 3;
  }
  else if (seq[i]=='U' and seq[j]=='G') {
    //printf("DEBUG: get_pairtype(%s,%d,%d)=4\n" % (seq,i,j));
    return 4;
  }
  else if (seq[i]=='U' and seq[j]=='A') {
    //printf("DEBUG: get_pairtype(%s,%d,%d)=5\n" % (seq,i,j));
    return 5;
  }
  else {
    //printf("DEBUG: get_pairtype(%s,%d,%d)=-1\n" % (seq,i,j));
    return -1;
  }
} //End of get_pairtype()

/*************************************************************
 * MAIN
 *
 *
 *
 *
 *************************************************************/
int main(int argc, char** argv) {
  if(argc < 2 || argc > 3) {
    printf("Usage: biosat <sequence length> <energy lower bound>\n");
    printf("Usage to print input back: biosat -b \n");
    exit(-1);
  }

  VC vc = vc_createValidityChecker();
  if('-' == argv[1][0] && 'b' == argv[1][1]) {
    vc_printVarDecls(vc);
    vc_printAsserts(vc,0);
    vc_printQuery(vc);
    exit(0);
  }
  
  //Alpha: Equivalent of Sigma in the paper
  float alpha = 0.7;

  //inputs: the RNA sequence
  char * seq  = argv[1];
  int seq_len = strlen(seq);
  //printf("The sequence length is : %d \n", seq_len);

  //inputs: STP needs to find a sequence whose energy is greater than
  //'energy_bound'
  int min_sol_energy = atoi(argv[2]);
  printf("The min energy sought is : %d \n", min_sol_energy);
  int idx2_bits_width = req_bits(seq_len*seq_len);
  int idx3_bits_width = req_bits(seq_len*seq_len*UNKNOWN_CONST*UNKNOWN_CONST);

  hash_set<int, hash<int>, eqint> Ex_blacklist(10000);
  hash_set<int, hash<int>, eqint> Ey_blacklist(10000);


  int E_table[36];
  E_table[0]  = 11;
  E_table[1]  = 21;
  E_table[2]  = 22;
  E_table[3]  = 14;
  E_table[4]  = 9;
  E_table[5]  = 6;
  E_table[6]  = 21;
  E_table[7]  = 24;
  E_table[8]  = 33;
  E_table[9]  = 21;
  E_table[10] = 21;
  E_table[11] = 14;
  E_table[12] = 22;
  E_table[13] = 33;
  E_table[14] = 34;
  E_table[15] = 25;
  E_table[16] = 24;
  E_table[17] = 15;
  E_table[18] = 14;
  E_table[19] = 21;
  E_table[20] = 25;
  E_table[21] = 13;
  E_table[22] = 13;
  E_table[23] = 5;
  E_table[24] = 9;
  E_table[25] = 21;
  E_table[26] = 24;
  E_table[27] = 13;
  E_table[28] = 13;
  E_table[29] = 10;
  E_table[30] = 6;
  E_table[31] = 14;
  E_table[32] = 15;
  E_table[33] = 5;
  E_table[34] = 10;
  E_table[35] = 3;


  vc_setFlags(vc,'n');
  vc_setFlags(vc,'d');
  vc_setFlags(vc,'p');
  vc_setFlags(vc,'r');
  vc_setFlags(vc,'a');
  vc_setFlags(vc,'w');
  vc_setFlags(vc,'y');
    
  //Parameteric Boolean X
  Expr X = vc_varExpr1(vc, "X", 0, 0);
  //Parameteric Boolean Y
  Expr Y = vc_varExpr1(vc, "Y", 0, 0);
  
  //final_Ex Array
  Expr Final_Ex = vc_varExpr1(vc, "Final_Ex", idx2_bits_width, E_BITS);
  //Final_Ey Array
  Expr Final_Ey = vc_varExpr1(vc, "Final_Ey", idx2_bits_width, E_BITS);

//   ########### (0) ##########
//   fd.write("%%%%%%%%%% (0) %%%%%%%%%%\n");
  
//   fd.write("X, Y : BOOLEAN;\n");
//   for i in range(0,seq_len):
//     for j in range(0,seq_len):
//       ij = i*seq_len + j;
//       ji = j*seq_len + i;
      
//       if(dec2bin(ij,idx2_bits) != dec2bin(ji,idx2_bits)):
//         fd.write("ASSERT(X(%s) <=> X(%s));\n" % (dec2bin(ij,idx2_bits), dec2bin(ji,idx2_bits)) );
      
//       if(dec2bin(ij,idx2_bits) != dec2bin(ji,idx2_bits)):
//         fd.write("ASSERT(Y(%s) <=> Y(%s));\n" % (dec2bin(ij,idx2_bits), dec2bin(ji,idx2_bits)) );      


  //########### (0) ##########
  for(int i=0; i < seq_len; i++) {
    for(int j = 0; j < seq_len; j++) {
      int ij = i*seq_len + j;
      int ji = j*seq_len + i;
      if(ij != ji) {
	Expr ijexpr = vc_bvConstExprFromInt(vc, idx2_bits_width, ij);
	Expr jiexpr = vc_bvConstExprFromInt(vc, idx2_bits_width, ji);
	Expr Xij = vc_paramBoolExpr(vc, X, ijexpr);
	Expr Xji = vc_paramBoolExpr(vc, X, jiexpr);
	Expr Yij = vc_paramBoolExpr(vc, Y, ijexpr);
	Expr Yji = vc_paramBoolExpr(vc, Y, jiexpr);
      
	Expr XijXji = vc_iffExpr(vc, Xij, Xji);
	Expr YijYji = vc_iffExpr(vc, Yij, Yji);
	vc_assertFormula(vc, XijXji);
	vc_assertFormula(vc, YijYji);
      }
    }
  }//End of constraints 0

//   ########### (1) ##########
//   fd.write("%%%%%%%%%% (1) %%%%%%%%%%\n");
//   for i in range(0,seq_len):
//     for j in range(0,seq_len):
//       k = get_pairtype(seq,i,j);
//       l = get_pairtype(seq,i+1,j-1);
//       ij = i*seq_len + j;
//       ji = j*seq_len + i;
//       ij2 = (i+1)*seq_len + (j-1);
//       kl = k*6 + l;
//       if (i==j or ij2==ji):
//         Ex_blacklist.add(ij);
//         fd.write("ASSERT(NOT(X(%s)));\n" % (dec2bin(ij,idx2_bits)) );
//         continue;
//       if (k<0 or l<0 or i==(seq_len-1) or j==0):
//         Ex_blacklist.add(ij);
//         continue;
//       fd.write("ASSERT((X(%s) AND X(%s)) => final_Ex[%s]=%s);\n" % \
//                (dec2bin(ij,idx2_bits), dec2bin(ij2,idx2_bits), dec2bin(ij,idx2_bits), dec2bin(E_table[kl],e_bits)) );
//       fd.write("ASSERT((NOT(X(%s)) OR NOT(X(%s))) => final_Ex[%s]=%s);\n" % \
//                (dec2bin(ij,idx2_bits), dec2bin(ij2,idx2_bits), dec2bin(ij,idx2_bits), dec2bin(0,e_bits)) );


  //########### (1) ##########
  for(int i=0; i<seq_len; i++) {
    for(int j=0; j<seq_len; j++) {
      int k = get_pairtype(seq,i,j);
      int l = get_pairtype(seq,i+1,j-1);
      int ij = i*seq_len + j;
      int ji = j*seq_len + i;
      int ij2 = (i+1)*seq_len + (j-1);
      int kl = k*6 + l;

      Expr ijexpr = vc_bvConstExprFromInt(vc, idx2_bits_width, ij);
      Expr Xij = vc_paramBoolExpr(vc, X, ijexpr);
      Expr NotXij = vc_notExpr(vc, Xij);

      if (i==j || ij2==ji) {
	Ex_blacklist.insert(ij);
	//Python: fd.write("ASSERT(NOT(X(%s)));\n" % (dec2bin(ij,idx2_bits)) );
	vc_assertFormula(vc, NotXij);
	continue;
      }
      
      if(k<0 or l<0 or i==(seq_len-1) or j==0) {
	Ex_blacklist.insert(ij);
	continue;
      }

      //Python:fd.write("ASSERT((X(%s) AND X(%s)) => Final_Ex[%s]=%s);\n" %
      //Python: (dec2bin(ij,idx2_bits), dec2bin(ij2,idx2_bits), dec2bin(ij,idx2_bits), dec2bin(E_table[kl],e_bits)) );
      Expr ij2expr               = vc_bvConstExprFromInt(vc, idx2_bits_width, ij2);
      Expr Xij2                  = vc_paramBoolExpr(vc, X, ij2expr);
      Expr Final_Ex_ij           = vc_readExpr(vc, Final_Ex, ijexpr);
      Expr E_tablekl             = vc_bvConstExprFromInt(vc, E_BITS, E_table[kl]);
      Expr Final_Ex_ij_E_tablekl = vc_eqExpr(vc, Final_Ex_ij, E_tablekl);
      Expr Xij_and_Xij2          = vc_andExpr(vc, Xij, Xij2);
      Expr implied_energy_1      = vc_impliesExpr(vc, Xij_and_Xij2, Final_Ex_ij_E_tablekl);

      //Python:fd.write("ASSERT((NOT(X(%s)) OR NOT(X(%s))) => Final_Ex[%s]=%s);\n" %
      //Python:(dec2bin(ij,idx2_bits), dec2bin(ij2,idx2_bits), dec2bin(ij,idx2_bits), dec2bin(0,e_bits)) );
      Expr NotXij2               = vc_notExpr(vc, Xij2);
      Expr NotXij_or_NotXij2     = vc_orExpr(vc,NotXij,NotXij2);
      Expr Zero_bits             = vc_bvConstExprFromInt(vc, E_BITS, 0);
      Expr Final_Ex_ij_Zero_bits = vc_eqExpr(vc,Final_Ex_ij,Zero_bits);
      Expr implied_energy_2      = vc_impliesExpr(vc, NotXij_or_NotXij2, Final_Ex_ij_Zero_bits);

      vc_assertFormula(vc, implied_energy_1);
      vc_assertFormula(vc, implied_energy_2);
    } //End of inner For
  }//End of outer For. End of constraints 1
  

//   ########### (2) ##########
//   fd.write("%%%%%%%%%% (2) %%%%%%%%%%\n");
//   for i in range(0,seq_len):
//     for j in range(0,seq_len):
//       k = get_pairtype(seq,i,j);
//       l = get_pairtype(seq,i+1,j-1);
//       ij = i*seq_len + j;
//       ji = j*seq_len + i;
//       ij2 = (i+1)*seq_len + (j-1);
//       kl = k*6 + l;
//       if (i==j or ij2==ji):
//         Ey_blacklist.add(ij);
//         fd.write("ASSERT(NOT(Y(%s)));\n" % (dec2bin(ij,idx2_bits)) );
//         continue;
//       if (k<0 or l<0 or i==(seq_len-1) or j==0):
//         Ey_blacklist.add(ij);
//         continue;
//       fd.write("ASSERT((Y(%s) AND Y(%s)) => final_Ey[%s]=%s);\n" % \
//                (dec2bin(ij,idx2_bits), dec2bin(ij2,idx2_bits), dec2bin(ij,idx2_bits), dec2bin(int(alpha*E_table[kl]),e_bits)) );
//       fd.write("ASSERT((NOT(Y(%s)) OR NOT(Y(%s))) => final_Ey[%s]=%s);\n" % \
//                (dec2bin(ij,idx2_bits), dec2bin(ij2,idx2_bits), dec2bin(ij,idx2_bits), dec2bin(0,e_bits)) );


  //########### (2) ##########
  for(int i=0; i<seq_len; i++) {
    for(int j=0; j<seq_len; j++) {
      int k = get_pairtype(seq,i,j);
      int l = get_pairtype(seq,i+1,j-1);
      int ij = i*seq_len + j;
      int ji = j*seq_len + i;
      int ij2 = (i+1)*seq_len + (j-1);
      int kl = k*6 + l;

      Expr ijexpr = vc_bvConstExprFromInt(vc, idx2_bits_width, ij);
      Expr Yij = vc_paramBoolExpr(vc, Y, ijexpr);
      Expr NotYij = vc_notExpr(vc, Yij);

      if (i==j || ij2==ji) {
	Ex_blacklist.insert(ij);
	//Python: fd.write("ASSERT(NOT(Y(%s)));\n" % (dec2bin(ij,idx2_bits)) );
	vc_assertFormula(vc, NotYij);
	continue;
      }
      
      if(k<0 or l<0 or i==(seq_len-1) or j==0) {
	Ex_blacklist.insert(ij);
	continue;
      }

      //Python: fd.write("ASSERT((Y(%s) AND Y(%s)) => final_Ey[%s]=%s);\n" %
      //Python: (dec2bin(ij,idx2_bits), dec2bin(ij2,idx2_bits), dec2bin(ij,idx2_bits), dec2bin(int(alpha*E_table[kl]),e_bits)) );
      Expr ij2expr               = vc_bvConstExprFromInt(vc, idx2_bits_width, ij2);
      Expr Yij2                  = vc_paramBoolExpr(vc, Y, ij2expr);
      Expr Final_Ey_ij           = vc_readExpr(vc, Final_Ey, ijexpr);
      Expr E_tablekl             = vc_bvConstExprFromInt(vc, E_BITS, int(alpha*E_table[kl]));
      Expr Final_Ey_ij_E_tablekl = vc_eqExpr(vc, Final_Ey_ij, E_tablekl);
      Expr Yij_and_Yij2          = vc_andExpr(vc, Yij, Yij2);
      Expr implied_energy_1      = vc_impliesExpr(vc, Yij_and_Yij2, Final_Ey_ij_E_tablekl);

      //Python:fd.write("ASSERT((NOT(Y(%s)) OR NOT(Y(%s))) => Final_Ey[%s]=%s);\n" %
      //Python:(dec2bin(ij,idx2_bits), dec2bin(ij2,idx2_bits), dec2bin(ij,idx2_bits), dec2bin(0,e_bits)) );
      Expr NotYij2               = vc_notExpr(vc, Yij2);
      Expr NotYij_or_NotYij2     = vc_orExpr(vc,NotYij,NotYij2);
      Expr Zero_bits             = vc_bvConstExprFromInt(vc, E_BITS, 0);
      Expr Final_Ey_ij_Zero_bits = vc_eqExpr(vc,Final_Ey_ij,Zero_bits);
      Expr implied_energy_2      = vc_impliesExpr(vc, NotYij_or_NotYij2, Final_Ey_ij_Zero_bits);

      vc_assertFormula(vc, implied_energy_1);
      vc_assertFormula(vc, implied_energy_2);
    } //End of inner For
  }//End of outer For. End of constraints 2



// #   ########### (3) ##########
// #   fd.write("%%%%%%%%%% (3) %%%%%%%%%%\n");
// #   for i in range(0,seq_len):
// #     for j in range(0,seq_len):
// #       for k in range(0,seq_len):
// #         if (i==j or j==k or i==k):
// #           continue;
// #         ji = j*seq_len + i;
// #         ik = i*seq_len + k;
// #           fd.write("ASSERT (NOT(X_%s) OR NOT(X_%s));\n" % (dec2bin(ji,idx2_bits), dec2bin(ik,idx2_bits)) );
// #           fd.write("ASSERT (NOT(Y_%s) OR NOT(Y_%s));\n" % (dec2bin(ji,idx2_bits), dec2bin(ik,idx2_bits)) );
// #           fd.write("ASSERT (NOT(Y_%s) OR NOT(X_%s));\n" % (dec2bin(ji,idx2_bits), dec2bin(ik,idx2_bits)) );
// #           fd.write("ASSERT (NOT(X_%s) OR NOT(Y_%s));\n" % (dec2bin(ji,idx2_bits), dec2bin(ik,idx2_bits)) );

  for(int i=0; i<seq_len; i++) {
    for(int j=0; j<seq_len; j++) {
      for(int k=0; k<seq_len; k++) {
	if(i==j || j==k || i==k)
	  continue;
	int ji = j*seq_len + i;
        int ik = i*seq_len + k;

	Expr jiexpr           = vc_bvConstExprFromInt(vc, idx2_bits_width, ji);
	Expr ikexpr           = vc_bvConstExprFromInt(vc, idx2_bits_width, ik);
	Expr NotXji           = vc_notExpr(vc,vc_paramBoolExpr(vc, X, jiexpr));
	Expr NotXik           = vc_notExpr(vc,vc_paramBoolExpr(vc, X, ikexpr));
	Expr NotYji           = vc_notExpr(vc,vc_paramBoolExpr(vc, Y, jiexpr));
	Expr NotYik           = vc_notExpr(vc,vc_paramBoolExpr(vc, Y, ikexpr));

	Expr NotXji_or_NotXik = vc_orExpr(vc, NotXji, NotXik);
	vc_assertFormula(vc, NotXji_or_NotXik);

	Expr NotYji_or_NotYik = vc_orExpr(vc, NotYji, NotYik);
	vc_assertFormula(vc, NotYji_or_NotYik);

	Expr NotYji_or_NotXik = vc_orExpr(vc, NotYji, NotXik);
	vc_assertFormula(vc, NotYji_or_NotXik);

	Expr NotXji_or_NotYik = vc_orExpr(vc, NotXji, NotYik);
	vc_assertFormula(vc, NotXji_or_NotYik);
      }
    }
  } //End of Constraint 3
  
//   ########### (4) ##########
//   fd.write("%%%%%%%%%% (4) %%%%%%%%%%\n");
//   for i in range(0,seq_len):
//     for j in range(0,seq_len):
//       if (i==j):
//         continue;
//       ij = (i*seq_len) + j;
//       fd.write("ASSERT(NOT(X(%s)) OR NOT(Y(%s)));\n" % (dec2bin(ij,idx2_bits), dec2bin(ij,idx2_bits)) );


  for(int i=0; i<seq_len; i++) {
    for(int j=0; j<seq_len; j++) {
      if(i==j)
	continue;
      int ij = i*seq_len + j;
      Expr ijexpr = vc_bvConstExprFromInt(vc, idx2_bits_width, ij);
      Expr NotXij = vc_notExpr(vc, vc_paramBoolExpr(vc, X, ijexpr));
      Expr NotYij = vc_notExpr(vc, vc_paramBoolExpr(vc, Y, ijexpr));
      
      Expr NotXij_or_NotYij = vc_orExpr(vc, NotXij, NotYij);
      vc_assertFormula(vc, NotXij_or_NotYij);
    }
  } //End of Constraint 4


//    ########### (5) ##########
//    fd.write("%%%%%%%%%% (5) %%%%%%%%%%\n");
//    for i in range(0,seq_len):
//      for j in range(0,seq_len):
//        for k in range(0,seq_len):
//          for l in range(0,seq_len):
//            if (i<k and k<j and j<l):
//              ij = i*seq_len + j;
//              kl = k*seq_len + l;
//              fd.write("ASSERT (NOT(X_%s) OR NOT(X_%s));\n" % (dec2bin(ij,idx2_bits),dec2bin(kl,idx2_bits))); 


  for(int i=0; i<seq_len; i++) {
    for(int j=0; j<seq_len; j++) {
      for(int k=0; k<seq_len; k++) {
	for(int l=0; l<seq_len; l++) {
	  if(i<k && k<j && j<l) {
	    int ij = i*seq_len + j;
	    int kl = k*seq_len + l;
	
	    Expr ijexpr = vc_bvConstExprFromInt(vc, idx2_bits_width, ij);
	    Expr NotXij = vc_notExpr(vc, vc_paramBoolExpr(vc, X, ijexpr));

	    Expr klexpr = vc_bvConstExprFromInt(vc, idx2_bits_width, kl);
	    Expr NotXkl = vc_notExpr(vc, vc_paramBoolExpr(vc, X, klexpr));
          
	    Expr NotXij_or_NotXkl = vc_orExpr(vc, NotXij, NotXkl);
	    vc_assertFormula(vc, NotXij_or_NotXkl);
	  }
	}
      }
    }
  }//End of Constraint (5)

//    ########### (6) ##########
//    fd.write("%%%%%%%%%% (6) %%%%%%%%%%\n");
//    for i in range(0,seq_len):
//      for j in range(0,seq_len):
//        for k in range(0,seq_len):
//          for l in range(0,seq_len):
//            if (i<k and k<j and j<l):
//              ij = i*seq_len + j;
//              kl = k*seq_len + l;
//              fd.write("ASSERT (NOT(Y_%s) OR NOT(Y_%s));\n" % (dec2bin(ij,idx2_bits),dec2bin(kl,idx2_bits))); 

  for(int i=0; i<seq_len; i++) {
    for(int j=0; j<seq_len; j++) {
      for(int k=0; k<seq_len; k++) {
	for(int l=0; l<seq_len; l++) {
	  if(i<k && k<j && j<l) {
	    int ij = i*seq_len + j;
	    int kl = k*seq_len + l;
	
	    Expr ijexpr = vc_bvConstExprFromInt(vc, idx2_bits_width, ij);
	    Expr NotYij = vc_notExpr(vc, vc_paramBoolExpr(vc, Y, ijexpr));

	    Expr klexpr = vc_bvConstExprFromInt(vc, idx2_bits_width, kl);
	    Expr NotYkl = vc_notExpr(vc, vc_paramBoolExpr(vc, Y, klexpr));
          
	    Expr NotYij_or_NotYkl = vc_orExpr(vc, NotYij, NotYkl);
	    vc_assertFormula(vc, NotYij_or_NotYkl);
	  }
	}
      }
    }
  }//End of Constraint (6)


  //////////////// OBJECTIVE FUNCTION ////////////////////////////////////

  int e_bitdiff = TOT_E_BITS - E_BITS;
  Expr padding  = vc_bvConstExprFromInt(vc, e_bitdiff, 0);
  int count     = 0;
  Expr bvplus_terms[100000];
  for(int i=0; i<seq_len; i++) {
    for(int j=0; j<seq_len; j++) {
      int ij = i*seq_len + j;
      if((Ex_blacklist.find(ij) == Ex_blacklist.end()) &&
	 (Ey_blacklist.find(ij) == Ey_blacklist.end())) {
	Expr ijexpr = vc_bvConstExprFromInt(vc, idx2_bits_width, ij);
	Expr Final_Ex_ij = vc_bvConcatExpr(vc, padding, vc_readExpr(vc,Final_Ex,ijexpr));
	Expr Final_Ey_ij = vc_bvConcatExpr(vc, padding, vc_readExpr(vc,Final_Ey,ijexpr));
	bvplus_terms[count++] = Final_Ex_ij;
	bvplus_terms[count++] = Final_Ey_ij;
      }
      else if((Ex_blacklist.find(ij) != Ex_blacklist.end()) &&
	      (Ey_blacklist.find(ij) == Ey_blacklist.end())) {
	Expr ijexpr = vc_bvConstExprFromInt(vc, idx2_bits_width, ij);
	Expr Final_Ex_ij = vc_bvConcatExpr(vc, padding, vc_readExpr(vc,Final_Ex,ijexpr));
	bvplus_terms[count++] = Final_Ex_ij;
      }
      else if((Ex_blacklist.find(ij) == Ex_blacklist.end()) &&
	      (Ey_blacklist.find(ij) != Ey_blacklist.end())) {
	Expr ijexpr = vc_bvConstExprFromInt(vc, idx2_bits_width, ij);
	Expr Final_Ey_ij = vc_bvConcatExpr(vc, padding, vc_readExpr(vc,Final_Ey,ijexpr));
	bvplus_terms[count++] = Final_Ey_ij;
      }
    } //End of inner for
  }//End of bvplus

  
  Expr total_energy = vc_varExpr1(vc, "total_energy", 0, TOT_E_BITS);
  Expr energy_addedup = vc_bvPlusExprN(vc, TOT_E_BITS, bvplus_terms, count);
  Expr final_eq = vc_eqExpr(vc, total_energy, energy_addedup);
  
  Expr min_sol_energy_expr = vc_bvConstExprFromInt(vc, TOT_E_BITS, min_sol_energy);
  vc_assertFormula(vc, vc_bvGeExpr(vc, total_energy, min_sol_energy_expr));

  vc_query(vc, vc_falseExpr(vc));
} //End of Main()
