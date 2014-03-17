/*
 * g++ -DEXT_HASH_MAP tree.cpp -I ../../c_interface -L ../../lib -lstp -o cc
 */

#include "/home/taking/stp/timking_expt/AST/AST.h"

#include <stdio.h>
#include "c_interface.h"

#include <stdlib.h>
#include <vector>
#include <unistd.h>

VC vc;
vector<Expr> gen_forms;
vector<Expr> gen_arrays;
vector<Expr> gen_terms;

//unsigned TERMS;
//unsigned FORMULAS;
bool o0,o1,o2,o3,o4,o5,o6,o7,o8;

unsigned MIN;
unsigned MAX;

using namespace BEEV;

unsigned T;
int trand(){
  T++;
  return rand();
}

Expr randconst(){
  return vc_bvConstExprFromInt(vc, 32, rand());
}
#define BUF_LENGTH 63 
char buf[] = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_";
void shufflebuf(){
  unsigned N = BUF_LENGTH;
  unsigned i;
  while(N--){
    i = trand()%BUF_LENGTH;
    char c = buf[i];
    buf[i] = buf[N]; 
    buf[N] = c;
  }
}

void nonsense(){
 gen_arrays.push_back(NULL);
}

char* rstr(unsigned len){
  char *ret = (char *)calloc(sizeof( char),len+1);
  shufflebuf();
  unsigned i = 0;
  while(len--){
    ret[i++] = buf[trand()%BUF_LENGTH];
  }
  return ret;
}
Expr randvar(){
  char *rname = rstr(trand()%11+6);
  
  Expr e = vc_varExpr1(vc,rname,0,32);
  free(rname);
  return e;
}
bool isTerm(Expr e){
  return BEEV::BITVECTOR_TYPE == ((ASTNode*)e)->GetType(); 
}
bool isFormula(Expr e){
  return BEEV::BOOLEAN_TYPE == ((ASTNode*)e)->GetType(); 
}

Expr selectTerm(){
  unsigned i = trand()%gen_terms.size();
  return gen_terms[i];
}
Expr selectForm(){
  unsigned i = trand()%gen_forms.size();
  return gen_forms[i];
}
Expr selectArray(){
  unsigned i = trand()%gen_arrays.size();
  return gen_arrays[i];
}
Expr randarrayvar(){
  char *rname = rstr(trand()%11+6);
  Expr e = vc_varExpr1(vc,rname,32,32);
  free(rname);
  return e;
}
Expr randarray(){
  unsigned r = trand()%11;
  if(0 == gen_arrays.size())
    r = 0;
  switch(r){
    case 0:
      return randarrayvar();
    default:
      return vc_writeExpr(vc,selectArray(),selectTerm(),selectTerm());
  }
}
Expr randbvterm(){
  unsigned r = trand()%11;
  Expr expr, left, right;

  left = selectTerm();
  if(1 == r){
    right = left;
    left =  selectArray();
  }else if(r > 2 ){
    right = selectTerm();
  }
  switch(r){
    case 0:
      expr = vc_bvNotExpr(vc, left);
      break;
    case 1:
      expr = vc_bvUMinusExpr(vc, left);
      break;
    case 2:
      expr = vc_readExpr(vc, left, right);
      break;
    case 3:
      expr = vc_bvPlusExpr(vc, 32, left, right);
      break;
    case 4:  
      expr = vc_bvMinusExpr(vc, 32, left, right);
      break;
    case 5:
      expr = vc_bvModExpr(vc, 32, left, right);
      break;
    case 6:  
      expr = vc_sbvDivExpr(vc, 32, left, right);
      break;
    case 7:
      expr = vc_sbvModExpr(vc, 32, left, right);
      break;
    case 8:
      expr = vc_bvOrExpr(vc, left, right);
      break;
    case 9:  
      expr = vc_bvAndExpr(vc, left, right);
      break;
    case 10:
      expr = vc_bvXorExpr(vc, left, right);
      break;
    default:
      expr = NULL;
      break;
  }
  return expr;
}
Expr randbvform(){
  unsigned r = trand()%10;

  Expr expr,left,right;
  left = selectTerm();
  if(r > 0 )
    right = selectTerm();

  switch(r){
    case 0:
      expr = vc_bvBoolExtract(vc, left, rand()%(vc_getBVLength(vc,left)));
      break;
    case 1:  
      expr = vc_bvLeExpr(vc, left, right);
      break;
    case 2:  
      expr = vc_bvGtExpr(vc, left, right);
      break;
    case 3:  
      expr = vc_bvGeExpr(vc, left, right);
      break;
    case 4:
      expr = vc_eqExpr(vc, left, right);
      break;
    case 5:  
      expr = vc_sbvLtExpr(vc, left, right);
      break;
    case 6:  
      expr = vc_sbvLeExpr(vc, left, right);
      break;
    case 7:  
      expr = vc_sbvGtExpr(vc, left, right);
      break;
    case 8:  
      expr = vc_sbvGeExpr(vc, left, right);
      break;
    case 9:  
      expr = vc_bvLtExpr(vc, left, right);
      break;
    default:
      expr = NULL;
      break;
  }
  return expr;
}
Expr randform(){
  unsigned r = rand()%6;

  Expr expr,left,right;
  left = selectForm();
  if(r != 0){
    right = selectForm();
  }

  switch(r){
    case 0:
      expr = vc_notExpr(vc, left);
      break;
    case 1:
      expr = vc_andExpr(vc, left, right);
      break;
    case 2:  
      expr = vc_orExpr(vc, left, right);
      break;
    case 3:  
      expr = vc_impliesExpr(vc, left, right);
      break;
    case 4:  
      expr = vc_iffExpr(vc, left, right);
      break;
    case 5:
      expr = vc_iteExpr(vc,selectForm(), left, right);
      break;
    default:
      expr = NULL;
      break;
  }
  return expr;
}
void printExpr(Expr x){
  ASTNode q = *((ASTNode*)x);
  q.LispPrint(cout,0);
}
void printArray(vector<Expr>& v){
  for( unsigned i=0;i<v.size();i++)
    printExpr(v[i]);
}
void cleanUp(vector<Expr>& v){
  while(!v.empty()){
    Expr elem = v.back();
    v.pop_back();
    vc_DeleteExpr(elem);
  }
}    
void setUpAST(){
  unsigned N;
  N = trand()%(MAX-MIN)+MIN;
  for( unsigned i=0;i<N;i++)
    gen_terms.push_back(randconst());
  
  N = trand()%((MAX-MIN)/10)+(MIN/10);
  for( unsigned i=0;i<N;i++)
    gen_terms.push_back(randvar());

  gen_arrays.push_back(randarray());
  
  N = trand()%(MAX-MIN)+MIN;
  for( unsigned i=0;i<N;i++){
    if(i%10 == 0){
      gen_arrays.push_back(randarray());
    }else{
      Expr e = randbvterm();
      gen_terms.push_back(e);
      if(vc_getBVLength(vc,e) > 32){
        gen_terms.push_back(vc_bvExtract(vc, e, 32, 0));
      }else if(32 > vc_getBVLength(vc,e)){ 
        gen_terms.push_back(vc_bv32LeftShiftExpr(vc, 0,e));
      }
    }  
  }

  N = trand()%(MAX-MIN)+MIN;
  for( unsigned i=0;i<N;i++)
    gen_forms.push_back(randbvform());

  gen_forms.push_back(vc_falseExpr(vc));
  gen_forms.push_back(vc_trueExpr(vc));

  N = trand()%(MAX-MIN)+MIN;
  for( unsigned i=0;i<N;i++)
    gen_forms.push_back(randform());
}

void runVC(){
  printf("\n**********\n");

  vc = vc_createValidityChecker();
  vc_setFlags('n');
  vc_setFlags('d');
  vc_setFlags('p');
  vc_setFlags('v');
  
  setUpAST();

  if(o0){
    printArray(gen_terms);
    printArray(gen_arrays);
    printArray(gen_forms);
  }

  Expr head = gen_forms.back();
  gen_forms.pop_back();

  if(o2){
    printExpr(head);  
  }
  if(o3){
    cout<<endl;
    cout<<vc_query(vc, head)<<endl;
  }
  if(o4){
    cleanUp(gen_terms);
    cleanUp(gen_arrays);
    cleanUp(gen_forms);
  }
  if(o5){
    printExpr(head); 
    printf("\n");
  }  
  if(o6){
    cout<<endl;
    cout<<vc_query(vc, head)<<endl;
  }
  if(o7)
    vc_DeleteExpr(head);
  if(o8)
    vc_Destroy(vc);

}

int main (int argc, char **argv) {
   int c;
   unsigned N;
   unsigned seed = 0;
   o0=o1=o2=o3=o4=o5=o6=o7=o8=false;

   MAX = 30;
   MIN = 10;
   T = 0;

   extern char *optarg;
   
   while ((c = getopt (argc, argv, "t:s:m:M:012345678::")) != -1){
      switch (c)
      {
        case '0':
	  o0 = true;
	  break;
        case '1':
	  o1 = true;
	  break;
        case '2':
	  o2 = true;
	  break;
        case '3':
	  o3 = true;
	  break;
        case '4':
	  o4 = true;
	  break;
        case '5':
	  o5 = true;
	  break;
	case '6':
	  o6 = true;
	  break;
	case '7':
	  o7 = true;
	  break;
	case '8':
	  o8 = true;
	  break;
	case 's':
	  seed = atoi(optarg);
	  break;
	case 'M':
	  MAX = atoi(optarg);
	  break;
	case 'm':
	  MIN = atoi(optarg);
	  break;
	case 't':
	  T = atoi(optarg);
	  break;
	default:
	  abort();
     }	  
  }
  srand(seed);
  unsigned i = T;
  while(i--){
    rand();
  }
  N = trand()%999+1;
  N = trand()%10+1;
//  N = 2;
  while(N--){
    runVC();
    gen_terms.clear();
    gen_arrays.clear();
    gen_forms.clear();
  }
}
