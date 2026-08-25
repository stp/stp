#ifndef MODULE_BIT_VECTOR
#define MODULE_BIT_VECTOR
/*****************************************************************************/
/*  AUTHOR:                                                                  */
/*****************************************************************************/
/*                                                                           */
/*    Steffen Beyer                                                          */
/*    mailto:sb@engelschall.com                                              */
/*    http://www.engelschall.com/u/sb/download/                              */
/*                                                                           */
/*****************************************************************************/
/*  COPYRIGHT:                                                               */
/*****************************************************************************/
/*                                                                           */
/*    Copyright (c) 1995 - 2004 by Steffen Beyer.                            */
/*    All rights reserved.                                                   */
/*                                                                           */
/*****************************************************************************/
/*  LICENSE:                                                                 */
/*****************************************************************************/
/*                                                                           */
/*    This library is free software; you can redistribute it and/or          */
/*    modify it under the terms of the GNU Library General Public            */
/*    License as published by the Free Software Foundation; either           */
/*    version 2 of the License, or (at your option) any later version.       */
/*                                                                           */
/*    This library is distributed in the hope that it will be useful,        */
/*    but WITHOUT ANY WARRANTY; without even the implied warranty of         */
/*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU       */
/*    Library General Public License for more details.                       */
/*                                                                           */
/*    You should have received a copy of the GNU Library General Public      */
/*    License along with this library; if not, write to the                  */
/*    Free Software Foundation, Inc.,                                        */
/*    59 Temple Place, Suite 330, Boston, MA 02111-1307 USA                  */
/*                                                                           */
/*    or download a copy from                                                */
/*    http://www.gnu.org/licenses/old-licenses/lgpl-2.0.en.html              */
/*                                                                           */
/*****************************************************************************/


/*****************************************************************************/
/*  MODULE NAME:  BitVector.h                           MODULE TYPE:  (adt)  */
/*****************************************************************************/
/*  MODULE IMPORTS:                                                          */
/*****************************************************************************/
#include <stdlib.h>                                 /*  MODULE TYPE:  (sys)  */
#include <limits.h>                                 /*  MODULE TYPE:  (sys)  */
#include <string.h>                                 /*  MODULE TYPE:  (sys)  */
#include <ctype.h>                                  /*  MODULE TYPE:  (sys)  */
/*****************************************************************************/
/*  MODULE INTERFACE:                                                        */
/*****************************************************************************/

namespace CONSTANTBV {

// STP builds with -fvisibility=hidden, but this API has to stay exported:
// inline code in STP's public headers calls it -- ASTBVConst's hasher,
// equality and destructor all do -- so a translation unit outside libstp that
// emits one of those inlines needs to be able to bind to it.
#if defined(__GNUC__) || defined(__clang__)
#pragma GCC visibility push(default)
#endif

#ifdef __cplusplus
  extern "C" {
    typedef bool boolean;
#else
    typedef enum { false = (0!=0), true = (0==0) } boolean;
#endif

    typedef enum {
      ErrCode_Ok = 0,    /* everything went allright                       */   
      ErrCode_Type,      /* types word and size_t have incompatible sizes  */
      ErrCode_Bits,      /* bits of word and sizeof(word) are inconsistent */
      ErrCode_Word,      /* size of word is less than 16 bits              */
      ErrCode_Long,      /* size of word is greater than size of long      */
      ErrCode_Powr,      /* number of bits of word is not a power of two   */
      ErrCode_Loga,      /* error in calculation of logarithm              */   
      ErrCode_Null,      /* unable to allocate memory                      */   
      ErrCode_Indx,      /* index out of range                             */
      ErrCode_Ordr,      /* minimum > maximum index                        */
      ErrCode_Size,      /* bit vector size mismatch                       */
      ErrCode_Pars,      /* input string syntax error                      */
      ErrCode_Ovfl,      /* numeric overflow error                         */
      ErrCode_Same,      /* operands must be distinct                      */
      ErrCode_Expo,      /* exponent must be positive                      */
      ErrCode_Zero       /* division by zero error                         */
    } ErrCode;


    /* ===> MISCELLANEOUS BASIC FUNCTIONS: <=== */
    unsigned char * BitVector_Error(ErrCode error);     /* return string for err code */
    ErrCode         BitVector_Boot (void);              /* 0 = ok, 1..7 = error */
    unsigned int    BitVector_Size(unsigned int bits);  /* bit vector size (# of words)  */
    unsigned int    BitVector_Mask(unsigned int bits);  /* bit vector mask (unused bits) */
    
    /* ===> CLASS METHODS: <=== */

    /* ===> CONSTRUCTOR METHODS: <=== */
    unsigned int *  BitVector_Create      (unsigned int bits, boolean clear);                /* malloc */
    unsigned int ** BitVector_Create_List (unsigned int bits, boolean clear, unsigned int count);
    unsigned int *  BitVector_Resize      (unsigned int * oldaddr, unsigned int bits);       /* realloc */
    unsigned int *  BitVector_Clone       (unsigned int * addr);                             /* make exact duplicate */
    unsigned int *  BitVector_Concat      (unsigned int * X, unsigned int * Y);              /* return concatenation */

    /* ===> DESTRUCTOR METHODS: <=== */
    void    BitVector_Dispose             (unsigned char * string);                     /* string */
    void    BitVector_Destroy             (unsigned int * addr);                        /* bitvec */
    void    BitVector_Destroy_List        (unsigned int * * list, unsigned int count);  /* list   */

    /* ===> OBJECT METHODS: <=== */

    /* ===> bit vector hash: */
    size_t  BitVector_Hash                (unsigned int * X);

    /* ===> bit vector copy function: */
    void    BitVector_Copy                (unsigned int * X, unsigned int * Y);              /* X := Y   */

    /* ===> bit vector initialization: */
    void    BitVector_Empty               (unsigned int * addr);                      /* X = {}  */
    void    BitVector_Fill                (unsigned int * addr);                      /* X = ~{} */
    void    BitVector_Flip                (unsigned int * addr);                      /* X = ~X  */

    /* ===> miscellaneous functions: */
    
    /* ===> bit vector interval operations and functions: */
    void    BitVector_Interval_Fill       (unsigned int * addr, unsigned int lower, unsigned int upper);
    
    void    BitVector_Interval_Copy       (unsigned int * X, unsigned int * Y, 
                                           unsigned int Xoffset, unsigned int Yoffset, unsigned int length);

    /* ===> bit vector test functions: */
    boolean BitVector_is_empty            (unsigned int * addr);                         /* X == {} ?   */
    boolean BitVector_is_full             (unsigned int * addr);                         /* X == ~{} ?  */
    boolean BitVector_equal               (unsigned int * X, unsigned int * Y);          /* X == Y ?    */
    signed int   BitVector_Lexicompare    (unsigned int * X, unsigned int * Y);          /* X <,=,> Y ? */
    signed int   BitVector_Compare        (unsigned int * X, unsigned int * Y);          /* X <,=,> Y ? */
    
    /* ===> bit vector string conversion functions: */
    unsigned char * BitVector_to_Hex      (unsigned int * addr);
    ErrCode BitVector_from_Hex            (unsigned int * addr, unsigned char * string);
    unsigned char * BitVector_to_Bin      (unsigned int * addr);
    ErrCode BitVector_from_Bin            (unsigned int * addr, unsigned char * string);
    unsigned char * BitVector_to_Dec      (unsigned int * addr);
    ErrCode BitVector_from_Dec            (unsigned int * addr, unsigned char * string);
    
    /* ===> bit vector bit operations, functions & tests: */
    void    BitVector_Bit_Off             (unsigned int * addr, unsigned int index); /*  X = X \ {x}    */
    void    BitVector_Bit_On              (unsigned int * addr, unsigned int index); /*  X = X + {x}    */
    boolean BitVector_bit_test            (unsigned int * addr, unsigned int index); /*  {x} in X ?     */
    
    /* ===> bit vector bit shift & rotate functions: */
    boolean BitVector_msb_                (unsigned int * addr);
    boolean BitVector_shift_left          (unsigned int * addr, boolean carry_in);
    boolean BitVector_shift_right         (unsigned int * addr, boolean carry_in);
    void    BitVector_Move_Left           (unsigned int * addr, unsigned int bits);
    void    BitVector_Move_Right          (unsigned int * addr, unsigned int bits);
    
    /* ===> bit vector insert/delete bits: */
    
    /* ===> bit vector arithmetic: */
    boolean BitVector_increment           (unsigned int * addr);                        /*  X++  */
    boolean BitVector_decrement           (unsigned int * addr);                        /*  X--  */
    boolean BitVector_compute             (unsigned int * X, unsigned int * Y, 
                                           unsigned int * Z, boolean minus, boolean *carry);
    boolean BitVector_add                 (unsigned int * X, 
                                           unsigned int * Y, unsigned int * Z, boolean *carry);
    boolean BitVector_sub                 (unsigned int * X, 
                                           unsigned int * Y, unsigned int * Z, boolean *carry); /* X = Y-Z*/
    
    void    BitVector_Negate              (unsigned int * X, unsigned int * Y);
    signed int   BitVector_Sign           (unsigned int * addr);
    ErrCode BitVector_Mul_Pos             (unsigned int * X, 
                                           unsigned int * Y, unsigned int * Z, boolean strict);
    ErrCode BitVector_Multiply            (unsigned int * X, unsigned int * Y, unsigned int * Z);
    ErrCode BitVector_Div_Pos             (unsigned int * Q, unsigned int * X, unsigned int * Y, unsigned int * R);
    ErrCode BitVector_Divide              (unsigned int * Q, unsigned int * X, unsigned int * Y, unsigned int * R);
    
    /* ===> direct memory access functions: */
    void    BitVector_Block_Store         (unsigned int * addr, 
                                           unsigned char * buffer, unsigned int length);
    
    /* ===> word array functions: */
    void    BitVector_Word_Insert         (unsigned int * addr, 
                                           unsigned int offset, unsigned int count, boolean clear);
    void    BitVector_Word_Delete         (unsigned int * addr, 
                                           unsigned int offset, unsigned int count, boolean clear);
    
    /* ===> arbitrary size chunk functions: */
    void    BitVector_Chunk_Store         (unsigned int * addr, unsigned int chunksize,
                                           unsigned int offset, unsigned long value);
    unsigned long  BitVector_Chunk_Read   (unsigned int * addr, 
                                           unsigned int chunksize,unsigned int offset);
    
    /* ===> set operations: */
    void    Set_Union                     (unsigned int * X, unsigned int * Y, unsigned int * Z); /* X = Y + Z */
    void    Set_Intersection              (unsigned int * X, unsigned int * Y, unsigned int * Z); /* X = Y * Z */
    void    Set_ExclusiveOr               (unsigned int * X, unsigned int * Y, unsigned int * Z); /*(Y+Z)\(Y*Z)*/
    void    Set_Complement                (unsigned int * X, unsigned int * Y);                   /* X = ~Y    */
    
    /* ===> set functions: */
    signed long    Set_Min                (unsigned int * addr);                    /* = min(X)  */
    signed long    Set_Max                (unsigned int * addr);                    /* = max(X)  */
    
    /* ===> matrix-of-booleans operations: */
    
    /*****************************************************************************/
    /*  MODULE RESOURCES:                                                        */
    /*****************************************************************************/
#define bits_(BitVector) *(BitVector-3)
#define size_(BitVector) *(BitVector-2)
#define mask_(BitVector) *(BitVector-1)
    
#define  ERRCODE_TYPE  "sizeof(word) > sizeof(size_t)"
#define  ERRCODE_BITS  "bits(word) != sizeof(word)*8"
#define  ERRCODE_WORD  "bits(word) < 16"
#define  ERRCODE_LONG  "bits(word) > bits(long)"
#define  ERRCODE_POWR  "bits(word) != 2^x"
#define  ERRCODE_LOGA  "bits(word) != 2^ld(bits(word))"
#define  ERRCODE_NULL  "unable to allocate memory"
#define  ERRCODE_INDX  "index out of range"
#define  ERRCODE_ORDR  "minimum > maximum index"
#define  ERRCODE_SIZE  "bit vector size mismatch"
#define  ERRCODE_PARS  "input string syntax error"
#define  ERRCODE_OVFL  "numeric overflow error"
#define  ERRCODE_SAME  "result vector(s) must be distinct"
#define  ERRCODE_EXPO  "exponent must be positive"
#define  ERRCODE_ZERO  "division by zero error"
#define  ERRCODE_OOPS  "unexpected internal error - please contact author"
        
#ifdef __cplusplus
  }
#endif

#if defined(__GNUC__) || defined(__clang__)
#pragma GCC visibility pop
#endif
} //end of namespace CONSTANTBV
#endif

