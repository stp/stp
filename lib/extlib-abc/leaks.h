/******************************************************************
Copyright (c) The Regents of the University of California. All rights reserved.

Permission is hereby granted, without written agreement and without license or
royalty fees, to use, copy, modify, and distribute this software and its
documentation for any purpose, provided that the above copyright notice and
the following two paragraphs appear in all copies of this software.

IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY FOR
DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT OF
THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF
CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING,
BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS ON AN "AS IS" BASIS,
AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO PROVIDE MAINTENANCE,
SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
*********************************************************************/


//////////////////////////////////////////////////////////////////////////
// This file is used to detect memory leaks using Visual Studio 6.0
// The idea comes from this page: http://www.michaelmoser.org/memory.htm
// In addition to this file, it required the presence of "stdlib_hack.h"
//////////////////////////////////////////////////////////////////////////

#ifndef __LEAKS_H__
#define __LEAKS_H__

#if defined(_DEBUG) && !defined(__cplusplus)
#define _CRTDBG_MAP_ALLOC // include Microsoft memory leak detection procedures
//#define _INC_MALLOC	     // exclude standard memory alloc procedures

#define   malloc(s)         _malloc_dbg(s, _NORMAL_BLOCK, __FILE__, __LINE__)
#define   calloc(c, s)      _calloc_dbg(c, s, _NORMAL_BLOCK, __FILE__, __LINE__)
#define   realloc(p, s)     _realloc_dbg(p, s, _NORMAL_BLOCK, __FILE__, __LINE__)
//#define   _expand(p, s)     _expand_dbg(p, s, _NORMAL_BLOCK, __FILE__, __LINE__)
//#define   free(p)           _free_dbg(p, _NORMAL_BLOCK)
//#define   _msize(p)         _msize_dbg(p, _NORMAL_BLOCK)

//#include <stdlib.h>
//#include <stdlib_hack.h>
#include <crtdbg.h>
#endif

#endif

//////////////////////////////////////


