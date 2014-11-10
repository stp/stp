/********************************************************************
 * AUTHORS: Vijay Ganesh, David L. Dill
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
// -*- c++ -*-

// STLport debug checking, if we use STLport threads flag is to get
// rid of link errors, since iostreams compiles with threads.  alloc
// and uninitialized are extra checks Later on, if used with Purify or
// Valgrind, may want to set flags to prevent reporting of false
// leaks.  For some reason, _STLP_THREADS works on the command line
// but not here (?)
#define _STLP_THREADS
#define _STLP_DEBUG 1
#define _STLP_DEBUG_LEVEL _STLP_STANDARD_DBG_LEVEL
#define _STLP_DEBUG_ALLOC 1
#define _STLP_DEBUG_UNINITIALIZED 1
