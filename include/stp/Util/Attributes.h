/********************************************************************
 * AUTHOR: Felix Kutzner, Mate Soos
 *
 * BEGIN DATE: Apr, 2017
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
// ********************************************************************/

#ifndef ATTRIBUTES_H_
#define ATTRIBUTES_H_

#include "stp/config.h"


#if defined(_MSC_VER)
#define ATTR_NORETURN __declspec(noreturn)
#elif defined(__GNUC__) || defined(__clang__)
#define ATTR_NORETURN __attribute__((noreturn))
#else
#define ATTR_NORETURN
#endif

// The DLL_PUBLIC / DLL_LOCAL block below is duplicated verbatim in
// include/stp/c_interface.h, and deliberately so: c_interface.h is the only
// header STP installs, and this header ships nowhere, so the public C header
// cannot include it. Do not "deduplicate" the two -- that would leave the
// installed header with no definition of DLL_PUBLIC. Keep them in sync instead.
#if defined(_MSC_VER)
// MSVC symbol visibility. Two macros drive it, both set by lib/CMakeLists.txt:
//
//   STP_SHARED_LIB  libstp is a DLL. Defined only when BUILD_SHARED_LIBS is ON:
//                   for the library's own sources, and, through the exported
//                   target's interface, for clients that link it.
//   STP_EXPORTS     this translation unit is part of libstp itself, rather than
//                   a client compiling against these headers.
//
// A static build defines neither and gets an empty DLL_PUBLIC. That is the only
// expansion that links for static: a static client that saw dllimport would
// fail at link time. A shared build gets dllexport while the library is being
// compiled and dllimport for everyone else.
//
// The mechanism is currently dormant -- no shared MSVC build of STP is produced
// (both Windows CI jobs are STATICCOMPILE=ON, which forces BUILD_SHARED_LIBS
// OFF), so neither __declspec arm is ever taken. It is kept correct so that
// enabling a Windows DLL build later works.
#if defined(STP_SHARED_LIB) && defined(STP_EXPORTS)
// This is visible when building the STP library as a DLL.
#define DLL_PUBLIC __declspec(dllexport)
#elif defined(STP_SHARED_LIB)
// This is visible for STP clients.
#define DLL_PUBLIC __declspec(dllimport)
#else
#define DLL_PUBLIC
#endif

// Symbols are hidden by default in MSVC.
#define DLL_LOCAL

#elif defined(__GNUC__) || defined(__clang__)
#define DLL_PUBLIC __attribute__((visibility("default")))
#define DLL_LOCAL __attribute__((visibility("hidden")))
#else
#define DLL_PUBLIC
#define DLL_LOCAL
#endif

// Defining THREAD_LOCAL_IE, the storage class STP uses for every one of its
// mutable globals. "IE" is the initial-exec TLS model: the variable lives at a
// fixed offset from the thread pointer instead of being reached through a
// __tls_get_addr call into the dynamic loader on every access. Thread-safety
// is identical either way -- one copy per thread -- only the addressing
// differs, so this is the right default for all of them, not just the hot
// ones. The cost is that initial-exec variables are allocated out of the
// process's static TLS surplus; that is fine for the stp binary and for
// libstp when it is in the initial load set or dlopen'd early, which are the
// normal cases. Configure with -DUSE_THREAD_LOCAL=OFF for plain globals.
#if !USE_THREAD_LOCAL
#define STP_THREAD_LOCAL
#elif __cplusplus >= 201103L
#define STP_THREAD_LOCAL thread_local
#elif defined _WIN32 && (defined _MSC_VER || defined __ICL ||                  \
                         defined __DMC__ || defined __BORLANDC__)

//********************
// For windows, this does not work, DLL_PUBLIC and thread-local together die
//********************
//#define STP_THREAD_LOCAL __declspec(thread)
#define STP_THREAD_LOCAL

/* note that ICC (linux) and Clang are covered by __GNUC__ */
#elif defined __GNUC__ || defined __SUNPRO_C || defined __xlC__
#define STP_THREAD_LOCAL __thread
#else
#error "Cannot define STP_THREAD_LOCAL"
#endif

// The initial-exec attribute is a GCC/Clang spelling; everywhere else the
// macro degrades to a plain thread-local (or to nothing).
#if USE_THREAD_LOCAL && (defined(__GNUC__) || defined(__clang__))
#define THREAD_LOCAL_IE                                                        \
  STP_THREAD_LOCAL __attribute__((tls_model("initial-exec")))
#else
#define THREAD_LOCAL_IE STP_THREAD_LOCAL
#endif

#endif //ATTRIBUTES_H_
