/******************
SMemoryChunk.h

THE WORK (AS DEFINED BELOW) IS PROVIDED UNDER THE TERMS OF THIS CODE PROJECT
OPEN LICENSE ("LICENSE"). THE WORK IS PROTECTED BY COPYRIGHT AND/OR OTHER
APPLICABLE LAW. ANY USE OF THE WORK OTHER THAN AS AUTHORIZED UNDER THIS LICENSE
OR COPYRIGHT LAW IS PROHIBITED.

BY EXERCISING ANY RIGHTS TO THE WORK PROVIDED HEREIN, YOU ACCEPT AND AGREE TO
BE BOUND BY THE TERMS OF THIS LICENSE. THE AUTHOR GRANTS YOU THE RIGHTS
CONTAINED HEREIN IN CONSIDERATION OF YOUR ACCEPTANCE OF SUCH TERMS AND
CONDITIONS. IF YOU DO NOT AGREE TO ACCEPT AND BE BOUND BY THE TERMS OF THIS
LICENSE, YOU CANNOT MAKE ANY USE OF THE WORK.

The main points subject to the terms of the License are:

* Source Code and Executable Files can be used in commercial applications;
* Source Code and Executable Files can be redistributed; and
* Source Code can be modified to create derivative works.
* No claim of suitability, guarantee, or any warranty whatsoever is provided. The software is provided "as-is".
* The Article(s) accompanying the Work may not be distributed or republished without the Author's consent
******************/

/*!\file SMemoryChunk.h
 * \brief Contains the "SMemoryChunk" Type-definition.
 */

#ifndef __INC_SMemoryChunk_h__
#define __INC_SMemoryChunk_h__

#include "IMemoryBlock.h"

namespace MemPool
{

/*!\class SMemoryChunk
 * \brief Memory Chunk Struct
 *
 * This struct will hold (and manage) the actual allocated Memory.
 * Every MemoryChunk will point to a MemoryBlock, and another SMemoryChunk,
 * thus creating a linked-list of MemoryChunks.
 */
typedef struct SMemoryChunk
{
  TByte *Data ;				//!< The actual Data
  size_t DataSize ;	//!< Size of the "Data"-Block
  size_t UsedSize ;	//!< actual used Size
  bool IsAllocationChunk ;	//!< true, when this MemoryChunks Points to a "Data"-Block which can be deallocated via "free()"
  SMemoryChunk *Next ;		//!< Pointer to the Next MemoryChunk in the List (may be NULL)

} SMemoryChunk ;

}

#endif /* __INC_SMemoryChunk_h__ */
