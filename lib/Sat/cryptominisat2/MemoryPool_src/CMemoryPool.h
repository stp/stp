/******************
CMemoryPool.h

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


/*!\file CMemoryPool.h
 * \brief Contains the "CMemoryPool" Class-defintion.
 */

#ifndef __INC_CMemoryPool_h__
#define __INC_CMemoryPool_h__

#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <assert.h>

#include <iostream>
#include <fstream>

#include "IMemoryBlock.h"
#include "SMemoryChunk.h"

namespace MemPool
{

static const size_t DEFAULT_MEMORY_POOL_SIZE        = 1000 ;                          //!< Initial MemoryPool size (in Bytes)
static const size_t DEFAULT_MEMORY_CHUNK_SIZE       = 128 ;                           //!< Default MemoryChunkSize (in Bytes)
static const size_t DEFAULT_MEMORY_SIZE_TO_ALLOCATE = DEFAULT_MEMORY_CHUNK_SIZE * 2 ; //!< Default Minimal Memory-Size (in Bytes) to Allocate.

/*!\class CMemoryPool
 * \brief MemoryPool-Class
 *
 * This class is the actual implementation of the IMemoryBlock - Interface.
 * It is responsible for all MemoryRequests (GetMemory() / FreeMemory()) and
 * manages the allocation/deallocation of Memory from the Operating-System.
 */
class CMemoryPool : public IMemoryBlock
{
  public :
    /*!
	Contructor
	\param [IN] sInitialMemoryPoolSize The Initial Size (in Bytes) of the Memory Pool
	\param [IN] sMemoryChunkSize The Size (in Bytes) each MemoryChunk can Manage. 
	            A low sMemoryChunkSize increases the MemoryPool runtime (bad), but decreases the Memory-overhead/fragmentation (good)
    \param [IN] sMinimalMemorySizeToAllocate The Minimal amount of Memory which is allocated (in Bytes).
	            That means, every time you have to allocate more Memory from the Operating-System,
				<b>at least</b> sMinimalMemorySizeToAllocate Bytes are allocated.
				When you have to request small amount of Memory very often, this will speed up
				the MemoryPool, beacause when you allocate a new Memory from the OS,
				you will allocate a small "Buffer" automatically, wich will prevent you from
				requesting OS-memory too often.
	\param [IN] bSetMemoryData Set to true, if you want to set all allocated/freed Memory to a specific
	            Value. Very usefull for debugging, but has a negativ impact on the runtime.
	*/
    CMemoryPool(const size_t &sInitialMemoryPoolSize = DEFAULT_MEMORY_POOL_SIZE,
		        const size_t &sMemoryChunkSize = DEFAULT_MEMORY_CHUNK_SIZE,
				const size_t &sMinimalMemorySizeToAllocate = DEFAULT_MEMORY_SIZE_TO_ALLOCATE,
				bool bSetMemoryData = false) ;
    virtual ~CMemoryPool() ; //!< Destructor

	/*!
	  Get "sMemorySize" Bytes from the Memory Pool.
	  \param [IN] sMemorySize       Sizes (in Bytes) of Memory.
	  \return                       Pointer to a Memory-Block of "sMemorySize" Bytes, or NULL if an error occured. 
	*/
    virtual void *GetMemory(const size_t &sMemorySize) ;
    
	/*!
	  Free the allocated memory again....
	  \param [IN] ptrMemoryBlock    Pointer to a Block of Memory, which is to be freed (previoulsy allocated via "GetMemory()").
	  \param [IN] sMemorySize       Sizes (in Bytes) of Memory.
	*/
	virtual void FreeMemory(void *ptrMemoryBlock, const size_t &sMemoryBlockSize) ;

	/*!
	  Writes the contents of the MemoryPool to a File.
	  Note : This file can be quite large (several MB).
	  \param [IN] strFileName      FileName of the MemoryDump.
	  \return                      true on success, false otherwise 
	*/
    bool WriteMemoryDumpToFile(const std::string &strFileName) ;
	/*!
	  Check, if a Pointer is in the Memory-Pool.
	  Note : This Checks only if a pointer is inside the Memory-Pool,
	         and <b>not</b> if the Memory contains meaningfull data.
	  \param [IN] ptrPointer       Pointer to a Memory-Block which is to be checked.
	  \return                      true, if the Pointer could be found in the Memory-Pool, false otherwise.
	*/
	bool IsValidPointer(void *ptrPointer) ;
 
  private :
    /*!
	  Will Allocate <b>at least</b> "sMemorySize" Bytes of Memory from the Operating-System.
	  The Memory will be cut into Pieces and Managed by the MemoryChunk-Linked-List.
	  (See LinkChunksToData() for details).
	  \param [IN] sMemorySize      The Memory-Size (in Bytes) to allocate
	  \return                      true, if the Memory could be allocated, false otherwise (e.g. System is out of Memory, etc.)
	*/
    bool AllocateMemory(const size_t &sMemorySize) ;
	void FreeAllAllocatedMemory() ; //!< Will free all Aloocated Memory to the Operating-System again.

    unsigned int CalculateNeededChunks(const size_t &sMemorySize) ; //!< \return the Number of MemoryChunks needed to Manage "sMemorySize" Bytes.
    size_t CalculateBestMemoryBlockSize(const size_t &sRequestedMemoryBlockSize) ; //!< return the amount of Memory which is best Managed by the MemoryChunks.

    SMemoryChunk *FindChunkSuitableToHoldMemory(const size_t &sMemorySize) ; //!< \return a Chunk which can hold the requested amount of memory, or NULL, if none was found.
    SMemoryChunk *FindChunkHoldingPointerTo(void *ptrMemoryBlock) ; //!< Find a Chunk which "Data"-Member is Pointing to the given "ptrMemoryBlock", or NULL if none was found.

	SMemoryChunk *SkipChunks(SMemoryChunk *ptrStartChunk, unsigned int uiChunksToSkip) ; //!< Skip the given amount of Chunks, starting from the given ptrStartChunk. \return the Chunk at the "skipping"-Position.
    SMemoryChunk *SetChunkDefaults(SMemoryChunk *ptrChunk) ; //!< Set "Default"-Values to the given Chunk

    void FreeChunks(SMemoryChunk *ptrChunk) ; //!< Makes the memory linked to the given Chunk available in the MemoryPool again (by setting the "UsedSize"-Member to 0).
	void DeallocateAllChunks() ; //!< Deallocates all Memory needed by the Chunks back to the Operating-System.

    bool LinkChunksToData(SMemoryChunk *ptrNewChunk, unsigned int uiChunkCount, TByte *ptrNewMemBlock) ; //!< Link the given Memory-Block to the Linked-List of MemoryChunks...
	void SetMemoryChunkValues(SMemoryChunk *ptrChunk, const size_t &sMemBlockSize) ; //!< Set the "UsedSize"-Member of the given "ptrChunk" to "sMemBlockSize".
	bool RecalcChunkMemorySize(SMemoryChunk *ptrChunks, unsigned int uiChunkCount) ; //!< Recalcs the "DataSize"-Member of all Chunks whe the Memory-Pool grows (via "AllocateMemory()")

	size_t MaxValue(const size_t &sValueA, const size_t &sValueB) const ; //!< \return the greatest of the two input values (A or B)
	
    SMemoryChunk *m_ptrFirstChunk ;  //!< Pointer to the first Chunk in the Linked-List of Memory Chunks
    SMemoryChunk *m_ptrLastChunk ;   //!< Pointer to the last Chunk in the Linked-List of Memory Chunks
    SMemoryChunk *m_ptrCursorChunk ; //!< Cursor-Chunk. Used to speed up the navigation in the linked-List.

    size_t m_sTotalMemoryPoolSize ;  //!< Total Memory-Pool size in Bytes
    size_t m_sUsedMemoryPoolSize ;   //!< amount of used Memory in Bytes
    size_t m_sFreeMemoryPoolSize ;   //!< amount of free Memory in Bytes

    size_t m_sMemoryChunkSize ;     //!< amount of Memory which can be Managed by a single MemoryChunk.
    unsigned int m_uiMemoryChunkCount ;  //!< Total amount of "SMemoryChunk"-Objects in the Memory-Pool.
	unsigned int m_uiObjectCount ;       //!< Counter for "GetMemory()" / "FreeMemory()"-Operation. Counts (indirectly) the number of "Objects" inside the mem-Pool.

	bool m_bSetMemoryData ;                      //!< Set to "true", if you want to set all (de)allocated Memory to a predefined Value (via "memset()"). Usefull for debugging.
	size_t m_sMinimalMemorySizeToAllocate ; //!< The minimal amount of Memory which can be allocated via "AllocateMemory()".
} ;

}

#endif /* __INC_CMemoryPool_h__ */
