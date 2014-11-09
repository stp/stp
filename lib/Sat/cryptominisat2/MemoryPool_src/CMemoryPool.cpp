/******************
CMemoryPool.cpp

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

/*!\file CMemoryPool.cpp
 * \brief CMemoryPool implementation.
 */

#include "SMemoryChunk.h"
#include "CMemoryPool.h"
#include <string.h>


namespace MemPool
{

static const int FREEED_MEMORY_CONTENT        = 0xAA ; //!< Value for freed memory  
static const int NEW_ALLOCATED_MEMORY_CONTENT = 0xFF ; //!< Initial Value for new allocated memory 

/******************
Constructor
******************/
CMemoryPool::CMemoryPool(const size_t &sInitialMemoryPoolSize,
		                 const size_t &sMemoryChunkSize,
				         const size_t &sMinimalMemorySizeToAllocate,
				         bool bSetMemoryData)
{
 m_ptrFirstChunk  = NULL ;
 m_ptrLastChunk   = NULL ;
 m_ptrCursorChunk = NULL ;

 m_sTotalMemoryPoolSize = 0 ;
 m_sUsedMemoryPoolSize  = 0 ;
 m_sFreeMemoryPoolSize  = 0 ;

 m_sMemoryChunkSize   = sMemoryChunkSize ;
 m_uiMemoryChunkCount = 0 ;
 m_uiObjectCount      = 0 ;

 m_bSetMemoryData               = bSetMemoryData ;
 m_sMinimalMemorySizeToAllocate = sMinimalMemorySizeToAllocate ;

 // Allocate the Initial amount of Memory from the Operating-System...
 AllocateMemory(sInitialMemoryPoolSize) ;
}

/******************
Destructor
******************/
CMemoryPool::~CMemoryPool()
{
  FreeAllAllocatedMemory() ;
  DeallocateAllChunks() ;
   
  // Check for possible Memory-Leaks...
  assert((m_uiObjectCount == 0) && "WARNING : Memory-Leak : You have not freed all allocated Memory") ;
}

/******************
GetMemory
******************/
void *CMemoryPool::GetMemory(const size_t &sMemorySize)
{
  size_t sBestMemBlockSize = CalculateBestMemoryBlockSize(sMemorySize) ;
  SMemoryChunk *ptrChunk = NULL ;
  while(!ptrChunk)
  {
    // Is a Chunks available to hold the requested amount of Memory ?
    ptrChunk = FindChunkSuitableToHoldMemory(sBestMemBlockSize) ;
    if(!ptrChunk)
    {
	  // No chunk can be found
	  // => Memory-Pool is to small. We have to request 
	  //    more Memory from the Operating-System....
	  sBestMemBlockSize = MaxValue(sBestMemBlockSize, CalculateBestMemoryBlockSize(m_sMinimalMemorySizeToAllocate)) ;
      AllocateMemory(sBestMemBlockSize) ;
    }
  }

  // Finally, a suitable Chunk was found.
  // Adjust the Values of the internal "TotalSize"/"UsedSize" Members and 
  // the Values of the MemoryChunk itself.
  m_sUsedMemoryPoolSize += sBestMemBlockSize ;
  m_sFreeMemoryPoolSize -= sBestMemBlockSize ;
  m_uiObjectCount++ ;
  SetMemoryChunkValues(ptrChunk, sBestMemBlockSize) ;

  // eventually, return the Pointer to the User
  return ((void *) ptrChunk->Data) ;
}

/******************
FreeMemory
******************/
void CMemoryPool::FreeMemory(void *ptrMemoryBlock, const size_t &sMemoryBlockSize)
{
  // Search all Chunks for the one holding the "ptrMemoryBlock"-Pointer
  // ("SMemoryChunk->Data == ptrMemoryBlock"). Eventually, free that Chunks,
  // so it beecomes available to the Memory-Pool again...
  SMemoryChunk *ptrChunk = FindChunkHoldingPointerTo(ptrMemoryBlock) ;
  if(ptrChunk)
  {
	  //std::cerr << "Freed Chunks OK (Used memPool Size : " << m_sUsedMemoryPoolSize << ")" << std::endl ;
	  FreeChunks(ptrChunk) ;
  }
  else
  {
	  assert(false && "ERROR : Requested Pointer not in Memory Pool") ;
  }
  assert((m_uiObjectCount > 0) && "ERROR : Request to delete more Memory then allocated.") ;
  m_uiObjectCount-- ;
}

/******************
AllocateMemory
******************/
bool CMemoryPool::AllocateMemory(const size_t &sMemorySize)
{
  // This function will allocate *at least* "sMemorySize"-Bytes from the Operating-System.

  // How it works :
  // Calculate the amount of "SMemoryChunks" needed to manage the requested MemorySize.
  // Every MemoryChunk can manage only a certain amount of Memory
  // (set by the "m_sMemoryChunkSize"-Member of the Memory-Pool).
  //
  // Also, calculate the "Best" Memory-Block size to allocate from the 
  // Operating-System, so that all allocated Memory can be assigned to a
  // Memory Chunk.
  // Example : 
  //	You want to Allocate 120 Bytes, but every "SMemoryChunk" can only handle
  //    50 Bytes ("m_sMemoryChunkSize = 50").
  //    So, "CalculateNeededChunks()" will return the Number of Chunks needed to
  //    manage 120 Bytes. Since it is not possible to divide 120 Bytes in to
  //    50 Byte Chunks, "CalculateNeededChunks()" returns 3.
  //    ==> 3 Chunks can Manage 150 Bytes of data (50 * 3 = 150), so
  //        the requested 120 Bytes will fit into this Block.
  //    "CalculateBestMemoryBlockSize()" will return the amount of memory needed
  //    to *perfectly* subdivide the allocated Memory into "m_sMemoryChunkSize" (= 50) Byte
  //    pieces. -> "CalculateBestMemoryBlockSize()" returns 150.
  //    So, 150 Bytes of memory are allocated from the Operating-System and
  //    subdivided into 3 Memory-Chunks (each holding a Pointer to 50 Bytes of the allocated memory).
  //    Since only 120 Bytes are requested, we have a Memory-Overhead of 
  //    150 - 120 = 30 Bytes. 
  //    Note, that the Memory-overhead is not a bad thing, because we can use 
  //    that memory later (it remains in the Memory-Pool).
  //

  unsigned int uiNeededChunks = CalculateNeededChunks(sMemorySize) ;
  size_t sBestMemBlockSize = CalculateBestMemoryBlockSize(sMemorySize) ;

  TByte *ptrNewMemBlock = (TByte *) malloc(sBestMemBlockSize) ; // allocate from Operating System
  SMemoryChunk *ptrNewChunks = (SMemoryChunk *) malloc((uiNeededChunks * sizeof(SMemoryChunk))) ; // allocate Chunk-Array to Manage the Memory
  assert(((ptrNewMemBlock) && (ptrNewChunks)) && "Error : System ran out of Memory") ;

  // Adjust internal Values (Total/Free Memory, etc.)
  m_sTotalMemoryPoolSize += sBestMemBlockSize ;
  m_sFreeMemoryPoolSize += sBestMemBlockSize ;
  m_uiMemoryChunkCount += uiNeededChunks ;

  // Usefull for Debugging : Set the Memory-Content to a defined Value
  if(m_bSetMemoryData)
  {
    memset(((void *) ptrNewMemBlock), NEW_ALLOCATED_MEMORY_CONTENT, sBestMemBlockSize) ;
  }

  // Associate the allocated Memory-Block with the Linked-List of MemoryChunks
  return LinkChunksToData(ptrNewChunks, uiNeededChunks, ptrNewMemBlock) ; ;
}

/******************
CalculateNeededChunks
******************/
unsigned int CMemoryPool::CalculateNeededChunks(const size_t &sMemorySize)
{
   float f = (float) (((float)sMemorySize) / ((float)m_sMemoryChunkSize)) ;
   return ((unsigned int) ceil(f)) ;
}

/******************
CalculateBestMemoryBlockSize
******************/
size_t CMemoryPool::CalculateBestMemoryBlockSize(const size_t &sRequestedMemoryBlockSize)
{
  unsigned int uiNeededChunks = CalculateNeededChunks(sRequestedMemoryBlockSize) ;
  return size_t((uiNeededChunks * m_sMemoryChunkSize)) ;
}

/******************
FreeChunks
******************/
void CMemoryPool::FreeChunks(SMemoryChunk *ptrChunk)
{
  // Make the Used Memory of the given Chunk available
  // to the Memory Pool again.

  SMemoryChunk *ptrCurrentChunk = ptrChunk ;
  unsigned int uiChunkCount = CalculateNeededChunks(ptrCurrentChunk->UsedSize);
  for(unsigned int i = 0; i < uiChunkCount; i++)
  {
    if(ptrCurrentChunk)
    {
      // Step 1 : Set the allocated Memory to 'FREEED_MEMORY_CONTENT'
      // Note : This is fully Optional, but usefull for debugging
	  if(m_bSetMemoryData)
	  {
        memset(((void *) ptrCurrentChunk->Data), FREEED_MEMORY_CONTENT, m_sMemoryChunkSize) ;
	  }

      // Step 2 : Set the Used-Size to Zero
      ptrCurrentChunk->UsedSize = 0 ;

      // Step 3 : Adjust Memory-Pool Values and goto next Chunk
      m_sUsedMemoryPoolSize -= m_sMemoryChunkSize ;
      ptrCurrentChunk = ptrCurrentChunk->Next ;
	}
  }
}


/******************
FindChunkSuitableToHoldMemory
******************/
SMemoryChunk *CMemoryPool::FindChunkSuitableToHoldMemory(const size_t &sMemorySize)
{
  // Find a Chunk to hold *at least* "sMemorySize" Bytes.
  unsigned int uiChunksToSkip = 0 ;
  bool bContinueSearch = true ;
  SMemoryChunk *ptrChunk = m_ptrCursorChunk ; // Start search at Cursor-Pos.
  for(unsigned int i = 0; i < m_uiMemoryChunkCount; i++)
  {
    if(ptrChunk)
    {
	  if(ptrChunk == m_ptrLastChunk) // End of List reached : Start over from the beginning
	  {
        ptrChunk = m_ptrFirstChunk ;
	  }

      if(ptrChunk->DataSize >= sMemorySize)
      {
        if(ptrChunk->UsedSize == 0)
        {
		  m_ptrCursorChunk = ptrChunk ;
          return ptrChunk ;
        }
      }
      uiChunksToSkip = CalculateNeededChunks(ptrChunk->UsedSize) ;
	  if(uiChunksToSkip == 0) uiChunksToSkip = 1 ;
      ptrChunk = SkipChunks(ptrChunk, uiChunksToSkip) ;
	}
	else
	{
      bContinueSearch = false ;
	}
  }
  return NULL ;
}

/******************
SkipChunks
******************/
SMemoryChunk *CMemoryPool::SkipChunks(SMemoryChunk *ptrStartChunk, unsigned int uiChunksToSkip)
{
	SMemoryChunk *ptrCurrentChunk = ptrStartChunk ;
	for(unsigned int i = 0; i < uiChunksToSkip; i++)
	{
		if(ptrCurrentChunk)
		{
		   ptrCurrentChunk = ptrCurrentChunk->Next ;
		}
		else
		{
			// Will occur, if you try to Skip more Chunks than actually available
			// from your "ptrStartChunk" 
			assert(false && "Error : Chunk == NULL was not expected.") ;
			break ;
		}
	}
	return ptrCurrentChunk ;
}

/******************
SetMemoryChunkValues
******************/
void CMemoryPool::SetMemoryChunkValues(SMemoryChunk *ptrChunk, const size_t &sMemBlockSize)
{
  if((ptrChunk)) // && (ptrChunk != m_ptrLastChunk))
  {
    ptrChunk->UsedSize = sMemBlockSize ;
  }
  else
  {
	  assert(false && "Error : Invalid NULL-Pointer passed") ;
  }
}

/******************
WriteMemoryDumpToFile
******************/
bool CMemoryPool::WriteMemoryDumpToFile(const std::string &strFileName)
{
  bool bWriteSuccesfull = false ;
  std::ofstream ofOutputFile ;
  ofOutputFile.open(strFileName.c_str(), std::ofstream::out | std::ofstream::binary) ;

  SMemoryChunk *ptrCurrentChunk = m_ptrFirstChunk ;
  while(ptrCurrentChunk)
  {
    if(ofOutputFile.good())
    {
		ofOutputFile.write(((char *)ptrCurrentChunk->Data), ((std::streamsize) m_sMemoryChunkSize)) ;
      bWriteSuccesfull = true ;
    }
    ptrCurrentChunk = ptrCurrentChunk->Next ;
  }
  ofOutputFile.close() ;
  return bWriteSuccesfull ;
}

/******************
LinkChunksToData
******************/
bool CMemoryPool::LinkChunksToData(SMemoryChunk *ptrNewChunks, unsigned int uiChunkCount, TByte *ptrNewMemBlock)
{
  SMemoryChunk *ptrNewChunk = NULL ;
  unsigned int uiMemOffSet = 0 ;
  bool bAllocationChunkAssigned = false ;
  for(unsigned int i = 0; i < uiChunkCount; i++)
  {
    if(!m_ptrFirstChunk)
    {
      m_ptrFirstChunk = SetChunkDefaults(&(ptrNewChunks[0])) ;
      m_ptrLastChunk = m_ptrFirstChunk ;
      m_ptrCursorChunk = m_ptrFirstChunk ;
    }
    else
    {
      ptrNewChunk = SetChunkDefaults(&(ptrNewChunks[i])) ;
      m_ptrLastChunk->Next = ptrNewChunk ;
      m_ptrLastChunk = ptrNewChunk ;
    }
    
	uiMemOffSet = (i * ((unsigned int) m_sMemoryChunkSize)) ;
    m_ptrLastChunk->Data = &(ptrNewMemBlock[uiMemOffSet]) ;

	// The first Chunk assigned to the new Memory-Block will be 
	// a "AllocationChunk". This means, this Chunks stores the
	// "original" Pointer to the MemBlock and is responsible for
	// "free()"ing the Memory later....
	if(!bAllocationChunkAssigned)
	{
		m_ptrLastChunk->IsAllocationChunk = true ;
		bAllocationChunkAssigned = true ;
	}
  }
  return RecalcChunkMemorySize(m_ptrFirstChunk, m_uiMemoryChunkCount) ;
}

/******************
RecalcChunkMemorySize
******************/
bool CMemoryPool::RecalcChunkMemorySize(SMemoryChunk *ptrChunk, unsigned int uiChunkCount)
{
  unsigned int uiMemOffSet = 0 ;
  for(unsigned int i = 0; i < uiChunkCount; i++)
  {
	  if(ptrChunk)
	  {
	    uiMemOffSet = (i * ((unsigned int) m_sMemoryChunkSize)) ;
	    ptrChunk->DataSize = (((unsigned int) m_sTotalMemoryPoolSize) - uiMemOffSet) ;
	    ptrChunk = ptrChunk->Next ;
	  }
	  else
	  {
		assert(false && "Error : ptrChunk == NULL") ;
        return false ;
	  }
  }
  return true ;
}

/******************
SetChunkDefaults
******************/
SMemoryChunk *CMemoryPool::SetChunkDefaults(SMemoryChunk *ptrChunk)
{
  if(ptrChunk)
  {
    ptrChunk->Data = NULL ;
    ptrChunk->DataSize = 0 ;
    ptrChunk->UsedSize = 0 ;
	ptrChunk->IsAllocationChunk = false ;
    ptrChunk->Next = NULL ;
  }
  return ptrChunk ;
}

/******************
FindChunkHoldingPointerTo
******************/
SMemoryChunk *CMemoryPool::FindChunkHoldingPointerTo(void *ptrMemoryBlock)
{
	SMemoryChunk *ptrTempChunk = m_ptrFirstChunk ;
	while(ptrTempChunk)
	{
		if(ptrTempChunk->Data == ((TByte *) ptrMemoryBlock))
		{
			break ;
		}
		ptrTempChunk = ptrTempChunk->Next ;
	}
	return ptrTempChunk ;
}

/******************
FreeAllAllocatedMemory
******************/
void CMemoryPool::FreeAllAllocatedMemory()
{
	SMemoryChunk *ptrChunk = m_ptrFirstChunk ;
	while(ptrChunk)
	{
		if(ptrChunk->IsAllocationChunk)
		{
			free(((void *) (ptrChunk->Data))) ;
		}
		ptrChunk = ptrChunk->Next ;
	}
}

/******************
DeallocateAllChunks
******************/
void CMemoryPool::DeallocateAllChunks()
{
  SMemoryChunk *ptrChunk = m_ptrFirstChunk ;
  SMemoryChunk *ptrChunkToDelete = NULL ;
  while(ptrChunk)
  {
	if(ptrChunk->IsAllocationChunk)
	{	
		if(ptrChunkToDelete)
		{
			free(((void *) ptrChunkToDelete)) ;
		}
		ptrChunkToDelete = ptrChunk ;
	}
	ptrChunk = ptrChunk->Next ;
  }
}

/******************
IsValidPointer
******************/
bool CMemoryPool::IsValidPointer(void *ptrPointer)
{
    SMemoryChunk *ptrChunk = m_ptrFirstChunk ;
	while(ptrChunk)
	{
		if(ptrChunk->Data == ((TByte *) ptrPointer))
		{
			return true ;
		}
		ptrChunk = ptrChunk->Next ;
	}
	return false ;
}

/******************
MaxValue
******************/
size_t CMemoryPool::MaxValue(const size_t &sValueA, const size_t &sValueB) const
{
  if(sValueA > sValueB)
  {
	  return sValueA ;
  }
  return sValueB ;
}

}
