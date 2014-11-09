/******************
IMemoryBlock.h

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

/*!\file IMemoryBlock.h
 * \brief Contains the "IMemoryBlock" Class-defintion.
 *        This is the (abstract) interface for the actual MemoryPool-Class.
 */


#ifndef __INC_IMemoryBlock_h__
#define __INC_IMemoryBlock_h__

#include <stdlib.h>

//#include "../BasicIncludes.h"

/*!\namespace MemPool
 * \brief MemoryPool Namespace
 *
 * This Namespace contains all classes and typedefs needed by
 * the MemoryPool implementation.
 * The MemoryPool has its own namespace because some typedefs
 * (e.g. TByte) may intefer with other toolkits if the
 * MemoryPool would be in the global namespace.
 */
namespace MemPool
{

/*!\typedef unsigned char TByte ;
 * \brief Byte (= 8 Bit) Typedefinition.
 */
typedef unsigned char TByte ;

/*!\class IMemoryBlock
 * \brief Interface Class (pure Virtual) for the MemoryPool
 *
 * Abstract Base-Class (interface) for the MemoryPool.
 * Introduces Basic Operations like Geting/Freeing Memory.
 */
class IMemoryBlock
{
  public :
    virtual ~IMemoryBlock() {} ;

    virtual void *GetMemory(const size_t &sMemorySize) = 0 ;
    virtual void FreeMemory(void *ptrMemoryBlock, const size_t &sMemoryBlockSize) = 0 ;
} ;

}
#endif /* __INC_IMemoryBlock_h__ */
