2.x C API handle lifetime
=========================

``libstp2`` provides the 2.x C API (``c_interface.h``) and keeps its handle
contract, which this page states.  The API exposes ``VC``, ``Expr``,
``Type``, and ``WholeCounterExample`` as opaque raw pointers.  Their
supported lifetime is owner-dominant: a manager-dependent child handle is
supported only while both of these conditions hold:

* its owning ``VC`` is live; and
* the child has not been explicitly deleted.

``vc_Destroy(vc)`` invalidates every manager-dependent child of ``vc``.
Explicit child deletion invalidates that child immediately.  The same rule
applies to ``Expr`` and ``Type`` handles, ``WholeCounterExample`` handles,
counterexample-array buffers and their contained expressions, and future
opaque handles derived from manager state unless they are separately
documented as independent.

Ownership is not copied with the pointer value.  Copying an opaque ``void *``
token does not copy ownership, extend its lifetime, create another deletion
right, make a child independent of its ``VC``, or make a stale token valid
again if an allocator later reuses the same address.

Cleanup order
-------------

The valid child-before-owner cleanup order is mandatory when the caller owns
child wrappers: delete each one exactly once while its owner is still live,
then destroy the owner.  Counterexample arrays must also be released while
their producing ``VC`` is live.  For example:

.. code-block:: c

   VC vc = vc_createValidityChecker();
   vc_setInterfaceFlags(vc, EXPRDELETE, 0);

   Type bv8 = vc_bvType(vc, 8);
   Expr x = vc_varExpr(vc, "x", bv8);
   Expr zero = vc_bvConstExprFromInt(vc, 8, 0);
   Expr equality = vc_eqExpr(vc, x, zero);

   /* Use every handle while vc is live. */
   (void)vc_query(vc, equality);

   /* Caller-owned children precede their owner. */
   vc_DeleteExpr(equality);
   vc_DeleteExpr(zero);
   vc_DeleteExpr(x);
   vc_DeleteExpr(bv8);
   vc_Destroy(vc);

With the default ``EXPRDELETE`` policy, ``vc_Destroy`` releases every
checker-owned wrapper the caller has not already deleted: an explicit
``vc_DeleteExpr`` on one of them makes the checker forget it, so the example
above is valid with or without its ``vc_setInterfaceFlags`` line.  Changing
the ownership policy during a session is unsupported.

Invalidated raw pointers
------------------------

Using or deleting a child after explicit deletion or after destruction of its
owning ``VC`` is outside the supported contract.  The same is true
of reusing or destroying an already destroyed owner.  These calls may reach
reclaimed storage.  STP does not promise safe execution, deterministic
diagnosis, an error message, a return value, or process continuation for an
arbitrary dangling raw pointer.

This boundary does not weaken validation of supported calls.  Live
same-owner operands remain supported, and each function's established rules
for null inputs, wrong live sorts, live foreign-manager operands, invalid
widths, disabled capabilities, allocation failures, and resource failures
continue to apply.  Normal product tests should not dereference a dangling
raw pointer in order to expect a diagnostic.

Independent returned allocations
--------------------------------

An allocation documented as independently caller-owned has its own lifetime.
For example, the exact Real model strings returned by the
``vc_getRealModel*`` functions are separate allocations: after a successful
return they do not alias manager storage, remain valid after ``vc_Destroy``,
and must be released once with ``vc_deleteString``.  This exception does not
make the ``Expr`` used to request the value independent.

The 3.x API and concurrency
---------------------------

The 3.x API (:doc:`api`) has a lifetime model of its own, in which terms and
solvers keep their term manager alive; ``stp.h`` states the rules for C
handles.  None of it extends to ``libstp2``'s raw pointers, and none of it
implies a dangling-pointer diagnostic for them.

Independent live checkers may be used on separate threads.  Concurrent use and
deletion of the same child, concurrent use and destruction of its owner,
repeated concurrent destruction, and unload or fork with outstanding handles
are unsupported.

This is the 2.x contract, not checked-handle hardening.  Apart from the
registry the uninterpreted-function entry points consult once ``'u'`` is set,
no tombstone, generation, owner control block, checked handle, or
use-after-free defence is provided.
