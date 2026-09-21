Mathematical API
================

Equality
--------

.. deppy-api:: crates/deppy-python/stdlib/deppy/equality.py

Logical data and decisions
--------------------------

.. deppy-api:: crates/deppy-python/stdlib/deppy/data.py

Natural numbers and order
-------------------------

.. deppy-api:: crates/deppy-python/stdlib/deppy/nat.py

Order decisions ``le_decide`` and ``lt_decide`` compute to ``Yes`` or ``No``.
The new order theorems are opaque; their statements remain available to proofs.
``pred_lt`` requires a proof that the counter is positive, so it does not
claim a decrease at zero.

.. deppy-api:: crates/deppy-python/stdlib/deppy/nat_order.py

Lists
-----

.. deppy-api:: crates/deppy-python/stdlib/deppy/lists.py

Verified branch helpers
-----------------------

.. deppy-api:: crates/deppy-python/stdlib/deppy/verified.py

Verified loop obligations
-------------------------

.. deppy-api:: crates/deppy-python/stdlib/deppy/verified_loop.py

Verified specification reuse
----------------------------

``verified_spec(function, *inputs, precondition_proof)`` is compiler-provided
syntax exported by ``deppy.verified``. It applies the opaque, kernel-checked
theorem associated with a statically resolved verified function. Its result has
type ``ensures(inputs, function(inputs))``. When there are no refined parameters and no explicit ``requires``, the
precondition is ``Unit`` and the final argument is ``MkUnit()``. User axiom
dependencies remain visible when the theorem is reused.

Refined returns and Fibonacci
-----------------------------

``Refined[A, predicate]`` is compiler-provided parameter and return annotation syntax for
``@verified``, exported by ``deppy.verified``. ``A`` is ``Nat`` or ``Bool``;
a return predicate receives the result and may capture entry arguments. It
replaces ``ensures`` and requires the same checked VC proof. The function returns an
ordinary base value; its refinement theorem is available through ``verified_spec``.
Parameter predicates receive the argument value and may capture earlier entry
arguments. Their conditions, in parameter order, followed by an explicit
``requires`` are combined into a right-associated Sigma. A single condition is
used directly; no conditions means ``Unit``. The combined evidence is the
``pre`` argument of proof callbacks and the final argument of ``verified_spec``.
Local refinements use named assignment VCs; same-base condition conversions require explicit evidence. Implicit subtyping is not supported.

.. deppy-api:: crates/deppy-python/examples/fibonacci.py

Contract composition
--------------------

``@verified(proofs={...})`` checks each call precondition and proves the
continuation for an arbitrary result satisfying the checked callee contract.
The result and its specification evidence are passed to subsequent proof
callbacks. Missing entries become named goals with source locations; unfinished
proofs are never registered. Calls in a single loop body and after the loop are supported.

Single loops support ``loop.init``, ``loop.preserve``,
``loop.decrease`` and ``loop.exit`` proof entries.

.. deppy-api:: crates/deppy-python/examples/verified_composition.py

Refined argument composition
----------------------------

Missing call proofs produce named precondition goals. ``exact`` can use an
entry refinement or an earlier call's postcondition; ``rewrite`` can transform
the goal using that evidence. Every generated proof is kernel-checked.

.. deppy-api:: crates/deppy-python/examples/refined_arguments.py

Local refinements and modular loops
-----------------------------------

Local ``Refined[Nat/Bool, predicate]`` annotations capture their environment at
annotation time. Initialization and reassignment generate ``local.x.refined``
VCs, with numeric suffixes for later assignments. Conversions between conditions
on the same base type use these VCs or a callee's precondition VC.

Loop preservation and decrease proofs independently compose helper contracts.
Refined state variables also require ``loop.preserve.entry.local.x.refined``
(and decrease/exit counterparts), deriving their conditions from the invariant.
No new kernel rules or implicit subtyping are introduced.

.. deppy-api:: crates/deppy-python/examples/refined_loop.py

.. deppy-api:: crates/deppy-python/examples/refined_loop_client.py
