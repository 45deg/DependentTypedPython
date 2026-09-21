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
type ``ensures(inputs, function(inputs))``. An omitted ``requires`` means
``Unit`` and therefore requires ``MkUnit()`` as the final argument. User axiom
dependencies remain visible when the theorem is reused.

Refined returns and Fibonacci
-----------------------------

``Refined[A, predicate]`` is compiler-provided return annotation syntax for
``@verified``, exported by ``deppy.verified``. ``A`` is ``Nat`` or ``Bool``;
the predicate receives the result and may capture entry arguments. It replaces
``ensures`` and requires the same checked VC proof. The function returns an
ordinary base value; its refinement theorem is available through ``verified_spec``.
Parameter refinements, local refinements and subtyping are not supported.

.. deppy-api:: crates/deppy-python/examples/fibonacci.py
