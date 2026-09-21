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
