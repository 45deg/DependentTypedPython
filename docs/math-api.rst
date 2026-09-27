Mathematical API
================

Canonical declarations are listed under their owning modules. Signatures and
constructor fields are extracted from checked source without running it.
The compiler provides ``Type``, ``Pi``, ``Sigma``, ``Pair``, and the builtin
Nat, Fin, Vec, and Eq forms; their preferred imports are ``deppy`` and the
module sections below. The demonstration Nat is a separate nominal family.

Core forms
----------

.. deppy-api:: crates/deppy-python/stdlib/deppy/_builtins.py
   :members: Type, Pi, Sigma, Pair

Equality
--------

.. deppy-api:: crates/deppy-python/stdlib/deppy/equality.py
   :members: Eq, refl, J, sym, trans, cong, transport, cong2, transport_refl, transport_trans

Logical data and decisions
--------------------------

.. deppy-api:: crates/deppy-python/stdlib/deppy/data.py
   :members: Empty, Unit, Bool, Sum, Option, Not, Decidable, sum_elim, decide_not, decide_and, decide_or, decide_implies, decision_weight, weight_yes, weight_no, weight_transport

Booleans
--------

.. deppy-api:: crates/deppy-python/stdlib/deppy/bool.py
   :members: negate, is_true, conjunction, disjunction, xor, true_ne_false, eq_decide, is_true_intro, is_true_elim, negate_involutive, conjunction_identity, conjunction_annihilator, conjunction_idempotent, conjunction_complement, conjunction_comm, conjunction_assoc, disjunction_identity, disjunction_annihilator, disjunction_idempotent, disjunction_complement, disjunction_comm, disjunction_assoc, negate_conjunction, conjunction_absorption, conjunction_distrib, negate_disjunction, disjunction_absorption, disjunction_distrib, xor_self, xor_comm, decision_bool, select, select_post, false_ne_true, decision_true, select_post_eq, bool_not, bool_eq, false_true_elim, true_false_elim, not_false, and_left, and_right, decision_true_intro

Natural numbers
---------------

.. deppy-api:: crates/deppy-python/stdlib/deppy/nat.py
   :members: Nat, Z, S, add, mul, add_zero, add_succ, add_assoc, add_comm, add_swap, mul_zero, mul_one, mul_add_right, mul_succ_left, zero_mul, zero_ne_succ, mul_comm, mul_add_left, mul_assoc, pred_or, succ_injective, add_left_cancel, add_right_cancel

Natural order
-------------

.. deppy-api:: crates/deppy-python/stdlib/deppy/nat_order.py
   :members: LE, LT, le_refl, le_step, le_pred, le_trans, not_succ_le_zero, le_decide_succ, le_decide_step, le_decide, lt_decide, le_total, lt_to_succ_le, le_lt_or_eq, strong_induction_all, strong_induction, lt_irrefl, le_weaken, lt_trans, le_zero_eq, le_antisymm, add_le_add_left, add_le_add_right, add_lt_add_right, mul_le_mul_right, mul_le_mul_left, mul_lt_succ, mul_lt_mul_left, mul_left_cancel_pos, pred_lt

Natural Boolean comparisons
---------------------------

.. deppy-api:: crates/deppy-python/stdlib/deppy/nat_bool.py
   :members: nat_le, nat_lt, nat_eq, nat_lt_true, nat_le_true, nat_eq_true, nat_le_refl_true, nat_lt_false_zero, lt_le_bound, pred_lt_true, nat_lt_not_false, equal, equal_true, equal_refl, equal_false, equal_nat_eq

Lists and removal
-----------------

.. deppy-api:: crates/deppy-python/stdlib/deppy/lists.py
   :members: List, length, Mem, NoDup, All, Any, all_get, all_decide, any_decide, search, append, mem_append_left, mem_append_right, mem_append_cases, map, append_assoc, map_identity, map_composition, length_append, length_map, map_append, snoc, reverse, reverse_append, map_reverse, length_reverse, reverse_snoc, reverse_involution, filter, filter_mem, filter_mem_intro, filter_nodup, count, length_filter_eq_count, count_le_length, length_filter_le, reject, count_split, Removal, find_removal, removal_mem, removal_length, map_mem, map_mem_reflect, map_nodup

Finite indices
--------------

.. deppy-api:: crates/deppy-python/stdlib/deppy/fin.py
   :members: Fin, FZ, FS, fin_case, to_nat, to_nat_lt, to_nat_injective

Vectors
-------

.. deppy-api:: crates/deppy-python/stdlib/deppy/vectors.py
   :members: Vec, VNil, VCons, vnil, vcons, get, map, get_map, vec_extensional, append, append_left_index, append_right_index, get_append_left, get_append_right, snoc, reverse, mirror_involution, reverse_get

Finite carriers
---------------

.. deppy-api:: crates/deppy-python/stdlib/deppy/finite.py
   :members: Enumeration, finite_count, finite_all_decide, finite_any_decide, finite_search, bijection_enumeration, bijection_cardinality, removal_present, removal_include, removal_keep, removal_nodup, removal_absent, removal_count, same_count, map_has, inverse_injective, bijection_count, count_map, weight_unique, weight_transport

Bijections
----------

.. deppy-api:: crates/deppy-python/stdlib/deppy/functions.py
   :members: Bijection, identity_bijection, inverse_bijection, compose_bijection, bijection_injective, bijection_surjective

Permutations
------------

.. deppy-api:: crates/deppy-python/stdlib/deppy/permutations.py
   :members: Permutation, perm_refl, perm_sym, perm_trans, perm_length, perm_mem, perm_mem_back, perm_nodup, perm_map

Arithmetic
----------

.. deppy-api:: crates/deppy-python/stdlib/deppy/arithmetic.py
   :members: sub, sub_add, divmod, quotient, remainder, divmod_bound, remainder_lt_true, divmod_equation

Signed integers
---------------

.. deppy-api:: crates/deppy-python/stdlib/deppy/integer.py
   :members: Int, of_nat, negative_nat, magnitude, negative, neg, add, sub, mul, le, lt, eq, quotient, remainder, to_nat, eq_true

Demonstration indexed types
---------------------------

These declarations demonstrate general inductives indexed by the canonical ``deppy.nat.Nat``.

.. deppy-api:: crates/deppy-python/stdlib/deppy/indexed.py
   :members: IVec, IFin, get

Implementation helpers
----------------------

These declarations remain importable for checked proof clients. They are not
recommended building blocks for new APIs.

.. deppy-api:: crates/deppy-python/stdlib/deppy/bool.py
   :members: false_type

.. deppy-api:: crates/deppy-python/stdlib/deppy/nat_bool.py
   :members: is_zero, equal_step, zero_equal, step_equal

Compatibility imports
---------------------

The following paths remain checked imports. Each link points to its canonical declaration.

.. list-table:: Compatibility aliases
   :header-rows: 1

   * - Compatibility path
     - Owning declaration
   * - ``deppy.finite.Removal``
     - :ref:`deppy.lists.Removal`
   * - ``deppy.finite.RemoveHere``
     - :ref:`RemoveHere <deppy.lists.removehere-constructor>`
   * - ``deppy.finite.RemoveThere``
     - :ref:`RemoveThere <deppy.lists.removethere-constructor>`
   * - ``deppy.finite.find_removal``
     - :ref:`deppy.lists.find_removal`
   * - ``deppy.finite.Has``
     - :ref:`deppy.lists.Mem`
   * - ``deppy.finite.Either``
     - :ref:`deppy.data.Sum`
   * - ``deppy.finite.Decision``
     - :ref:`deppy.data.Decidable`
   * - ``deppy.finite.Unit_``
     - :ref:`MkUnit <deppy.data.mkunit-constructor>`
   * - ``deppy.finite.either_elim``
     - :ref:`deppy.data.sum_elim`
   * - ``deppy.finite.map_injective_has``
     - :ref:`deppy.lists.map_mem_reflect`
   * - ``deppy.verified.decision_bool``
     - :ref:`deppy.bool.decision_bool`
   * - ``deppy.verified.select``
     - :ref:`deppy.bool.select`
   * - ``deppy.verified.select_post``
     - :ref:`deppy.bool.select_post`
   * - ``deppy.verified.select_post_eq``
     - :ref:`deppy.bool.select_post_eq`
   * - ``deppy.verified.decision_true``
     - :ref:`deppy.bool.decision_true`
   * - ``deppy.verified.decision_true_intro``
     - :ref:`deppy.bool.decision_true_intro`
   * - ``deppy.verified.bool_not``
     - :ref:`deppy.bool.bool_not`
   * - ``deppy.verified.bool_eq``
     - :ref:`deppy.bool.bool_eq`
   * - ``deppy.verified.false_ne_true``
     - :ref:`deppy.bool.false_ne_true`
   * - ``deppy.verified.false_true_elim``
     - :ref:`deppy.bool.false_true_elim`
   * - ``deppy.verified.true_false_elim``
     - :ref:`deppy.bool.true_false_elim`
   * - ``deppy.verified.not_false``
     - :ref:`deppy.bool.not_false`
   * - ``deppy.verified.and_left``
     - :ref:`deppy.bool.and_left`
   * - ``deppy.verified.and_right``
     - :ref:`deppy.bool.and_right`
   * - ``deppy.verified.false_type``
     - :ref:`deppy.bool.false_type`
   * - ``deppy.verified.nat_le``
     - :ref:`deppy.nat_bool.nat_le`
   * - ``deppy.verified.nat_lt``
     - :ref:`deppy.nat_bool.nat_lt`
   * - ``deppy.verified.nat_eq``
     - :ref:`deppy.nat_bool.nat_eq`
   * - ``deppy.verified.nat_lt_true``
     - :ref:`deppy.nat_bool.nat_lt_true`
   * - ``deppy.verified.nat_le_true``
     - :ref:`deppy.nat_bool.nat_le_true`
   * - ``deppy.verified.nat_eq_true``
     - :ref:`deppy.nat_bool.nat_eq_true`
   * - ``deppy.verified.nat_le_refl_true``
     - :ref:`deppy.nat_bool.nat_le_refl_true`
   * - ``deppy.verified.nat_lt_false_zero``
     - :ref:`deppy.nat_bool.nat_lt_false_zero`
   * - ``deppy.verified.lt_le_bound``
     - :ref:`deppy.nat_bool.lt_le_bound`
   * - ``deppy.verified.pred_lt_true``
     - :ref:`deppy.nat_bool.pred_lt_true`
   * - ``deppy.verified.nat_lt_not_false``
     - :ref:`deppy.nat_bool.nat_lt_not_false`
   * - ``deppy.arithmetic.equal``
     - :ref:`deppy.nat_bool.equal`
   * - ``deppy.arithmetic.equal_true``
     - :ref:`deppy.nat_bool.equal_true`
   * - ``deppy.arithmetic.equal_refl``
     - :ref:`deppy.nat_bool.equal_refl`
   * - ``deppy.arithmetic.equal_false``
     - :ref:`deppy.nat_bool.equal_false`
   * - ``deppy.arithmetic.is_zero``
     - :ref:`deppy.nat_bool.is_zero`
   * - ``deppy.arithmetic.equal_step``
     - :ref:`deppy.nat_bool.equal_step`
   * - ``deppy.arithmetic.zero_equal``
     - :ref:`deppy.nat_bool.zero_equal`
   * - ``deppy.arithmetic.step_equal``
     - :ref:`deppy.nat_bool.step_equal`

The ``verified`` compatibility functions remain real checked declarations for
compiler generated proof terms. The arithmetic equality names reexport the
same bindings from ``deppy.nat_bool``. The lists removal family replaces the
former finite nominal family, so previously extracted values must be regenerated.

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
``@verified``, exported by ``deppy.verified``. ``A`` is ``Nat``, ``Bool``, or ``Int``;
a return predicate receives the result and may capture entry arguments. It
replaces ``ensures`` and generates a VC. Bare ``@verified`` attempts bounded automatic proof;
``proofs`` can supply evidence for remaining goals. The function returns an
ordinary base value; its refinement theorem is available through ``verified_spec``.
Parameter predicates receive the argument value and may capture earlier entry
arguments. Their conditions, in parameter order, followed by an explicit
``requires`` are combined into a right-associated Sigma. A single condition is
used directly; no conditions means ``Unit``. The combined evidence is the
``pre`` argument of proof callbacks and the final argument of ``verified_spec``.
Local refinements use named assignment VCs; same-base condition conversions require checked evidence,
produced automatically or supplied explicitly. Implicit subtyping is not supported.
When ``invariant`` is omitted, loop state is inferred from assignments and its local
refinements supply an invariant candidate. Initialization and preservation are still proved.
``decreases(counter)`` specifies the current value as the natural-number measure.

.. deppy-api:: crates/deppy-python/examples/verified/fibonacci.py

Contract composition
--------------------

``@verified`` checks each call precondition and proves the
continuation for an arbitrary result satisfying the checked callee contract.
The result and its specification evidence are passed to subsequent proof
callbacks when explicitly supplied in ``proofs``. Unsolved entries become named goals
with source locations; ``auto=False`` disables automatic proof. Unfinished
proofs are never registered. Calls in expressions, loop initialization and bodies,
and after loops are supported; calls in while guards are not.

Single loops support ``loop.init``, ``loop.preserve``,
``loop.decrease`` and ``loop.exit`` proof entries. Multiple and nested loops
use source-order loop numbers in their goal names.

.. deppy-api:: crates/deppy-python/examples/verified/verified_composition.py

Refined argument composition
----------------------------

Missing call proofs produce named precondition goals. ``exact`` can use an
entry refinement or an earlier call's postcondition; ``rewrite`` can transform
the goal using that evidence. Every generated proof is kernel-checked.

.. deppy-api:: crates/deppy-python/examples/verified/refined_arguments.py

Local refinements and modular loops
-----------------------------------

Local ``Refined[Nat/Bool/Int, predicate]`` annotations capture their environment at
annotation time. Initialization and reassignment generate ``local.x.refined``
VCs, with numeric suffixes for later assignments. Conversions between conditions
on the same base type use these VCs or a callee's precondition VC.

Loop preservation and decrease proofs independently compose helper contracts.
Refined state variables also require ``loop.preserve.entry.local.x.refined``
(and decrease/exit counterparts), deriving their conditions from the invariant.
No new kernel rules or implicit subtyping are introduced.

.. deppy-api:: crates/deppy-python/examples/verified/refined_loop.py

.. deppy-api:: crates/deppy-python/examples/verified/refined_loop_client.py
