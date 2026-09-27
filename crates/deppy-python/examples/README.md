# DepPy examples

| Directory | Contents |
| --- | --- |
| [`core/`](core/) | Dependent functions, indexed data, records, recursion, and equality proofs |
| [`verified/`](verified/) | Contracts, refined arguments, verified loops, and specification reuse |
| [`proof_case/`](proof_case/) | Cantor's theorem, Lagrange's theorem, and Fermat's theorem |

Examples with local imports keep their dependencies in the same directory. The examples are grouped by what they demonstrate:

| Topic | Examples |
| --- | --- |
| Pattern matching | [indexed matches](core/indexed_matches.py), [nested matches](core/nested_matches.py), [list patterns](core/list_patterns.py) |
| Recursion and induction | [list induction](core/list_induction.py), [list recursion](core/list_recursion.py), [tree size](core/tree_size.py), [tree depth](core/tree_depth.py) |
| Indexed data | [indexed get](core/indexed_get.py), [indexed length](core/indexed_length.py), [nested indexed get](core/nested_indexed_get.py) |
| Other checks | [docstrings](core/docstrings.py), [list theorems](core/list_theorems.py), [higher universe](core/higher_universe.py) |
| Order proofs | [bounds and countdown](core/order_bounds.py), [impossible indexed cases](core/order_absurd.py) |
