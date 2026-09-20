from __future__ import annotations

# A stable import surface for propositions and decisions.  These are aliases,
# not fresh declarations, so values can cross deppy.data/deppy.logic imports.
from deppy.data import Empty, Unit, MkUnit, Bool, False_, True_, Sum, Left, Right, Option, None_, Some, Not, Decidable, Yes, No, sum_elim, decide_not, decide_and, decide_or, decide_implies, decision_weight, weight_yes, weight_no, weight_transport
