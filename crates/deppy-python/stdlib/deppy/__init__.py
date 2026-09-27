from deppy._builtins import inductive, constructor, Index, induct, absurd, dependent, theorem, hole, axiom, record, Type, Nat, Z, S, Vec, VNil, VCons, Fin, FZ, FS, Eq, refl, J, nat_elim, vec_elim, fin_elim, record_elim, ann, lam, implicit_lam, ImplicitPi, vnil, vcons, pair, fin0_elim, Pi, Sigma, Pair
from deppy.tactics import intro, exact, apply, rewrite, rewrite_in, cases, induction
from deppy.equality import sym, trans, cong, cong2, transport, transport_refl, transport_trans
from deppy.nat import add, mul, add_zero, add_succ, add_assoc, add_comm, add_swap, mul_zero, mul_one, mul_add_right, pred_or, succ_injective, add_left_cancel, add_right_cancel
from deppy.fin import fin_case
