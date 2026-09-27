"""Run with an installed package: python -m unittest discover -s tests."""
import importlib
import pkgutil
import runpy
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import deppy
from deppy import dependent, theorem, Nat, Z, S, Eq, record, Type, Vec
from deppy.data import False_, True_, Some, Left
from deppy.integer import of_nat, neg, Pos, Neg
from deppy.verified import verified
from deppy.verified_loop import invariant, decreases

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / 'crates/deppy-python/examples'
sys.path.insert(0, str(EXAMPLES / 'verified'))


def must_not_run(*args, **kwargs):
    raise AssertionError('annotation or contract executed')


@dependent
def deferred(n: must_not_run()) -> must_not_run():
    return n


@theorem
def computational_theorem() -> Nat:
    return 7


@dependent
def explicit[n: Nat]() -> Nat:
    return n


@record
class DependentRecord[T: Type]:
    size: Nat
    values: Vec[T, self.size]


class PackageTests(unittest.TestCase):
    def test_installed_script_from_other_directory(self):
        with tempfile.TemporaryDirectory() as cwd:
            result = subprocess.run(
                [sys.executable, '-I', str(EXAMPLES / 'verified/direct.py')],
                cwd=cwd, text=True, capture_output=True, check=True,
            )
        self.assertEqual(result.stdout, '42\n')

    def test_existing_examples_execute_as_scripts(self):
        for path in sorted(EXAMPLES.rglob('*.py')):
            with self.subTest(path=path.name):
                result = subprocess.run([sys.executable, str(path)], text=True,
                                        capture_output=True, timeout=20)
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_every_public_module_imports(self):
        for module in pkgutil.iter_modules(deppy.__path__):
            importlib.import_module(f'deppy.{module.name}')

    def test_native_naturals_and_pattern_matching(self):
        from deppy.nat import add, pred_or
        self.assertEqual(add(4, 5), 9)
        self.assertEqual(add(4)(5), 9)
        self.assertEqual(pred_or(99, 0), 99)
        self.assertEqual(pred_or(99, S(5)), 5)
        self.assertIsInstance(Z(), Nat)

    def test_dependent_annotations_are_not_evaluated(self):
        self.assertEqual(deferred(3), 3)
        self.assertEqual(computational_theorem(), 7)
        self.assertEqual(explicit[6](), 6)
        self.assertEqual(DependentRecord(0, deppy.VNil()).size, 0)

    def test_contracts_are_not_evaluated(self):
        @verified(requires=must_not_run, ensures=must_not_run,
                        proof=must_not_run, proofs={'return': must_not_run})
        def run(n: Nat) -> Nat:
            invariant(must_not_run, state=(n,))
            decreases(n)
            return n + 1
        self.assertEqual(run(2), 3)

    def test_shared_generic_functions_and_constructors(self):
        from deppy.lists import Cons, Nil, length
        from deppy.data import sum_elim
        self.assertEqual(length(Cons(1, Cons(2, Nil()))), 2)
        self.assertEqual(sum_elim[Nat, Nat, Nat](Left[Nat, Nat](4), lambda x: x + 1, lambda x: x), 5)
        self.assertEqual(Some[Nat](4).value, 4)
        self.assertFalse(False_())
        self.assertTrue(True_())

    def test_eliminators_and_indexed_values(self):
        tree = runpy.run_path(str(EXAMPLES / 'core/tree_depth.py'))
        self.assertEqual(tree['depth'](tree['Node'](lambda n: tree['Leaf']())), 1)
        from deppy.indexed import ICons, INil, IFS, IFZ, get
        vector = ICons(1, 7, ICons(0, 9, INil[Nat]()))
        self.assertEqual(get(vector, IFS(1, IFZ(0))), 9)
        from deppy.tactics import intro, apply, cases
        self.assertEqual(apply(intro(lambda x: x + 1), 4), 5)
        self.assertEqual(cases(3, {Z: 99, S: lambda k: k}), 2)
        step = lambda k, ih, x: ih(x) + 1
        self.assertEqual(deppy.nat_elim(0, None, lambda x: x, step, 2)(5), 7)

    def test_existing_fibonacci_source(self):
        from fibonacci import fib_loop, fib_recursive
        expected = [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]
        for n, value in enumerate(expected):
            self.assertEqual(fib_loop(n), value)
            self.assertEqual(fib_recursive(n), value)

    def test_existing_numeric_source(self):
        import math
        from verified_numeric import gcd, subtract, signed_div, signed_mod
        for a in range(8):
            for b in range(8):
                self.assertEqual(gcd(a, b), math.gcd(a, b))
                self.assertEqual(subtract(a, b), max(0, a - b))
        for a in range(-4, 5):
            for b in range(-3, 4):
                left = of_nat(a) if a >= 0 else neg(of_nat(-a))
                right = of_nat(b) if b >= 0 else neg(of_nat(-b))
                self.assertEqual(int(signed_div(left, right)), a // b if b else 0)
                self.assertEqual(int(signed_mod(left, right)), a % b if b else 0)
                self.assertIsInstance(signed_div(left, right), (Pos, Neg))
        self.assertEqual(int(2 + neg(of_nat(3))), -1)
        self.assertEqual(int(2 - neg(of_nat(3))), 5)

    def test_axioms_and_holes_fail_explicitly(self):
        @deppy.axiom
        def unknown() -> Nat: ...
        with self.assertRaises(NotImplementedError):
            unknown()
        with self.assertRaises(NotImplementedError):
            deppy.hole('unfinished')


if __name__ == '__main__':
    unittest.main()
