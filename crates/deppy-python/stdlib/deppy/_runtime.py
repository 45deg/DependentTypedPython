"""Execution primitives for the shared DepPy sources; no proof checking.

Contracts and equality-proof results are erased. Callers must satisfy the preconditions
checked separately by DepPy. This module is not used by the Rust checker.
"""
import ast
import textwrap
import functools
import inspect
import sys
import types
from dataclasses import make_dataclass


class _Marker:
    @classmethod
    def __class_getitem__(cls, arguments):
        return cls


Type = Index = Refined = Eq = Pi = Sigma = ImplicitPi = _Marker


class Nat(int):
    @property
    def predecessor(self):
        return Nat(self - 1)

    def __add__(self, other):
        return Nat(int(self) + other)

    __radd__ = __add__

    def __mul__(self, other):
        return Nat(int(self) * other)

    __rmul__ = __mul__

    def __sub__(self, other):
        return _natural(int(self) - other)

    def __floordiv__(self, other):
        return _natural(int(self) // other)

    def __mod__(self, other):
        return _natural(int(self) % other)


class _Zero(type):
    def __instancecheck__(cls, value):
        return isinstance(value, int) and not isinstance(value, bool) and value == 0


class _Succ(type):
    def __instancecheck__(cls, value):
        return isinstance(value, Nat) and value > 0


class Z(metaclass=_Zero):
    def __new__(cls):
        return Nat(0)


class S(metaclass=_Succ):
    __match_args__ = ('predecessor',)

    def __new__(cls, n):
        return Nat(n + 1)


def _natural(value):
    # Make Python literals usable by the source's Z()/S(k) patterns.
    return Nat(value) if type(value) is int and value >= 0 else value


class _Function:
    def __init__(self, function, *, erased=False, signed=False):
        functools.update_wrapper(self, function, assigned=("__module__", "__name__", "__qualname__", "__doc__"))
        self.function = function
        self.erased = erased
        self.signed = signed

    def __getitem__(self, arguments):
        arguments = arguments if isinstance(arguments, tuple) else (arguments,)
        params = getattr(self.function, '__type_params__', ())
        if len(arguments) > len(params):
            raise TypeError(f'{self.__name__}: too many implicit arguments')
        replacements = dict(zip((p.__name__ for p in params), arguments))
        closure = self.function.__closure__
        if closure:
            closure = tuple(types.CellType(replacements[name]) if name in replacements else cell
                            for name, cell in zip(self.function.__code__.co_freevars, closure))
        specialized = types.FunctionType(self.function.__code__, self.function.__globals__,
                                         self.function.__name__, self.function.__defaults__, closure)
        specialized.__kwdefaults__ = self.function.__kwdefaults__
        specialized.__type_params__ = params[len(arguments):]
        return _Function(specialized, erased=self.erased, signed=self.signed)

    def __call__(self, *args, **kwargs):
        if self.erased:
            return _PROOF
        # DepPy accepts both f(x, y) and curried f(x)(y).
        if not kwargs and len(args) < self.function.__code__.co_argcount:
            return functools.partial(self, *args)
        result = self.function(*map(_natural, args), **{k: _natural(v) for k, v in kwargs.items()})
        return _signed(result) if self.signed and isinstance(result, int) else _natural(result)


def _syntax(value):
    # Do not request __annotations__: dependent annotations can run arbitrary
    # expressions, even through Python 3.14's STRING annotation format.
    try:
        return ast.parse(textwrap.dedent(inspect.getsource(value))).body[0]
    except (OSError, TypeError, IndentationError, SyntaxError):
        return None


def dependent(function=None, **options):
    if function is None:
        return lambda f: dependent(f, **options)
    node = _syntax(function)
    result = ast.unparse(node.returns) if node is not None and node.returns else ''
    return _Function(function, erased=result.startswith('Eq['),
                     signed=result == 'Int' or result.startswith('Refined[Int,'))


def verified(function=None, **options):
    # Never evaluate requires/ensures/proof/proofs/using.
    return dependent(function) if function is not None else lambda f: dependent(f)


def theorem(function=None, **options):
    # Opaqueness is a checker property; a theorem may return computational data.
    return dependent(function, **options)


class _Proof:
    """Opaque erased evidence, never a certificate of verification."""
    def __repr__(self):
        return '<erased proof>'


_PROOF = _Proof()


def refl(value):
    return _PROOF


def _noop(*args, **kwargs):
    return None


def _proof(*args, **kwargs):
    return _PROOF


def absurd(*args):
    raise RuntimeError('DepPy reached an impossible branch; check input preconditions')


def hole(*args):
    raise NotImplementedError('An unresolved DepPy hole has no Python implementation')


def axiom(function):
    @functools.wraps(function)
    def unavailable(*args, **kwargs):
        raise NotImplementedError(f'axiom {function.__name__} has no Python implementation')
    return _Function(unavailable)


def constructor(function):
    function._deppy_constructor = True
    return function


def _data_class(name, fields, *, bases=(), module=__name__):
    def initialize(self, *args, **kwargs):
        if len(args) > len(fields):
            raise TypeError(f'{name}: too many fields')
        values = dict(zip(fields, args))
        for key, value in kwargs.items():
            if key not in fields or key in values:
                raise TypeError(f'{name}: unexpected or duplicate field {key}')
            values[key] = value
        if len(values) != len(fields):
            raise TypeError(f'{name}: expected fields {fields}')
        for field in fields:
            object.__setattr__(self, field, _natural(values[field]))
    return make_dataclass(name, [(field, object) for field in fields], bases=bases,
                          namespace={'__init__': initialize,
                                     '__class_getitem__': classmethod(lambda cls, args: cls)},
                          frozen=True, module=module)


def inductive(cls=None, **options):
    if cls is None:
        return lambda c: inductive(c, **options)
    # Constructors are declared once in the existing standard-library source.
    constructors = [(name, value) for name, value in vars(cls).items()
                    if getattr(value, '_deppy_constructor', False)]
    cls.__class_getitem__ = classmethod(lambda cls, args: cls)
    for index, (name, function) in enumerate(constructors):
        fields = function.__code__.co_varnames[:function.__code__.co_argcount]
        generated = _data_class(name, fields, bases=(cls,), module=cls.__module__)
        generated._deppy_index = index
        node = _syntax(function)
        generated._deppy_recursive = tuple(
            field.arg for field in node.args.args
            if field.annotation and cls.__name__ in {n.id for n in ast.walk(field.annotation) if isinstance(n, ast.Name)}
        ) if node else ()
        if cls.__module__ == 'deppy.data' and cls.__name__ == 'Bool':
            generated.__bool__ = lambda self: self._deppy_index == 1
        if cls.__module__ == 'deppy.integer' and cls.__name__ == 'Int':
            generated.__int__ = lambda self: (int(self.value) if self._deppy_index == 0
                                             else -int(self.predecessor) - 1)
            for method, operation in _INT_OPERATIONS.items():
                setattr(generated, method, operation)
        setattr(cls, name, generated)
        setattr(sys.modules[cls.__module__], name, generated)
    return cls


def record(cls=None, **options):
    if cls is None:
        return lambda c: record(c, **options)
    node = _syntax(cls)
    if node is None:
        raise TypeError('DepPy records require an inspectable source declaration')
    fields = tuple(stmt.target.id for stmt in node.body if isinstance(stmt, ast.AnnAssign))
    return _data_class(cls.__name__, fields, module=cls.__module__)


def _signed(value):
    from deppy.integer import Pos, Neg
    return Pos(value) if value >= 0 else Neg(-value - 1)


_INT_OPERATIONS = {
    '__add__': lambda a, b: _signed(int(a) + int(b)),
    '__sub__': lambda a, b: _signed(int(a) - int(b)),
    '__mul__': lambda a, b: _signed(int(a) * int(b)),
    '__floordiv__': lambda a, b: _signed(int(a) // int(b)),
    '__mod__': lambda a, b: _signed(int(a) % int(b)),
    '__neg__': lambda a: _signed(-int(a)),
    '__radd__': lambda a, b: _signed(int(b) + int(a)),
    '__rsub__': lambda a, b: _signed(int(b) - int(a)),
    '__rmul__': lambda a, b: _signed(int(b) * int(a)),
    '__rfloordiv__': lambda a, b: _signed(int(b) // int(a)),
    '__rmod__': lambda a, b: _signed(int(b) % int(a)),
    '__lt__': lambda a, b: int(a) < int(b),
    '__le__': lambda a, b: int(a) <= int(b),
    '__gt__': lambda a, b: int(a) > int(b),
    '__ge__': lambda a, b: int(a) >= int(b),
    '__eq__': lambda a, b: int(a) == int(b) if isinstance(b, (int, type(a))) or getattr(type(b), '__module__', '') == 'deppy.integer' else False,
    '__hash__': lambda a: hash(int(a)),
}


class Vec(_Marker):
    pass


class Fin(_Marker):
    pass


Pair = _data_class('Pair', ('fst', 'snd'))
VNil = _data_class('VNil', (), bases=(Vec,))
VCons = _data_class('VCons', ('length', 'head', 'tail'), bases=(Vec,))
FZ = _data_class('FZ', ('bound',), bases=(Fin,))
FS = _data_class('FS', ('bound', 'predecessor'), bases=(Fin,))


def _apply(function, *arguments):
    # Branch lambdas can be either multi-argument or explicitly curried.
    while arguments:
        if isinstance(function, _Function):
            count = function.function.__code__.co_argcount
        else:
            count = len(inspect.signature(function).parameters)
        if count == 0:
            function = function()
            continue
        if len(arguments) < count:
            return lambda *rest: _apply(function, *arguments, *rest)
        function = function(*arguments[:count])
        arguments = arguments[count:]
    return function


def nat_elim(level, motive, zero, succ, value):
    result = zero
    for k in range(value):
        result = _apply(succ, Nat(k), result)
    return result


def vec_elim(level, element, motive, nil, cons, size, value):
    if isinstance(value, VNil):
        return nil
    return _apply(cons, value.length, value.head, value.tail,
                  vec_elim(level, element, motive, nil, cons, value.length, value.tail))


def fin_elim(level, motive, zero, succ, size, value):
    if isinstance(value, FZ):
        return _apply(zero, value.bound)
    return _apply(succ, value.bound, value.predecessor,
                  fin_elim(level, motive, zero, succ, value.bound, value.predecessor))


def induct(level, value, motive, *branches):
    if isinstance(value, int):
        return nat_elim(level, motive, *branches, value)
    if isinstance(value, Vec):
        return vec_elim(level, None, motive, *branches, 0, value)
    if isinstance(value, Fin):
        return fin_elim(level, motive, *branches, 0, value)
    fields = [getattr(value, field) for field in value.__match_args__]
    hypotheses = []
    for field in value._deppy_recursive:
        child = getattr(value, field)
        if callable(child):
            hypotheses.append(lambda *args, child=child: induct(level, child(*args), motive, *branches))
        else:
            hypotheses.append(induct(level, child, motive, *branches))
    branch = branches[value._deppy_index]
    return _apply(branch, *fields, *hypotheses) if fields else branch


def cases(value, branches):
    value = _natural(value)
    for constructor, branch in branches.items():
        if isinstance(value, constructor):
            fields = tuple(getattr(value, name) for name in getattr(constructor, '__match_args__', ()))
            return _apply(branch, *fields) if fields else branch
    return absurd(value)


def J(level, element, start, motive, base, end, proof):
    return base


def _identity(value, *args):
    return value


_IMPLEMENTATIONS = {
    'invariant': _noop, 'decreases': _noop, 'verified_spec': _proof,
    'intro': _identity, 'exact': _identity, 'apply': lambda function, *args: _apply(function, *args),
    'rewrite': lambda equality, proof: proof,
    'rewrite_in': lambda equality, proof: proof,
    'cases': cases, 'induction': induct,
    'ann': _identity, 'lam': lambda domain, body: body,
    'implicit_lam': lambda domain, body: body,
    'vnil': lambda element: VNil(),
    'vcons': lambda element, length, head, tail: VCons(length, head, tail),
    'pair': lambda element, first, second: Pair(first, second),
    'fin0_elim': absurd,
    'record_elim': lambda level, motive, branch, value: _apply(
        branch, *(getattr(value, field) for field in value.__match_args__)),
}


def builtin(declaration):
    name = declaration.__name__
    implementation = _IMPLEMENTATIONS.get(name, globals().get(name))
    if implementation is None:
        raise NotImplementedError(f'Missing Python primitive: {name}')
    # Compiler primitives may also carry explicit erased type applications.
    if getattr(declaration, '__type_params__', ()) and not isinstance(implementation, type):
        return _Primitive(implementation)
    return implementation


class _Primitive:
    def __init__(self, function):
        self.function = function

    def __getitem__(self, arguments):
        return self

    def __call__(self, *args, **kwargs):
        return self.function(*args, **kwargs)
