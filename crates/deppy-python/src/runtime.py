# Generated DepPy runtime. Values use immutable canonical representations.
# This module contains checked declarations only; source assertions and ordinary
# Python functions are not copied or executed.
class _Proof:
    __slots__ = ()

_PROOF = _Proof()
_ERASED_PROOF = _Proof()

def _natural(n):
    if type(n) is not int or n < 0:
        raise TypeError('expected a nonnegative integer')
    return n

def _zero():
    return 0

def _succ(n):
    return _natural(n) + 1

def _vnil():
    return ()

def _vcons(k, head, tail):
    _natural(k)
    if type(tail) is not tuple or len(tail) != k:
        raise TypeError('vector tail length mismatch')
    return (head,) + tail

def _fz(k):
    return (_natural(k) + 1, 0)

def _fs(k, pred):
    _natural(k)
    if type(pred) is not tuple or len(pred) != 2 or pred[0] != k:
        raise TypeError('finite index predecessor bound mismatch')
    _fin(pred, k)
    return (k + 1, pred[1] + 1)

def _fin(value, bound):
    if (type(value) is not tuple or len(value) != 2
            or type(value[0]) is not int or type(value[1]) is not int
            or value[0] != bound or not 0 <= value[1] < bound):
        raise TypeError('finite index out of bounds')
    return value

def _pair(a, b):
    return (a, b)

def _fst(p):
    return p[0]

def _snd(p):
    return p[1]

def _refl():
    return _PROOF

def _erased_proof():
    return _ERASED_PROOF

def _j(base, proof):
    if proof is not _PROOF:
        raise TypeError('invalid equality proof token')
    return base

def _absurd(value):
    raise TypeError('unreachable Fin[0] elimination')

def _nat_elim(zero, step, n):
    result = zero
    for k in range(_natural(n)):
        result = step(k)(result)
    return result

def _vec_elim(nil, cons, xs):
    if type(xs) is not tuple:
        raise TypeError('expected an immutable vector')
    result = nil
    for position in range(len(xs) - 1, -1, -1):
        tail = xs[position + 1:]
        result = cons(len(tail))(xs[position])(tail)(result)
    return result

def _fin_elim(zero, step, index):
    bound, rank = index
    _fin(index, bound)
    result = zero(bound - rank - 1)
    for offset in range(rank):
        k = bound - rank + offset
        result = step(k)((k, offset))(result)
    return result

def _record(tag, fields):
    return (_tag(tag), fields)

def _record_elim(tag, branch, value):
    if type(value) is not tuple or len(value) != 2 or value[0] is not _tag(tag):
        raise TypeError('record nominal tag mismatch')
    for field in value[1]:
        branch = branch(field)
    return branch

_TAGS = {}

def _tag(identifier):
    if identifier not in _TAGS:
        _TAGS[identifier] = object()
    return _TAGS[identifier]

def _opaque(value):
    if value is None or type(value) in (bool, int, float, str, bytes):
        return value
    if type(value) is tuple:
        return tuple(_opaque(item) for item in value)
    if any(value is tag for tag in _TAGS.values()):
        return value
    raise TypeError('opaque values must be immutable canonical data')

def _validate(value, schema, output=False):
    kind, *args = schema
    if kind == 'opaque':
        return _opaque(value)
    if kind == 'type':
        if value is not None:
            raise TypeError('runtime types are erased')
        return None
    if kind == 'nat':
        return _natural(value)
    if kind == 'proof':
        if not output or (value is not _PROOF and value is not _ERASED_PROOF):
            raise TypeError('unchecked Python cannot supply equality proofs')
        return None
    if kind == 'vec':
        element, length = args
        _natural(length)
        if type(value) is not tuple or len(value) != length:
            raise TypeError('vector length mismatch')
        return tuple(_validate(x, element, output) for x in value)
    if kind == 'fin':
        return _fin(value, _natural(args[0]))
    if kind == 'pair':
        if type(value) is not tuple or len(value) != 2:
            raise TypeError('expected an immutable dependent pair')
        first, second = args
        a = _validate(value[0], first, output)
        b = _validate(value[1], second(value[0]), output)
        return (a, b)
    if kind == 'record':
        tag, fields = args
        if (type(value) is not tuple or len(value) != 2 or value[0] is not tag
                or type(value[1]) is not tuple or len(value[1]) != len(fields)):
            raise TypeError('record nominal tag or arity mismatch')
        checked = []
        for i, field in enumerate(fields):
            checked.append(_validate(value[1][i], field(*value[1][:i]), output))
        return (tag, tuple(checked))
    raise TypeError('unknown boundary schema')
