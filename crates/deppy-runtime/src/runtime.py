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
    raise TypeError('unreachable empty elimination')

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
        b = _validate(value[1], second(a), output)
        return (a, b)
    if kind == 'function':
        if not callable(value):
            raise TypeError('expected a callable')
        argument, result = args
        def checked(arg):
            arg = _validate(arg, argument, not output)
            return _validate(value(arg), result(arg), output)
        return checked
    if kind == 'data':
        return _validate_data(value, schema, output)
    if kind == 'record':
        tag, fields = args
        if (type(value) is not tuple or len(value) != 2 or value[0] is not tag
                or type(value[1]) is not tuple or len(value[1]) != len(fields)):
            raise TypeError('record nominal tag or arity mismatch')
        checked = []
        for i, field in enumerate(fields):
            checked.append(_validate(value[1][i], field(*checked), output))
        return (tag, tuple(checked))
    raise TypeError('unknown boundary schema')


# General data uses a separate nominal namespace from single-constructor records.
_DATA_SCHEMAS = {}

_NAT_ID = 18446744073709551613
_VEC_ID = 18446744073709551614
_FIN_ID = 18446744073709551615

def _is_vector(identifier):
    offset = _VEC_ID - identifier
    return 0 <= offset <= 2 * 4294967295 and offset % 2 == 0

def _data(identifier, constructor, fields):
    if identifier == _NAT_ID:
        return 0 if constructor == 0 else _succ(fields[0])
    if _is_vector(identifier):
        return () if constructor == 0 else _vcons(*fields)
    if identifier == _FIN_ID:
        return _fz(*fields) if constructor == 0 else _fs(*fields)
    return (_tag(('data', identifier)), constructor, fields)

def _data_fields(identifier, value, arities):
    if identifier == _NAT_ID:
        n = _natural(value)
        return (0, ()) if n == 0 else (1, (n - 1,))
    if _is_vector(identifier):
        if type(value) is not tuple:
            raise TypeError('expected an immutable vector')
        return (0, ()) if not value else (1, (len(value) - 1, value[0], value[1:]))
    if identifier == _FIN_ID:
        if type(value) is not tuple or len(value) != 2:
            raise TypeError('expected a finite index')
        bound, rank = value
        _fin(value, _natural(bound))
        return (0, (bound - 1,)) if rank == 0 else (1, (bound - 1, (bound - 1, rank - 1)))
    if (type(value) is not tuple or len(value) != 3
            or value[0] is not _tag(('data', identifier))
            or type(value[1]) is not int or not 0 <= value[1] < len(arities)
            or type(value[2]) is not tuple or len(value[2]) != arities[value[1]]):
        raise TypeError('inductive nominal tag or constructor arity mismatch')
    return value[1], value[2]

def _data_elim(identifier, recursion, branches, value):
    # An explicit postorder stack keeps direct recursion independent of Python's
    # call-stack limit. Function-valued recursive fields produce lazy IH functions.
    arities = tuple(len(fields) for fields in recursion)
    def function_ih(field, depth):
        if depth == 0:
            return _data_elim(identifier, recursion, branches, field)
        return lambda arg: function_ih(field(arg), depth - 1)
    stack = [(False, value)]
    results = []
    while stack:
        ready, node = stack.pop()
        c, fields = _data_fields(identifier, node, arities)
        plan = recursion[c]
        direct = [field for field, depth in zip(fields, plan) if depth == 0]
        if not ready:
            stack.append((True, node))
            stack.extend((False, child) for child in reversed(direct))
            continue
        count = len(direct)
        children = results[-count:] if count else []
        if count:
            del results[-count:]
        children = iter(children)
        result = branches[c]
        for field in fields:
            result = result(field)
        for field, depth in zip(fields, plan):
            if depth is not None:
                result = result(next(children) if depth == 0 else function_ih(field, depth))
        results.append(result)
    return results[0]


def _same_index(left, right):
    pending = [(left, right)]
    while pending:
        a, b = pending.pop()
        if a is b:
            continue
        if type(a) is not type(b):
            return False
        if type(a) is tuple:
            if len(a) != len(b):
                return False
            pending.extend(zip(a, b))
        elif type(a) is int:
            if a != b:
                return False
        else:
            # Nominal tags compare by identity; no user-defined equality runs.
            return False
    return True

def _validate_data(value, schema, output):
    pending = [('visit', value, schema)]
    results = []
    while pending:
        action, value, schema = pending.pop()
        if action == 'fields':
            c, fields, validators, result_indices, indices, i = schema
            if i < len(fields):
                checked = results[-i:] if i else []
                pending.append(('fields', value, (c, fields, validators, result_indices, indices, i + 1)))
                pending.append(('visit', fields[i], validators[i](*checked)))
                continue
            count = len(fields)
            checked = tuple(results[-count:]) if count else ()
            if count:
                del results[-count:]
            if not _same_index(result_indices(*checked), indices):
                raise TypeError('inductive result index mismatch')
            results.append((value[0], c, checked))
            continue
        if schema[0] != 'data':
            results.append(_validate(value, schema, output))
            continue
        _, identifier, parameters, indices = schema
        constructors = _DATA_SCHEMAS[identifier](*parameters)
        c, fields = _data_fields(identifier, value, tuple(len(fs) for fs, _ in constructors))
        validators, result_indices = constructors[c]
        pending.append(('fields', value, (c, fields, validators, result_indices, indices, 0)))
    return results[0]
