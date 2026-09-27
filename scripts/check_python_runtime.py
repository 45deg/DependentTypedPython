"""Compare committed source fixtures with generated Python (requires Python 3.14).

Run: uv run --python 3.14 scripts/check_python_runtime.py
Only repository fixtures are executed, using the test-only reference model.
"""
from pathlib import Path
import subprocess
import sys
import types
import reference_deppy as ref

if sys.version_info[:2] != (3, 14):
    raise SystemExit("Python 3.14 is required")

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / 'crates/deppy-python/examples/core'
sys.modules['deppy'] = ref
subprocess.run(['cargo', 'build', '-p', 'deppy-runtime', '--locked', '--offline'], cwd=ROOT, check=True)


def load(name):
    path = EXAMPLES / f'{name}.py'
    generated = subprocess.run(
        [str(ROOT / 'target/debug/deppy-runtime'), str(path)],
        check=True, text=True, capture_output=True,
    ).stdout
    source_module = types.ModuleType(f'reference_{name}')
    sys.modules[source_module.__name__] = source_module
    exec(compile(path.read_text(), str(path), 'exec'), source_module.__dict__)
    generated_module = {}
    exec(compile(generated, f'<generated {name}>', 'exec'), generated_module)
    return source_module, generated_module['exports']


checks = 0


def equal(source, generated):
    global checks
    assert ref.canonical(source) == generated, (source, generated)
    checks += 1


source, generated = load('basics')
for n in range(8):
    k = ref.natural(n)
    equal(source.identity(k), generated['identity'](n))
    equal(source.twice(k), generated['twice'](n))
    equal(source.reflexive(k), generated['reflexive'](n))
    equal(source.empty(k), generated['empty'](n))

source, generated = load('structural')
for n in range(8):
    for m in range(8):
        xs, ys = tuple(range(n)), tuple(range(m))
        equal(source.add(ref.natural(n), ref.natural(m)), generated['add'](n, m))
        equal(source.append(ref.natural(n), ref.natural(m), ref.vector(xs), ref.vector(ys)),
              generated['append'](n, m, xs, ys))

source, generated = load('proofs')
for n in range(8):
    equal(source.zero_right(ref.natural(n)), generated['zero_right'](n))
    xs = tuple(range(n))
    for i in range(n):
        equal(source.get(ref.natural(n), ref.vector(xs), ref.index(n, i)),
              generated['get'](n, xs, (n, i)))

source, generated = load('records')
for n in range(8):
    xs = tuple(range(n))
    packed = source.pack(ref.natural(n), ref.vector(xs))
    compiled_packed = generated['pack'](n, xs)
    equal(packed, compiled_packed)
    equal(source.as_pair(source.as_record(packed)),
          generated['as_pair'](generated['as_record'](compiled_packed)))
    equal(source.as_pair(source.SomeVec(ref.natural(n), ref.vector(xs))),
          generated['as_pair'](generated['SomeVec'](n, xs)))

source, generated = load('before_match')
for n in range(8):
    xs = tuple(range(n))
    equal(source.count(ref.natural(n)), generated['count'](n))
    equal(source.keep(ref.natural(n), ref.vector(xs)), generated['keep'](n, xs))
    equal(source.reflexive(ref.natural(n)), generated['reflexive'](n))

print(f'Python {sys.version.split()[0]}: {checks} source/generated comparisons passed')
