# verifiedの仕様と証明

`@verified` は、Nat／Boolの局所変数、再代入、`if`／`elif`／`else`、単一の `while`、`return` を持つ関数を検査する。
仕様と手書き証明はdecoratorの引数に置く。通常のPythonとしてこのdecoratorを実行するものではなく、
既存の静的frontendで読み、生成したCore項とVC証明をkernelで検査する。

```python
from __future__ import annotations
from deppy import Nat, Eq, refl
from deppy.nat import add
from deppy.verified import verified

@verified(
    ensures=lambda n, result: Eq[Nat, result, add(n, n)],
    proof=lambda n, pre: refl(add(n, n)),
)
def twice(n: Nat) -> Nat:
    x = n
    x = x + n
    return x
```

## 仕様と証明

- `requires` は入力引数を宣言順に受け取り、`Type` の命題を返す。省略時は `deppy.data.Unit`。
- `ensures` は入力引数、その後に戻り値を受け取り、`Type` の命題を返す。戻り値を `Refined` で指定する場合は省略する。
- `proof` は入力引数、その後に事前条件の証拠を受け取り、生成VCを証明する。必須。
  ループなしでは事後条件を直接証明し、ループがある場合は後述の四つのVCの組を返す。
- 仕様の入力引数は入口時点の値。本文で同名の引数へ再代入しても変化しない。
- 証明にはlambda、先に検査した定理、`hole("名前")` を使える。holeが残れば検証は未完了であり、
  `--goals`／`--json` で期待する型と文脈を確認できる。

例えば `proof=lambda n, pre: hole("twice_vc")` に置き換えると、
`Eq[Nat, add(n, n), add(n, n)]` に相当する証明課題が表示される。
本文の最後を `return n` に変えるとVCも変わり、元の証明は受理されない。

分岐の証明はBoolの消去に対応する。両分岐で同じ述語を証明する場合には、
`deppy.verified.select_post` を使える。完成した例は
[`examples/verified.py`](../crates/deppy-python/examples/verified.py) にある。
数値比較から順序の証拠を自動的に局所文脈へ導入する機能や自動証明探索はまだない。
`decision_true` を使えば、判定結果がTrueという等式から元の命題の証拠を取り出せる。

```sh
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/verified.py
cargo run -p deppy-python --locked --offline -- --goals path/to/proof.py
```

## Refinedの戻り値

`deppy.verified` から `Refined` をimportし、戻り値を
`Refined[Nat, lambda result: Eq[Nat, result, S(n)]]` のように指定できる。
述語は戻り値を一つ受け取り、入口時点の引数を参照できる。本文で `n` を更新しても、
述語の `n` は変わらない。述語を既存の事後条件へ変換し、同じVCとkernelで検査する。
`proof` は必須で、`requires` と `verified_spec` もそのまま使える。

現時点では `@verified` の戻り値専用で、基底型はNat／Boolに限る。
`ensures` との併記は拒否する。公開関数は基底型の値を返し、Σの包みを作らない。
引数・局所変数のrefinementやsubtypingは未対応である。

## HIRの意味論とVC

専用frontendは本文を代入・分岐・returnからなる小さなcommand HIRへ分類する。
式は元の位置情報を保ち、各経路の局所状態で名前解決・型検査する。
状態は局所名からNat／Boolの型と新しいCoreの束縛名への対応である。

- `x = e; c`：更新前の状態で `e` を評価するCore letを作り、`x` を新しい束縛に対応させて `c` を解釈する。
- `a, b = e1, e2`：全右辺を更新前の状態で解釈してから、各変数を新しい束縛へ対応させる。
- `if b: c1 else: c2; c`：Boolのeliminatorを作り、それぞれの状態で `c1; c`、`c2; c` を解釈する。
- `return e`：その状態の `e` を結果とする。後続のcommandは実行しない。
- いずれかの経路がreturnなしで終われば拒否する。分岐後の未初期化変数の使用も拒否する。

ループなしの部分言語の意味を純粋な全域関数 `D(inputs)` と定める。
事後条件を `Q(inputs, result)` とすると、最弱事前条件は
`WP(Q, body)(inputs) = Q(inputs, D(inputs))`。
生成VCは `Π inputs. requires(inputs) → Q(inputs, D(inputs))` である。
分岐の結果はBoolのeliminatorとしてこの項に含まれる。

実装はVC型に注釈した証明letと、同じ `D` を返す関数を一つのCore定義にする。
使われないletも型検査されるので、不正な証明は登録前に拒否される。
kernelに新しい規則や公理を追加しない。VC証明がユーザー公理に依存する場合は、
関数の公理依存として通常のレポートに残る。

これは定義したHIR意味論に対する検証である。元のCPython実行との意味保存や
生成Pythonでの新APIの実行検証は含まない。公開される関数の型は通常の引数・戻り値の型であり、
仕様は `verified_spec` で後続の証明から再利用できる。

## 受理範囲

- 引数・戻り値の基底型は公開 `Nat` または `deppy.data.Bool`。Natは非負整数であり、Pythonの負数を含むint全体ではない。
- 値は初期化済み局所変数、自然数リテラル、`True`／`False`、Natの `+`／`*`／`<`／`<=`。
- 先に検査した純粋な関数への位置引数による呼び出し。外部Python関数、属性呼び出し、再帰は拒否する。
- 新しい局所変数は右辺から型を決め、以後の再代入で型を変えない。純粋関数呼び出しの結果は
  期待型がない場合Natとして検査する。Boolを返す呼び出しで新しい局所変数を作る場合は `flag: Bool = f(...)` と書く。
- 同時代入は、異なる局所名の平坦なtupleと同じ要素数のtuple式に限る。入れ子・starred target・重複名は拒否する。
- `requires`／`ensures`／`proof` は既存のdependent式の構文を使う。
  仕様内では `add(n, 1)`、`LE[n, limit]` のように書き、本文用の演算子構文とは区別する。
- 最初のdocstringは許可する。その他の式文、heap更新、例外、I/O、async、型parameter、
  default／keyword引数、暗黙のNone returnは対象外。

経路ごとの継続展開は分岐数によって大きくなるため、既存のlowering budgetで制限する。
共有する制御フロー表現やネストしたloopは後続の段階で扱う。

## whileと停止性

ループには不変条件と自然数の減少尺度を指定する。`state` は、ループ中に更新する局所変数を
並べた明示的なtupleで、各変数はループ前に初期化しておく。
不変条件と尺度の関数は、その順序で現在の値を受け取る。

```python
counter = n
total = 0
while 0 < counter:
    invariant(lambda counter, total: Eq[Nat, add(counter, total), n],
              state=(counter, total))
    decreases(lambda counter, total: counter)
    total = S(total)
    counter = pred_or(0, counter)
return total
```

`invariant` と `decreases` は `deppy.verified_loop` からimportする静的な注釈で、
必ずwhile本文の先頭に、この順で置く。上の例で `n` はループ入口の値を捕捉し、
明示的な引数 `counter` と `total` は各反復の値を表す。

ループを含む関数の `proof` は、次の四つをnested Pairで返す。

```python
proof=lambda n, pre: Pair(
    initial_proof,
    Pair(preserve_proof, Pair(decrease_proof, exit_proof)),
)
```

| VC | 証明すること | 証明関数が受け取るもの |
| --- | --- | --- |
| 初期化 | 実際の初期状態で不変条件が成り立つ | 外側の入力と事前条件を利用して証拠を返す |
| 保存 | 実際の本文を一回実行した状態でも不変条件が成り立つ | 状態、不変条件の証拠、guardがTrueという等式 |
| 減少 | 本文実行後の尺度が実行前より厳密に小さい | 状態、不変条件の証拠、guardがTrueという等式 |
| 終了 | ループ後の代入・分岐・returnまで含めて事後条件が成り立つ | 状態、不変条件の証拠、guardがFalseという等式 |

尺度はNatなので非負性は型で保証される。`state=(counter, total)` の証明用状態は
`Sigma[Nat, lambda _: Sigma[Nat, lambda _: Unit]]` であり、`state.fst` がcounter、
`state.snd.fst` がtotalとなる。一変数の場合も末尾にUnitを置く。
各フィールドに `hole("preserve")` などを置いて、そのVCを確認できる。

完全な手書き証明を含む
[`examples/verified_loop.py`](../crates/deppy-python/examples/verified_loop.py) は、
カウントダウンと加算による累積を公理なしで検証する。

### 有限反復とwhileの接続

実行の意味は `iterate(guard, step, measure(initial), initial)` で表す。
`iterate` 自体はNatに対する構造的再帰であり、指定回数までの反復を表す。
**指定回数で止まることだけをwhileの停止証明とは扱わない。**

`iterate_invariant` が不変条件の保存を、`iterate_exit` が
「不変条件・保存・厳密減少・尺度が残り回数以下なら、結果のguardはFalse」を証明する。
初期回数には尺度そのものを使い、`loop_correct` が初期化・保存・減少・終了のVCから
関数の事後条件を導く。これらも通常のPython記法で書いたkernel検査済みの定理であり、
loop用のkernel規則や公理は追加しない。

コンパイラは `LoopVC` 型に注釈したユーザー証明と、`loop_correct` の適用から作る
関数全体のVC証明を両方検査する。本体を減らない更新にしたり、初期値・不変条件・尺度・
終了後の戻り値を変更した場合は、変更後のVCに合う証明が必要になる。
公理を使う証明は通常の公理依存レポートに残る。

保証は事前条件を満たす入力について成立する。事前条件を満たさない入力に対して、
有限反復の意味関数がwhileの動作に一致するとは主張しない。
CPythonソースとの意味保存や生成Pythonの実行についての境界は、ループなしの場合と同じ。

### ループの受理範囲

- 関数直下のwhileを一つだけ扱う。ループ前は局所代入、ループ後は代入・分岐・returnを許可する。
- 本文は代入と分岐。更新先は `state` に列挙した変数に限る。列挙していない変数は読み取り専用。
- stateにはNatとBoolを混在させられる。反復中に型は変えられない。
- 入れ子・複数のwhile、`while ... else`、`break`、`continue`、本文中のreturnは拒否する。
- 辞書式尺度、一般の整礎関係、自動不変条件推論は未実装。

## verified_specによる仕様の再利用

```python
from deppy.verified import verified_spec
from deppy.data import MkUnit

@theorem
def twice_spec(n: Nat) -> Eq[Nat, twice(n), add(n, n)]:
    return verified_spec(twice, n, MkUnit())
```

`verified_spec(f, 引数..., 事前条件の証拠)` は、検査済みの仕様定理を適用する静的な構文である。
最後の引数は `requires` の証拠。省略したrequiresはUnitなので `MkUnit()` を渡す。
例えば `advance` の事前条件が `LT(n, limit)` なら、その証拠が必要であり、Unitでは代用できない。
引数を途中まで適用した場合は、残りの引数を受け取る証明関数となる。

仕様定理の型は `Π inputs. requires(inputs) → ensures(inputs, f(inputs))`。
関数を登録した後、その関数自体を参照するこの型に対して、VCから得た証明を改めてkernelで検査し、
opaqueな定理として登録する。ループについては四つのVCと `loop_correct` による停止性の証明を
そのまま利用する。未検査の公理やsolverの成功フラグへ置き換える経路はない。

最初の引数は静的に解決できる `@verified` 関数名に限る。通常の `@dependent` 関数、
局所変数、式の結果を渡すと拒否する。関数を別名でimportした場合や再exportした場合も、
元の検査済み関数に対応する仕様定理を参照する。

`CheckedInterface` の関数entryには `verified_spec` IDを保存する。同じinterfaceのkernel snapshotで
その定理の型・本体・opaque属性を調べられる。生成定理の内部名はPythonの名前として公開しない。
moduleの本体・仕様・証明・事前条件が変われば、依存snapshotを無効化して再検査する。
仕様定理を利用した証明にも、元のユーザー公理への依存が通常のレポートとして伝播する。

[`examples/verified_spec.py`](../crates/deppy-python/examples/verified_spec.py) では、
別moduleの通常関数とループ関数の仕様を、任意の自然数について再利用している。

```sh
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/verified_spec.py
```

`f(inputs)` はこのfrontendが定義するHIRの意味関数である。仕様の再利用を追加しても、
元のCPythonソースとの意味保存や生成Python実行を検証したことにはならない。

## Fibonacciの実例

[`examples/fibonacci.py`](../crates/deppy-python/examples/fibonacci.py) は
`fib_loop(n) -> Refined[Nat, lambda result: Eq[Nat, result, fib_recursive(n)]]`
を検査する。純粋な仕様は構造的再帰で隣接する二項 `(F_n, F_(n+1))` を計算し、
`fib_step` が通常のFibonacci漸化式を証明する。

ループは `a, b = b, a + b` で更新する。不変条件は
`remaining + index = n`、`a = F_index`、`b = F_(index+1)` の組である。
`remaining` の厳密な減少と、終了時の `remaining = 0` から、停止性と結果の一致を証明する。
`fib_loop_correct` と `fib_loop_twice` は `verified_spec` で仕様を取り出し、後続の定理で再利用する。
これらの証明は公理に依存しない。

```sh
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/fibonacci.py
```

テストでは一般形の証明に加えて、入力0～3の具体値をCoreの正規化で検査する。
大きな入力の正規化はelaborationの処理予算に達し得る。これはCPythonでの実行性能の検証ではない。
