# verifiedの仕様と証明

`@verified` は、Nat／Boolの局所変数、再代入、`if`／`elif`／`else`、複数・入れ子の `while`、Nat境界の `for range`、`continue`／`break`／`return` を持つ関数を検査する。
仕様は引数・戻り値・局所変数の型注釈を基本とする。`@verified` または `@verified()` で
VCを生成し、限定した自動証明を試す。解けないVCは名前付きgoalとして残り、検証済みとして登録しない。
`proof`／`proofs` は明示的な証明を与えるための追加インターフェースである。
通常のPythonとしてdecoratorや注釈を実行せず、静的frontendで読み、生成したCore項とVC証明をkernelで検査する。

```python
from __future__ import annotations
from deppy import Nat, Eq
from deppy.nat import add
from deppy.verified import verified, Refined

@verified
def twice(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, add(n, n)]]:
    x = n
    x = x + n
    return x
```

## 型注釈からの自動検証

`proof`／`proofs` の省略自体はエラーにならない。引数と戻り値の `Refined` が事前・事後条件、
局所変数の `Refined` が各代入で維持する条件になる。戻り値が単なるNat／Boolで `ensures` もなければ、
事後条件はUnitであり、より強い値の性質は主張しない。本文の型とループの停止性は引き続き検査する。

自動証明は、文脈中の証拠とΣの射影、等式の反射律、Unit・Σの構築、固定した自然数の順序補題を使う。
順序補題は反射律、厳密順序から非厳密順序への変換、推移律、正の入力に対する `pred_or(0, n)` の減少、
厳密減少による上界の保存を扱う。`<`／`<=` のTrue側の等式から順序の証拠を取り出し、
`0 < n` がFalseなら `n = 0` を導ける。補題の前提は既存の証拠・反射律で解き、再帰的な補題探索はしない。
各VCで探索回数を制限し、Σの分解・構築にも深さの上限を置く。一般の算術solverや完全な証明探索ではない。
任意のユーザー定理・公理を勝手に探索しない。生成した通常の証明項をkernelで再検査する。

`@verified(using=(add_zero, fib_preserve, fib_exit))` のように、使用する補題を追加できる。
`using` は既に検査された宣言名のタプルで、import時の別名にも対応する。
補題の結論をVCの型と照合して引数を推論し、残る前提を文脈中の証拠・反射律で解く。
推論できない引数や前提は未解決goalとして残す。補題同士の再帰的な連鎖は行わない。
明示した `proofs` が優先され、`using` は残りのVCにだけ適用される。
`auto=False` または単一の `proof=` と `using` の併用はエラーになる。
公理を明示した場合は、実際に生成された証明が使う公理への依存を記録する。


```python
@verified
def bounded_countdown(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, 0]]:
    counter: Refined[Nat, lambda value: LE[value, n]] = n
    while 0 < counter:
        decreases(counter)
        counter = decrement(counter)
    return counter
```

この例の `decrement` は、正の入力を要求し、入力より小さいNatを返すverified関数である。
importと補助関数を含む完成例は [`verified_annotations.py`](../crates/deppy-python/examples/verified_annotations.py) にある。

`invariant` を省略すると、本文が更新する変数を出現順にstateとして集め、その局所Refined条件を
不変条件候補にする。条件がなければUnit、一つならその条件、複数なら右結合のΣとする。
初期化と保存を証明してから利用し、注釈を無条件に仮定しない。state変数はループ前に初期化する。
Refined述語が捕捉した外部の値は注釈時点のままであり、不変条件候補の生成で捕捉先を変えない。
引数のRefinedは入口条件であり、引数への再代入の不変条件へ自動昇格させない。
`decreases(counter)` は反復時点の値を尺度とする。従来の `decreases(lambda counter: counter)` も使える。
複数変数の関係など、局所条件だけで足りなければ従来の `invariant(..., state=(...))` を明示する。

解けないVCにだけ `proofs={キー: 証明, ...}` を指定できる。明示した証明は必ず検査し、誤っていても
自動証明で置き換えない。明示的な `hole` も残す。`proofs={}` は自動証明を有効にしたまま、
残った課題を表示する。自動証明なしですべての課題を見る場合は `@verified(auto=False)` または
`@verified(auto=False, proofs={})` を使う。`auto` はTrue／Falseのリテラルに限る。

```sh
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/verified_annotations.py
cargo run -p deppy-python --locked --offline -- --goals path/to/program.py
```

Pythonの遅延注釈の実行時評価には依存しない。関数の入口値やSSAの局所値への束縛はDepPyの静的規則であり、
CPythonの `__annotations__` から局所注釈や呼び出し時の引数値を取得する仕組みではない。

## 仕様と証明

- `requires` は入力引数を宣言順に受け取り、`Type` の命題を返す。Refined引数の条件と合わせて事前条件とし、どちらもなければ `deppy.data.Unit`。
- `ensures` は入力引数、その後に戻り値を受け取り、`Type` の命題を返す。戻り値を `Refined` で指定する場合は省略する。
- `proof` は入力引数、その後に事前条件の証拠を受け取り、生成VCを証明する。省略できるが、指定時は `proofs` と併用しない。
  ループなしでは事後条件を直接証明し、ループがある場合は後述の四つのVCの組を返す。
- 仕様の入力引数は入口時点の値。本文で同名の引数へ再代入しても変化しない。
- 証明にはlambda、先に検査した定理、`hole("名前")` を使える。holeが残れば検証は未完了であり、
  `--goals`／`--json` で期待する型と文脈を確認できる。

例えばdecoratorを `@verified(proof=lambda n, pre: hole("twice_vc"))` にすると、
`Eq[Nat, add(n, n), add(n, n)]` に相当する証明課題が表示される。
本文の最後を `return n` に変えるとVCも変わり、自動証明は完成しない。

分岐の証明はBoolの消去に対応する。両分岐で同じ述語を証明する場合には、
`deppy.verified.select_post` を使える。完成した例は
[`examples/verified.py`](../crates/deppy-python/examples/verified.py) にある。
自動証明では、True側の比較の等式を順序の証拠へ変換できる。
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
必要なら `proof` または `proofs` で証明を補い、`requires` と `verified_spec` もそのまま使える。

`@verified` の引数と戻り値で使え、基底型はNat／Boolに限る。
`ensures` との併記は拒否する。公開関数は基底型の値を返し、Σの包みを作らない。
局所変数では後述の名前付きVCを使う。同じ基底型の条件変換もVCとして検査し、暗黙のsubtypingは行わない。

## Refined引数

`n: Refined[Nat, lambda value: Eq[Nat, value, 0]]` は、基底型Natの引数と
入口条件 `Eq[Nat, n, 0]` に変換する。述語は値を一つ受け取って `Type` の命題を返す。
先行する引数の入口値も参照できる。例えば
`limit: Nat, n: Refined[Nat, lambda value: LE(value, limit)]` と書ける。
自分自身の引数名と後続引数は述語の外部変数として参照できない。自分の値は述語の引数で受け取る。
本文での再代入は入口条件を変更しない。

引数の条件と明示的な `requires` を合わせたものが、関数の事前条件となる。
既存の `proof`／`proofs` callbackの `pre` と、`verified_spec` の最後の引数に使う証拠は次の形式である。

| 条件 | 事前条件と証拠 |
|---|---|
| 条件なし | `Unit` と `MkUnit()` |
| 条件が一つ | その命題と証拠を直接使う |
| 条件が二つ | `Sigma[P, lambda _: Q]` と `Pair(p, q)` |
| 条件が三つ | `Sigma[P, lambda _: Sigma[Q, lambda _: R]]` と `Pair(p, Pair(q, r))` |

条件はRefined引数の宣言順に並べ、明示的な `requires` があれば最後へ加える。
省略した `requires` のために余分なUnitを追加することはない。
引数が基底型だけの既存関数は、証拠の形式が変わらない。

[`examples/refined_arguments.py`](../crates/deppy-python/examples/refined_arguments.py) は、
`n = 0` を要求して `result = 1` を保証する関数と、`n = 1` を要求して `result = 2` を
保証する関数を合成する。各関数は `rewrite` で入力の証拠を使い、呼び出し元は次のtacticでVCを解く。

```python
@verified(proofs={
    "call.first.requires": lambda n, pre: exact(pre),
    "call.second.requires": lambda n, pre, first, first_spec: exact(first_spec),
    "return": lambda n, pre, first, first_spec, second, second_spec: exact(second_spec),
})
def composed(n: Refined[Nat, lambda value: Eq[Nat, value, 0]]) -> Refined[Nat, lambda result: Eq[Nat, result, 2]]:
    first = zero_to_one(n)
    second = one_to_two(first)
    return second
```

`auto=False` で最初の証明項目を削除すると `composed.call.first.requires` が名前付きgoalとして表示される。
`exact(pre)` を戻すと、その条件が入口の仮定から証明される。
呼び出し元を単なる `n: Nat` に変えた場合は、入口に `n = 0` の証拠がないため
同じtacticでは解けない。未解決goalを残した関数は検証済みとして登録しない。

```sh
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/refined_arguments.py
```

単一whileを持つ関数でもRefined引数を宣言でき、まとめた証拠を各ループVCの `pre` で使える。
ループ本体とループ後の継続でも、`proofs` による契約合成を使える。
この機能はverifiedの契約注釈であり、一般のΣ型の値や暗黙のsubtypingではない。
公開Core関数の引数は基底型のままで、保証を利用するには事前条件の証拠が必要となる。
CPython実行時の引数検査を追加する機能ではない。

## 契約による関数の合成と名前付きVC

`proof` を指定しない通常の検証では、verified関数への
`y = f(x)` または `return f(x)` を契約で検証する。まず呼び出し時点の引数について
事前条件を証明し、続きは抽象的な結果 `y` と事後条件の証拠を使って証明する。
続きの証明を任意の結果について検査した後、実際の呼び出し値と `verified_spec` の証拠を適用する。
呼び出し先の本体を展開して続きの証明を済ませることはできない。
最終的な仕様定理は従来と同じkernelで再検査する。

[`examples/verified_composition.py`](../crates/deppy-python/examples/verified_composition.py) では、
`zero_to_one` の事前条件が `n = 0`、事後条件が `result = 1`、
`one_to_two` の事前条件が `n = 1`、事後条件が `result = 2` である。
二つを次のように合成できる。

```python
@verified(
    requires=lambda n: Eq[Nat, n, 0],
    proofs={
        "call.first.requires": lambda n, pre: pre,
        "call.second.requires": lambda n, pre, first, first_spec: first_spec,
        "return": lambda n, pre, first, first_spec, second, second_spec: second_spec,
    },
)
def composed(n: Nat) -> Refined[Nat, lambda result: Eq[Nat, result, 2]]:
    first = zero_to_one(n)
    second = one_to_two(first)
    return second
```

証明callbackの引数は、入口の入力引数、事前条件の証拠、経路上で得た証拠の順である。
各契約呼び出しは「結果・その事後条件の証拠」を追加し、各分岐は
`Eq[Bool, condition, True_()]` または `Eq[Bool, condition, False_()]` を追加する。
通常の局所代入はcallbackの引数を増やさない。再代入後も過去の呼び出しの証拠は
その時点の結果についての証拠であり、更新後の変数の条件としては使えない。
callbackは、この文脈と同じ個数の位置引数を持つlambda、または同じ順序で適用できる検査済みの補題とする。

| VCのキー | 証明する内容 |
|---|---|
| `call.y.requires` | `y = f(...)` の事前条件 |
| `call.y.2.requires` | 同じ経路での二回目の `y = f(...)` の事前条件 |
| `call.return.requires` | `return f(...)` の事前条件 |
| `return` | 関数の事後条件 |
| `then.return` / `else.return` | 各分岐経路の事後条件 |
| `then.call.y.requires` | True側の経路にある呼び出しの事前条件 |

入れ子の分岐では `then.else.` のように経路名を重ねる。通常の分岐の継続は共有するが、
契約やassertの証明は到達条件の異なる各経路で検査する。
キーは関数ごとに指定し、表示時には `composed.call.first.requires` のように関数名を付ける。
キーの重複、未知のキー、余った証明は拒否する。

`@verified(auto=False)` から始めると、各項目を独立したgoalとして表示できる。
`--goals` と `--json` は、名前・期待型・文脈・呼び出しやreturn式のソース位置を出力する。
未解決goalがあれば関数も仕様定理も検証完了として登録しない。

```sh
cargo run -p deppy-python --locked --offline -- --goals path/to/program.py
cargo run -p deppy-python --locked --offline -- --json path/to/program.py
```

呼び出し先はNat／Boolを扱う検査済みverified関数で、単一whileを含む関数も利用できる。
importの別名と再exportでも契約を保持し、公理への依存を合成先へ伝える。
呼び出し先の本体・契約が変われば依存snapshotを無効化する。

契約呼び出しは引数・算術式・ifの条件・条件式・同時代入の右辺と、ループ前の初期化・本文・終了後で扱う。
内部の一時変数へ左から右に正規化し、各呼び出しの事前条件を証明する。同時代入では全右辺の評価後に左辺を更新する。
一時変数の呼び出しgoalは `call.$exprN.requires` となり、元の呼び出し式のソース位置を持つ。
番号は正規化に依存するため、手書き証明を指定するときは `--goals` で確認する。
whileのguard内の契約呼び出しは未対応。ループ前の分岐は自動証明または `proofs` で扱う。
`proof=` だけでverified関数を通常の純粋関数として呼び出す経路も拒否する。
異なる基底型への変換、暗黙のrefinement subtyping、一般の証明探索、heap更新は未対応である。


## 基本式とassert

Natの `+`／`*` に加え、次の演算子を扱う。表の右辺は型注釈・手書き証明で使う式であり、
プログラムの比較構文をそのまま命題の注釈内に記述する構文糖は導入していない。

| プログラムの式 | 対応するBool値／命題 |
| --- | --- |
| `n < m`、`n <= m` | `nat_lt(n, m)`、`nat_le(n, m)`。Trueの証拠から `LT(n,m)`、`LE[n,m]` を得る |
| `n > m`、`n >= m` | `nat_lt(m, n)`、`nat_le(m, n)` |
| `n == m` | `nat_eq(n, m)`。`nat_eq_true` で `Eq[Nat,n,m]` を得る |
| `a == b`（Bool） | `bool_eq(a, b)` |
| `a != b` | 等価比較の `bool_not` |
| `not a` | `bool_not(a)`。入力はBoolのみ |
| `a and b`、`a or b` | Boolに限定した短絡評価。オペランドの値を返すPythonの一般的な演算には広げない |
| `x if p else y` | Boolの `p` に従って選択する条件式 |

上記の関数・補題は `deppy.verified` からimportできる。
`+=` は初期化済みNat局所変数への加算と再代入として扱い、局所Refinedも再検証する。
契約呼び出しを含む `and`／`or` と条件式は分岐へ正規化する。各分岐の契約VCは到達条件の証拠を受け取り、
到達不能な経路ではBoolの矛盾を除去する検査済み補題を利用できる。

`assert p` は `Eq[Bool, p, True_()]` のVCを生成する。goal名は `assert.test.holds`、
二つ目以降は `assert.test.2.holds` などで、分岐内では経路名も付く。
証明済みの等式を後続の文脈へ追加する。偽のassertを仮定として使うことはできない。
メッセージ付きassertと、`proof=` の一括証明でのassertは未対応。

正規化も検査予算を消費する。分岐後の継続の意味関数を共有しても、経路ごとのVCは残るため、
多数の短絡演算・条件式を重ねる場合は予算超過になることがある。契約呼び出しを含まない式は
Boolの消去で表し、後続の継続を複製しない。

## 局所Refinedと同じ基底型の条件変換

`proof` による一括証明を使わない関数では、`x: Refined[Nat, predicate] = value` と宣言できる。
基底型はNat／Bool。初期化、再代入、同時代入の各更新で `predicate(新しい値)` のVCを生成する。
`x: Nat = ...` と再注釈しても既存の条件は消えない。同じ局所名へのRefinedの再宣言は拒否する。
述語が参照する外部の値は注釈を処理した時点で固定する。例えば `x` の条件に `limit` を
参照した後で `limit` を更新しても、`x` の条件は元の値を参照する。

| VCのキー | 証明する内容 |
|---|---|
| `local.x.refined` | 初期化後の `x` が宣言した条件を満たす |
| `local.x.2.refined` | 二回目の代入後もその条件を満たす |
| `then.local.x.refined` | True側での代入後の条件 |

callbackには更新後の値を追加し、証明後のcallbackにはその証拠も追加する。
契約呼び出しの戻り値がすでに文脈にある場合、同じ値は重複して追加しない。
同時代入は全右辺を更新前の状態で評価し、左辺の順に条件を検査する。
過去の値と証拠は残るが、新しい値の条件を無条件に仮定することはない。

同じNatについて `Eq[Nat, x, 0]` から `LE[x, 0]` に変換する場合も、
代入先または呼び出し先の条件を証明するVCを使う。例えば前者の証拠 `zero` があれば、
`rewrite(zero, le_refl(0))` で後者を証明できる。基底型は変えず、条件の含意を
手書き補題やtacticで明示する。変換用の新しいkernel規則や実行時の包装は追加しない。

### ループ内の契約合成

[Refinedループの実例](../crates/deppy-python/examples/refined_loop.py) は、
`counter ≤ n` を局所変数の条件と不変条件にし、正の入力から小さい値を返す
`decrement` の契約だけで保存と減少を証明する。
[別moduleの証明](../crates/deppy-python/examples/refined_loop_client.py) は
`verified_spec` でその結果を再利用する。

| VCのキー | 証明する内容 |
|---|---|
| `loop.preserve.call.counter.requires` | 保存の証明中に呼び出す補助関数の事前条件 |
| `loop.decrease.call.counter.requires` | 減少の証明中の同じ呼び出しの事前条件 |
| `loop.preserve.local.counter.refined` | 更新後の局所条件 |
| `loop.preserve.entry.local.counter.refined` | 任意の反復状態で、不変条件から局所条件を復元できる |
| `loop.decrease.entry.local.counter.refined` | 減少の証明の入口で同じ条件を復元できる |
| `loop.exit.entry.local.counter.refined` | 終了状態でも局所条件を復元できる |
| `loop.exit.call.y.requires` | ループ後の契約呼び出しの事前条件 |

保存と減少は独立したVCである。自動で解けない呼び出しの証拠はそれぞれ指定する。
callbackは入力・事前条件・ループ前の証拠に続き、状態・不変条件・guardの等式、
その経路で得た値と証拠を受け取る。不変条件だけでは局所条件を導けなければ
`entry.local` のgoalが残る。ループ前の初期化の証拠を反復後の値へ流用しない。

本文の分岐は `loop.preserve.then.call.x.requires` のように経路名を含め、
末尾の保存・減少は `loop.preserve.then`、`loop.decrease.else` などになる。
ループ後の分岐の事後条件は `loop.exit.then.return` などで指定する。
手書き証明とtacticはどちらも通常のCore証明項になり、同じkernel検査を通る。

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
本体を直接解釈する `proof=` 方式では、
事後条件を `Q(inputs, result)` とすると、最弱事前条件は
`WP(Q, body)(inputs) = Q(inputs, D(inputs))`。
生成VCは `Π inputs. requires(inputs) → Q(inputs, D(inputs))` である。
分岐の結果はBoolのeliminatorとしてこの項に含まれる。
`proofs=` 方式では、呼び出しの事前条件と、結果を全称化した継続の証明を組み合わせ、
同じ `requires(inputs) → Q(inputs, D(inputs))` の証明へ接続する。

実装はVC型に注釈した証明letと、同じ `D` を返す関数を一つのCore定義にする。
使われないletも型検査されるので、不正な証明は登録前に拒否される。
kernelに新しい規則や公理を追加しない。VC証明がユーザー公理に依存する場合は、
関数の公理依存として通常のレポートに残る。

これは定義したHIR意味論に対する検証である。元のCPython実行との意味保存や
生成Pythonでの新APIの実行検証は含まない。公開される関数の型は通常の引数・戻り値の型であり、
仕様は `verified_spec` で後続の証明から再利用できる。

## 受理範囲

- 引数・戻り値の基底型は公開 `Nat` または `deppy.data.Bool`。Natは非負整数であり、Pythonの負数を含むint全体ではない。
- 値は初期化済み局所変数、自然数リテラル、`True`／`False`、Natの `+`／`*`、比較 `==`／`!=`／`<`／`<=`／`>`／`>=`、Boolの `and`／`or`／`not`、条件式。
- 先に検査したdependent関数への位置引数による呼び出し。verified関数の呼び出しは後述の契約合成で扱う。外部Python関数、属性呼び出し、再帰は拒否する。
- 新しい局所変数は右辺から型を決め、以後の再代入で型を変えない。純粋関数呼び出しの結果は
  期待型がない場合Natとして検査する。Boolを返す呼び出しで新しい局所変数を作る場合は `flag: Bool = f(...)` と書く。
- 同時代入は、異なる局所名の平坦なtupleと同じ要素数のtuple式に限る。入れ子・starred target・重複名は拒否する。
- `requires`／`ensures`／`proof` は既存のdependent式の構文を使う。
  仕様内では `add(n, 1)`、`LE[n, limit]` のように書き、本文用の演算子構文とは区別する。
- 最初のdocstringは許可する。その他の式文、heap更新、例外、I/O、async、型parameter、
  default／keyword引数、暗黙のNone returnは対象外。

経路ごとの継続展開は分岐数によって大きくなるため、既存のlowering budgetで制限する。
合成するループの本文は保存・減少をまとめて検証し、意味関数と本文の証明をletで共有する。
通常の分岐では、両経路から合流する変更済みの状態をtupleにして、後続の関数を共有する。
契約呼び出し・assertの証拠は各経路で検査する。自動証明で事後条件がUnitだけの計算の継続は、
自明な証明も繰り返し探索しない。途中脱出や局所Refined宣言を持つ分岐は個別に合成する。

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
明示する場合はwhile本文の先頭に、この順で置く。不変条件を省略する場合は `decreases` を先頭に置く。上の例で `n` はループ入口の値を捕捉し、
明示的な引数 `counter` と `total` は各反復の値を表す。

従来の関数直下の単一whileに対する `proof` は、次の四つをnested Pairで返す。

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

### whileの名前付き証明

単一whileでは、従来のnested Pairの代わりに `proofs` を使える。
キーは `loop.init`、`loop.preserve`、`loop.decrease`、`loop.exit` の四つ。
初期化のcallbackは入力引数、事前条件の証拠、ループ前のRefined代入で得た値と証拠を受け取り、残りの三つは続けて
状態、不変条件の証拠、guardの等式を受け取る。
[Fibonacciの実例](../crates/deppy-python/examples/fibonacci.py) は `using` による補題適用でこの辞書を省略する。

未指定で自動証明もできない項目が名前付きgoalになる。`auto=False` なら未指定の全項目がgoalになる。初期化・保存はinvariant述語、減少はmeasure、
終了はreturn式のソース位置を示す。生成した四つの証明は既存の `LoopVC` にまとめ、
`loop_correct` で関数全体の仕様を導く。分岐があれば経路ごとにgoalを生成する。

### ループの合成とcontinue

複数・入れ子・分岐内のwhile、ループ前の文の分岐、continue・break・ループ内returnを含む関数では、
自動証明または `proofs` で各ループを検証する。

```python
@verified
def nested(n: Nat) -> Refined[Nat, lambda r: Eq[Nat, r, 0]]:
    x = n
    y = 0
    while 0 < x:
        decreases(x)
        y = x
        while 0 < y:
            decreases(y)
            y = pred_or(0, y)
            continue
        x = pred_or(0, x)
    return x
```

内側ループの初期化・保存・減少・終了を証明してから、その終了状態で外側の本文を検証する。
連続するループでも、前のループの不変条件とguardがFalseという証拠を次の初期化で使える。
`continue` は最も内側のループの残りの本文を飛ばす。その地点の状態について、
不変条件の保存と尺度の厳密減少を証明する。更新前にcontinueする非停止経路は受理しない。

ループ番号は関数内のソース順で1から付け、外側を内側より先に数える。
合成時のgoalには経路と番号を含める。

| 例 | 意味 |
| --- | --- |
| `loop.1.init` | 最初のループの初期化 |
| `loop.1.step.preserve` / `loop.1.step.decrease` | 本文終了時の保存・減少 |
| `loop.1.step.then.decrease` | 本文のthen経路の減少 |
| `loop.1.step.call.y.requires` | 本文中の契約呼び出しの事前条件 |
| `loop.1.step.loop.2.init` | 内側ループの初期化 |
| `loop.1.exit.loop.2.init` | 最初のループが終了した後の次のループの初期化 |
| `loop.1.exit.return` | ループ終了後の関数の事後条件 |

callbackにはその地点までの文脈が渡る。内側では外側の状態・不変条件・guardの証拠も含む。
本文は保存と減少の組を事後条件として一度合成するため、同じ経路の契約VCを両者で重複生成しない。
既存の単一while（ループ前の文の分岐・途中脱出・continueなし）のgoal名とcallbackは変更しない。

### breakとループ内return

`break` は最も内側のループを抜け、その地点の状態でループ後の継続を検証する。
ここにはguardがFalseという証拠を渡さない。次の反復がないので、break地点での
ループ不変条件の保存や尺度の減少は要求しない。ただし、局所Refinedの代入条件は引き続き検査する。
`return` はすべてのループを抜け、返す値について関数の事後条件をその地点で検証する。
契約呼び出しを返す場合もcalleeの仕様だけを使う。

通常の反復と途中脱出は既存のSum／Sigmaによる別の結果で表し、`run` と `run_correct` で接続する。
尺度が0でも直ちにbreak／returnできる。次の反復へ進む経路では、従来どおり保存・厳密減少が必要になる。
たとえば `loop.1.step.break.return` はbreak後の継続でのreturn、`loop.1.step.return` はループ内returnのgoal。
到達しない後続文のVCは生成しない。未対応の構文は到達性にかかわらずfrontendで拒否する。

### for range

`range(stop)`、`range(start, stop)`、`range(start, stop, step)` を扱う。
境界はNatに限定し、stopは含まない。step省略時は1、正のNat式は昇順、負の整数リテラルは降順とする。
動的な負step、負の境界、Bool／float、キーワード引数、for-else、shadowされたrangeは拒否する。

```python
@verified
def count(n: Nat) -> Nat:
    i = 0
    total = 0
    for i in range(n):
        assert i < n
        total += 1
    return total
```

現行の局所変数規則に合わせ、targetはループ前に初期化済みのNatに限定する。
空のrangeでは本文を実行せず、targetの入口の値を保つ。
境界とstepは左から右に一度だけ評価し、契約呼び出しもその地点で検査する。
stepの絶対値が正であることは `range.step.positive` のVCになり、ソース位置はstepの式を指す。
0のstepは空のrangeでも拒否する。動的stepには `Refined[Nat, lambda s: LT(0, s)]` などで証拠を渡せる。

内部でcursorと残り回数を保持し、自然数の構造的再帰で反復回数を計算する。
本文への入口には元の範囲の比較と残り回数が正という条件を使う。
本文でtargetや元の境界変数を変更しても、次の要素は入口で確定した範囲に従う。
continueでもcursorと残り回数は進み、break／returnは通常の途中脱出として検証する。
`invariant(..., state=(...))` は本文の先頭に置ける。stateにはtargetと更新する利用者の変数を列挙する。
内部変数は自動で補い、利用者の不変条件には渡さない。`decreases` の指定は不要。

基本例は既定の検査予算で検証する。ネストしたrangeと途中脱出の証明は大きくなり、
検査予算やスタックの追加が必要な場合がある。回帰テストの複合例は1,600万stepと16 MiBを指定している。
既定値は変更しておらず、予算超過を検証成功とは扱わない。

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

- 自動証明または `proofs` では複数・入れ子・分岐内のwhileと、ループ前の分岐を扱う。
  単一の `proof=` は従来の関数直下の単一whileに限る。
- 本文は代入・分岐・assert・while・for range・continue・break・return。更新先は `state` に列挙した変数に限る。
  内側ループのstateも外側のstateに含める。不変条件を省略した場合は内側のstateも含めて推論する。
  stateに含めない変数は読み取り専用で、すべてのstate変数は各ループに入る前に初期化する。
- stateにはNatとBoolを混在させられる。反復中に型は変えられない。
- `while ... else` と `for ... else` は拒否する。
- 辞書式尺度、一般の整礎関係、局所Refined以外からの一般的な不変条件推論は未実装。

## verified_specによる仕様の再利用

```python
from deppy.verified import verified_spec
from deppy.data import MkUnit

@theorem
def twice_spec(n: Nat) -> Eq[Nat, twice(n), add(n, n)]:
    return verified_spec(twice, n, MkUnit())
```

`verified_spec(f, 引数..., 事前条件の証拠)` は、検査済みの仕様定理を適用する静的な構文である。
最後の引数は、Refined引数の条件と `requires` を合わせた事前条件の証拠。どちらもない場合はUnitなので `MkUnit()` を渡す。
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

`@verified(using=(add_zero, fib_preserve, fib_exit))` で必要な補題を指定し、証明辞書は使わない。
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
