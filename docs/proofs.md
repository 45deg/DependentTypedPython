# Pythonで書く証明とライブラリ

Python frontendから、既存kernelの依存関数・依存対・等式消去・Nat/Vec/Fin/recordの消去を明示できます。型推論や `match` の自動変換が扱えない場合は、型・引数・motiveを明示して証明項を書けます。`@dependent` の本体は検査対象の純粋な部分言語です。CPythonを実行して証明を取り出す仕組みではありません。

## ライブラリの利用

```python
from __future__ import annotations
from deppy import dependent, Nat, Eq, refl, trans


@dependent
def reflexive(n: Nat) -> Eq[Nat, n, n]:
    return trans(refl(n), refl(n))
```

標準ライブラリのソースは `crates/deppy-python/stdlib/deppy/` にあります。Rustのバイナリに同梱し、利用時に通常の宣言としてelaborateし、kernelで再検査します。

| モジュール | 定義 |
| --- | --- |
| `deppy` | 通常利用する言語構文・基本型・コンストラクタ・消去子・等式補題をまとめたprelude |
| `deppy.core` | `dependent`・`axiom`・`Type`・`Pi`・明示的なλと型注釈 |
| `deppy.nat` | `Nat`・`Z`・`S`・`nat_elim` |
| `deppy.equality` | `Eq`・`refl`・`J` と、Jから定義した `sym`・`trans`・`cong`・`transport` |
| `deppy.sigma` | `Sigma`・`Pair`・型を明示する `pair` |
| `deppy.fin` | `Fin`・`FZ`・`FS`・消去子と、依存分岐 `fin_case` |
| `deppy.vectors` | `Vec`・コンストラクタ・消去子と、`get`・`reverse`・参照補題など |
| `deppy.records` | `record`・`record_elim` |

通常のコードではトップレベルpreludeを使い、`get`・`reverse` のようなライブラリ操作は責務別モジュールからimportします。kernel primitiveとPythonで書いた派生定義は、利用者からは同じドメインモジュールに見えます。Rust frontendに `cong`・`trans` の呼び出し専用変換はありません。Rust用のelaborator APIと例が使う `prelude::cong` などは別に残っています。また、`+` や構造的 `match` の構文変換は引き続きRustが担当します。

`examples/reverse.py` はライブラリを利用する構造的帰納法の証明です。`examples/reverse_explicit.py` は同じ型の証明を `@dependent`、`vec_elim`、Pythonライブラリの `fin_case` だけで書いています。どちらも公理なしで検査できます。

## 自分のライブラリを別ファイルにする

例えば、同じディレクトリの `lemmas.py` に上の `reflexive` を置き、`main.py` で次のように使えます。

```python
from __future__ import annotations
from deppy import dependent, Nat, Eq
from lemmas import reflexive as lemma


@dependent
def result(n: Nat) -> Eq[Nat, n, n]:
    return lemma(n)
```

```sh
cargo run -p deppy-python --locked --offline -- path/to/main.py
cargo run -p deppy-runtime --locked --offline -- path/to/main.py
```

CLIの検索ルートは入力ファイルの親ディレクトリです。`from proofs.lemmas import lemma` は、そのルートの `proofs/lemmas.py`、または `proofs/lemmas/__init__.py` を読みます。ルート外へ出るsymlinkは拒否します。Pythonのimport機構、site-packages、`sys.path`、パッケージ初期化コードは実行しません。

対応するのは絶対指定の `from module import name`、alias、検査済み宣言の再exportです。recordと公理もimportできます。循環import、相対import、ワイルドカードimport、動的import、通常の未装飾Python関数の利用は拒否します。モジュール名で定義を分離するため、異なるライブラリの同名関数やrecordは混同しません。宣言順・前方参照禁止は各モジュール内でも維持します。

読み込むソースは1ファイル1 MB、グラフ全体8 MB、import深さ32に制限し、モジュール数にも上限を設けています。各宣言のelaborationとkernel検査には有限のステップ予算があります。

Rust APIでは、`deppy-python`の`check_module_with_resolver`と`deppy-runtime`の`compile_module_with_resolver`に`SourceResolver`を渡せます。`FileResolver`はCLIと同じファイル解決を提供します。resolverを取らない`check_module`・`compile_module`は標準ライブラリだけを解決し、カレントディレクトリを暗黙には読みません。

生成Pythonの `exports` に載るのは入力モジュール自身の宣言です。importした関数を外部から実行したい場合は、入力モジュールでラッパーを定義してください。ライブラリの高階関数は検査済み内部呼び出しとして利用でき、外部Pythonとの高階関数の境界には、呼び出し時に引数・結果を検査するwrapperを付けます。外部callbackの停止性は証明しません。対応するschemaの制約は[一般帰納型のruntime境界](dependent-phase1.md)を参照してください。

## 型とλを明示する

通常の `lambda x: ...`、`lambda x, y: ...` は期待される依存関数型で検査します。期待型が得られない位置では次を使えます。

```python
helper = lam(Nat, lambda x: x)
helper2 = ann(lambda x: x, Pi[Nat, lambda x: Nat])
```

| 構文 | 意味 |
| --- | --- |
| `Pi[A, lambda x: B]` | 明示引数の依存関数型 |
| `ImplicitPi[A, lambda x: B]` | 暗黙・実行時消去引数の依存関数型 |
| `lam(A, lambda x: body)` | 引数型を指定したλ |
| `implicit_lam(A, lambda x: body)` | 暗黙引数のλ |
| `ann(value, A)` | 値を型 `A` と照合する注釈 |
| `f[a, b]` | 暗黙引数を明示的に適用 |
| `Sigma[A, lambda x: B]`・`Pair(a, b)` | 依存対。値は期待型で検査 |
| `pair(SigmaType, a, b)` | 依存対の型を明示する構築 |
| `vnil(A)`・`vcons(A, n, head, tail)` | 要素型を明示するVec構築。高いuniverseにも対応 |

`def name() -> A` は型付きの定数宣言として使用できます。`name()` と `name` はその定数を参照します。引数が必要な関数への空の呼び出しは拒否します。局所補助関数は型注釈付きのλを不変のローカル変数に束縛して記述できます。任意のPython文や副作用は受け付けません。

## Eliminatorを直接使う

`level` は戻り値のmotiveのuniverseを指定する具体的な非負整数です。universeは非累積的であり、型が合わなければ拒否します。motiveは「対象とともに、証明する性質がどう変わるか」を記述する型族です。

| 呼び出し | motiveと分岐 |
| --- | --- |
| `J(level, A, x, C, base, y, proof)` | `C : (z : A) → Eq[A,x,z] → Type[level]`、`base : C(x,refl(x))`、`proof : Eq[A,x,y]` |
| `nat_elim(level, P, zero, step, n)` | `P : Nat → Type[level]`、`zero : P(0)`、`step : (k : Nat) → P(k) → P(S(k))` |
| `vec_elim(level, A, P, nil, cons, n, xs)` | `P : (k : Nat) → Vec[A,k] → Type[level]`、consの引数は `k, head, tail, ih` |
| `fin_elim(level, P, zero, step, n, i)` | `P : (k : Nat) → Fin[k] → Type[level]`、zeroの引数は `k`、stepは `k, pred, ih` |
| `record_elim(level, P, branch, value)` | recordをvalueから推論。branchは宣言順のフィールドを受け取り、`P(そのコンストラクタ値)` を返す |
| `fin0_elim(A, impossible)` | `Fin[0]` の値から任意の型 `A` を得る。`fin0_elim(impossible)` は従来のType₀の期待型推論版 |

例えば `trans` のライブラリ実装は次のとおりです。

```python
@dependent
def trans[A: Type, x: A, y: A, z: A](
    p: Eq[A, x, y], q: Eq[A, y, z],
) -> Eq[A, x, z]:
    return J(0, A, y, lambda end, proof: Eq[A, x, end], p, z, q)
```

標準の等式補題はType₀用です。より高いuniverse用の補題も、`Type[level]` と `J` の具体的levelを指定してPythonで定義できます。universe polymorphismは未実装です。

## 公理

公理は専用の `@axiom` 宣言にし、本体は単独の `...` に限定します。例として関数外延性を宣言する `examples/axioms.py` を用意しています。

```python
@axiom
def assumed[A: Type](x: A, y: A) -> Eq[A, x, y]:
    ...
```

これは例示用の強い仮定であり、この宣言から導いた結果はその仮定に依存します。kernelは公理の型の整合性を検査しますが、公理自体を証明したとは扱いません。

公理は本体を持たない不透明な定数です。正規化で `refl` に置き換えたり、`Eq[A,x,y]` を仮定しただけで `x` と `y` を定義的に等しいと扱ったりしません。未解決meta、`@dependent` の `...`、不正な証明を公理として受理することもありません。

CLIは各公開宣言を `[axiom-free]` または `[axioms: ...]` と表示します。Rust APIの `CheckedModule.axiom_dependencies` からも確認できます。追跡には宣言の型、型注釈、参照先の定義・recordも含みます。これは構文上の依存関係であり、必要な公理の最小集合を探索する処理ではありません。

公理には実行実装がありません。公開した公理そのものや、実行時に公理の値・証明トークンを必要とするコードは`deppy-runtime`のコード生成で拒否します。実行可能な証明トークンや公理の実装は捏造しません。公理に依存する証明でも、結果として消去する場合はコード生成できます。公理への依存情報は引き続き保持します。現在のコード生成は読み込んだ透明な定義全体を消去検査するため、未使用のライブラリ関数でも実行時に公理を必要とすれば生成を拒否する場合があります。

## 到達範囲

現在のkernelの型・定数・公理・eliminatorを組み合わせる証明は、Rustに補題を追加せずPythonで記述できます。必要な注釈を省略したときの型推論や、すべてのPythonパターンマッチの自動変換を保証するものではありません。明示的な証明でも有限の計算・スタック制限には従います。

一般のユーザー定義再帰帰納型・添字付き帰納型の宣言は[Phase 1の構文](dependent-phase1.md)で扱えます。universe polymorphism、自動証明探索、任意のPythonとの混在実行は未対応です。既存の `@record` は非再帰・単一コンストラクタのままです。


## 証明の消去

`Kernel::erase` は全体の型検査後、`Eq` 型の結果に至る証明計算を消去します。たとえば `reverse_get` の再帰や `sym` の `J` は、証明を返すだけなら実行しません。生成Pythonの公開結果は従来どおり `None` です。内部では消去済み結果を専用マーカーで表し、実行時の `J` が要求する証明トークンとは区別します。kernelの簡約・変換判定・公理依存の追跡は変更しません。

```python
@dependent
def erased[p: Eq[Nat, 0, 0]]() -> Eq[Nat, 0, 0]:
    return sym(p)

@dependent
def keep[p: Eq[Nat, 0, 0]](n: Nat) -> Nat:
    unused_proof = p
    return n
```

`p` は角括弧内の暗黙引数なので消去対象です。最初の例は証明結果全体が消え、二番目は `unused_proof` の実行時使用がないため束縛ごと消えます。生成Pythonではそれぞれ引数なし、`n` のみで呼び出します。元の言語では引き続き証明引数が必要で、未解決の証明を穴として認める変更ではありません。

消去条件は次のとおりです。

- 結果位置で型が `Eq` と判定できる項は、計算全体を消去します。
- `Eq` 型のlet束縛は、その変数を実行時に使わずに本体を消去できる場合だけ除去します。
- 実行時引数、データのフィールド、消去子に渡す値は、後で `J` が使う可能性があるため証明計算を保持します。高階関数にも同じ規則を適用します。
- データを返す `J` が消去指定の証明を要求すれば、コンパイル時に拒否します。公理の実行実装を要求する場合も拒否します。

証明を計算に使う場合、透明なグローバル定義は証明計算を保持する形で展開します。消去済みのグローバル結果を再利用しないための処理です。展開には既存の計算予算を適用しますが、生成コードが大きくなる場合があります。

これは保守的な使用検査です。明示的な証明引数を自動で暗黙引数に変えたり、record・Sigma・Vec内の証明フィールドを削除したりはしません。一般の `transport` の証明トークンも保持します。実行例は `crates/deppy-python/examples/proof_erasure.py` にあります。


## 名前付きholeとgoal表示

```python
from __future__ import annotations
from deppy import dependent, Nat, Eq, hole

@dependent
def identity_proof(n: Nat) -> Eq[Nat, n, n]:
    return hole("identity")
```

`--goals` は `n: Nat` と期待型 `Eq[Nat, n, n]` を表示します。`--json` はdiagnosticsとgoalsをJSONで返します。Rustでは `analyze_module` / `analyze_module_with_resolver` を使います。goalのIDはその解析結果内の識別子です。

型が推論できない位置では `ann(hole("name"), Nat)` のように期待型を与えてください。利用者のholeは暗黙引数推論用のmetaとは区別され、未使用になった場合も未完成として扱います。holeを含むmoduleから `CheckedModule` は返りません。

## Opaqueな検査済み定義

```python
from __future__ import annotations
from deppy import theorem, Nat, Eq, refl

@theorem
def identity_proof(n: Nat) -> Eq[Nat, n, n]:
    return refl(n)
```

`@theorem` は `@dependent(opaque=True)` の別名です。本体は通常どおりkernelで検査しますが、正規化と変換判定では展開しません。後続の証明は公開された型を使ってこの定理を適用できます。`@theorem(decreases="n")` のように `decreases`・`motive_level` と併用できます。`deppy` と `deppy.core` からimportできます。`theorem` に透明化オプションはありません。計算する透明な定義には従来どおり `@dependent` を使います。既存の `@dependent(opaque=True/False)` も引き続き利用できます。

opaque定義は公理ではありません。本体が公理を使う場合、その依存はimport後も追跡します。明示的なunfold機能はありません。runtime extractionは変換判定とは別で、保持した検査済み本体を利用します。

## 小さなtactic層

`deppy.tactics` のtacticは式として組み合わせます。生成するのは既存のCore証明項で、通常の証明と同じkernel検査を通ります。Pythonの実行やsolverを信頼する仕組みではありません。

| 式 | 動作 |
| --- | --- |
| `intro(lambda x: proof)` | goalの関数型に従って仮定を導入。複数引数も可 |
| `exact(proof)` | 証明を現在のgoalの型で検査 |
| `apply(lemma, arg, ...)` | 補題に引数を適用。暗黙引数は既存の推論で補完 |
| `rewrite(eq, proof)` | goal中の等式の左辺を右辺に書換え、残ったgoalを `proof` で証明 |
| `rewrite_in(eq, proof)` | 既存の証明の型を左辺から右辺へ書換え |
| `cases(value, {Constructor: branch, ...})` | コンストラクタごとの場合分け。フィールドは `lambda` で束縛 |
| `induction(level, value, motive, *branches)` | Natまたは一般帰納型の帰納法。再帰フィールドには帰納法の仮定も渡る |

`apply` の明示引数は指定します。未完成の引数には `hole("名前")` を置けます。`cases` の分岐は全コンストラクタを重複なく列挙し、結果のuniverseは0です。高いuniverseや明示的なmotiveが必要な場合は `induction` / `induct` を使います。

```python
from deppy.tactics import rewrite, induction

@theorem
def add_zero_again(n: Nat) -> Eq[Nat, add(n, 0), n]:
    return induction(0, n, lambda k: Eq[Nat, add(k, 0), k],
        refl(0), lambda k, ih: rewrite(ih, refl(S(k))))
```

書換えは解決済みの型を正規化し、変換可能な出現をまとめて置換します。逆向きには `rewrite(sym(eq), proof)` を使います。該当する出現がなければgoalは変わりません。まだ推論できないメタ変数がある場合や、依存する出現の置換で型が成立しなくなる場合は検査に失敗します。その場合は型注釈や明示的なmotiveを持つ `transport` / `J` を使ってください。

Fibonacciの不変条件保存は、二つの等式でgoalを書換えて漸化式を適用します。

```python
rewrite(inv.snd.fst, rewrite(inv.snd.snd, fib_step(index)))
```

終了時の添字の証明も、motiveを手書きせずに表せます。

```python
index_is_n = rewrite_in(counter_zero(remaining, test), inv.fst)
return rewrite(sym(index_is_n), inv.snd.fst)
```

`@verified(proofs={...})` の各証明callbackにも同じtacticを使えます。`@verified(auto=False, proofs={})` では、自動証明を止めて未指定の `loop.init`・`loop.preserve`・`loop.decrease`・`loop.exit` を確認できます。これらはそれぞれ名前・ソース位置・局所文脈・期待型を持つ独立goalになります。`analyze_module` やCLIのgoal表示で確認し、必要なキーだけ順に埋められます。tactic内の `hole` も同じgoal形式を使います。未完成の証明は検査済み宣言として登録されません。
