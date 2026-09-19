# DepPy 言語設計案

DepPy は、**Python の構文を使って記述する、純粋な依存型言語と通常の Python の混在環境**として設計する。依存型の意味論は Rust 製の検査器が定義し、CPython の型注釈機構には型検査を委ねない。以下では目標仕様を定義したうえで、第19節に初期実装の範囲を限定する。

## 1. Language Goals

DepPy が再利用するのは、Python の字句・構文、ソースファイル、関数呼び出しの表記、および実行基盤である。依存型を扱う領域では、注釈の名前解決、型パラメータ、型内の式、パターンマッチに DepPy 独自の静的意味論を与える。通常の Python 全体を依存型コアへ翻訳することは目標にしない。

本仕様の互換対象は CPython 3.12〜3.14 とする。`def identity[A: Type](...)` の型パラメータ構文は Python 3.12 で導入された構文を使う。将来の Python バージョンへの対応は、構文と注釈の評価方式を確認したうえで追加する。([Python Enhancement Proposals (PEPs)][1])

互換性は、次の四段階を区別する。

| 段階      | 保証すること                                 |
| ------- | -------------------------------------- |
| 構文互換    | 対象 CPython がソースを構文解析・コンパイルできる          |
| 通常実行互換  | `deppy` ランタイムを入れれば、対応するプログラムをそのまま実行できる |
| 静的保証    | 検査済みの依存型領域が、明示した境界条件のもとで型を保つ           |
| 消去後実行互換 | 型・証明を消去したコードを通常の CPython で実行できる        |

「構文解析できる」と「注釈を Python の式として評価できる」は別の条件である。例えば、関数の注釈に現れる `n` を、その関数の呼び出し時の引数値へ結び付ける機能は、Python の注釈機構にはない。DepPy は注釈をソース AST から読み、独自の束縛規則で解釈する。([Python documentation][2])

通常実行向けのソースでは、次の記述を標準とする。

```python
from __future__ import annotations
from deppy import dependent, Type, Nat, Vec
```

Python 3.14 では注釈が通常は遅延評価されるが、それだけでは依存する引数名の問題を解決できない。対象バージョンでは `from __future__ import annotations` による文字列化が利用できるため、本仕様ではこれを要求する。`typing.get_type_hints()` などによる DepPy 注釈の Python 式としての評価は、互換性の保証対象から外す。([Python documentation][3])

## 2. Design Principles

設計上の優先順位は、型の健全性、Python として有効な構文、対応範囲での実行意味の保存、予測可能な消去、段階的な導入の順とする。構文を維持したまま健全に扱えない機能は、依存型領域では拒否する。静的意味と実行時意味が食い違うコードを、利便性のために黙って受理しない。

| 原則                     | 採用する規則                          |
| ---------------------- | ------------------------------- |
| Valid Python syntax    | 独自の字句や構文を追加しない                  |
| Small trusted core     | 完全に明示化されたコア項を、小さな kernel が再検査する |
| Explicit boundary      | 純粋・全域な領域と、通常の Python を区別する      |
| Predictable erasure    | 消去する変数について、実行時の使用を検査する          |
| Gradual adoption       | 関数単位で DepPy を導入できる              |
| Reproducible checking  | 型検査中にユーザーモジュールや注釈を実行しない         |
| Conservative inference | 推論できなかった箇所を `Any` や公理で埋めない      |

依存型領域の指定には、原則として `@dependent` を使う。通常の `def` や `class` は、指定がなければ Python 側の宣言として扱う。プロジェクト設定によるモジュール単位の指定も可能とするが、初見のソースで意味が分かる関数単位の指定を推奨する。

## 3. Surface Language

以下の `deppy` API は、本設計で定義する API であり、既存パッケージの説明ではない。注釈に使う `Type`、`Pi`、`Sigma`、`Eq` などは、実行時には注釈用の記述子として提供する。静的検査器は、それらの Python メソッドを呼び出さず、解決済みの宣言 ID に対応する構文として処理する。

### Universe と polymorphism

```python
from __future__ import annotations
from deppy import dependent, Type, Level

@dependent
def identity[A: Type](x: A) -> A:
    return x

@dependent
def universe_identity[u: Level, A: Type[u]](x: A) -> A:
    return x
```

`Type` は `Type[0]` の省略形とする。最初の `identity` は、小さい型について多相だが、universe level については多相ではない。後者の `u` は universe parameter であり、値レベルの `Nat` とは区別する。

### Π、Σ、命題

```python
from deppy import Pi, Sigma, Empty

type PreserveLength[T: Type] = Pi[
    Nat,
    lambda n: Pi[
        Vec[T, n],
        lambda xs: Vec[T, n],
    ],
]

type SomeVector[T: Type] = Sigma[
    Nat,
    lambda n: Vec[T, n],
]

type Not[P: Type] = Pi[P, lambda p: Empty]
type And[P: Type, Q: Type] = Sigma[P, lambda p: Q]
```

`Pi[A, lambda x: B]` を依存関数型とする。`Sigma[A, lambda x: B]` を依存対型とする。命題には専用の `Prop` universe を設けず、型を命題、その項を証明として使う。

### Equality と proof

```python
from deppy import Eq, Proof, refl

@dependent
def reflexive(n: Nat) -> Eq[Nat, n, n]:
    return refl(n)

@dependent
def erased_reflexive(n: Nat) -> Proof[Eq[Nat, n, n]]:
    return refl(n)
```

`Eq[Nat, n, n]` は通常の型であり、`refl(n)` はその項である。`Proof[P]` は、対応する証明を消去対象として扱うための注釈であり、新しい論理的命題を作らない。消去条件を満たさない使い方はエラーにする。

### Implicit arguments と indexed datatype

```python
from deppy import S, VCons

@dependent
def head[T: Type, n: Nat](xs: Vec[T, S(n)]) -> T:
    match xs:
        case VCons(k, x, rest):
            return x
```

角括弧内のパラメータは、DepPy では原則として推論される消去対象の引数とする。したがって、`n: Nat` は型ではなく自然数の暗黙引数を宣言する。CPython は同じ構文から `TypeVar` を作るため、この `n` を実行時の自然数として関数本体から読むことは禁止する。([Python Enhancement Proposals (PEPs)][1])

明示的な特殊化には、通常の関数呼び出し構文を使う。

```python
specialize(identity, A=Nat)(Z())
specialize(head, T=Nat, n=Z())(VCons(Z(), Z(), VNil()))
```

`specialize` は静的には暗黙引数を指定する構文として扱う。通常実行では、指定された静的引数を呼び出し対象へ渡さず、元の callable を返す補助関数になる。通常の Python 関数に subscription を追加する必要がある `identity[Nat](...)` は、標準表記には採用しない。

### Dependent record

```python
from deppy import record

@record
class SomeVec[T: Type]:
    n: Nat
    value: Vec[T, self.n]
```

`@record` のフィールド注釈内では、`self` を検査器が導入する特別な束縛として扱う。`self.n` は先行するフィールドへの依存を表し、任意の属性アクセスには解釈しない。レコードの詳細と Σ 型との関係は第10節で定義する。

## 4. Static Semantics

依存関数の引数列は、**左から右へ伸びる telescope**として解釈する。各引数の型を検査してから、その引数を後続の型と戻り値型の環境に追加する。これにより、値レベルの引数を後続の注釈で参照できる。

```python
def f[T: Type](
    n: Nat,
    x: Vec[T, n],
) -> Vec[T, n + 1]:
    ...
```

この宣言の型は、次のように elaboration する。

```text
Π⁰ (T : Type₀).
Πω (n : Nat).
Πω (x : Vec T n).
Vec T (add n (S Z))
```

ここで `0` は実行時に消去する束縛、`ω` は実行時に利用できる束縛を表す。`x` の型では `T` と `n` が参照でき、戻り値型ではすべての引数が参照できる。提示された `def f(n: Nat, x: Vec[T, n]) ...` のように `T` が宣言されていない場合は、外側に適切な束縛がなければエラーにする。

名前解決には次の制限を設ける。

| 場所                   | 参照できる名前                            |
| -------------------- | ---------------------------------- |
| Generic parameter の型 | 外側の静的環境と、先行する generic parameter    |
| 通常引数の注釈              | 外側の静的環境、generic parameter、先行する通常引数 |
| 戻り値の注釈               | すべての引数                             |
| 関数本体                 | 静的環境と通常のローカル変数。ただし消去対象には使用制限がある    |
| レコードのフィールド型          | 型パラメータと、`self` を通した先行フィールド         |
| パターンの分岐内             | 分岐で導入された変数と、その分岐で成立する添字の関係         |

同じ関数内で後から宣言される引数を、先行する引数の型から参照することは禁止する。引数や添字として使われるローカル変数への再代入も、初期仕様では禁止する。Python のデフォルト引数は引数の束縛前に評価されるため、依存するデフォルト値には転用せず、依存型領域では単純な定数に限定する。([Python Enhancement Proposals (PEPs)][1])

注釈中の式は、実行時の値が分からなければ symbolic term のまま保持する。例えば `n + m` は、その場で長さを計算する要求ではなく、環境中の `n` と `m` を参照する `add n m` である。依存型の添字がコンパイル時に具体的な整数へ確定する必要はない。

数値リテラルには、実行互換性のための制限を設ける。注釈の添字などで `Nat` が要求される `0` や `1` は、それぞれ `Z` と `S Z` に展開する。一方、実行される位置の Python 整数を黙って Peano 自然数へ変換せず、`Nat` の値には `Z()`、`S(n)`、または明示的な変換関数を使う。

## 5. Core Calculus

コアは、predicative な intensional Martin-Löf 型理論を基礎とする。Π、Σ、identity type、universe hierarchy、および検査済みの帰納型を持たせる。Python の属性探索、例外、継承、`Any`、一般再帰はコアの構成要素にしない。

概略の Rust 表現を次に示す。`Tm` は共有された不変の項への参照であり、束縛変数には de Bruijn index を使う。名前とソース位置は別の対応表に保持する。

```rust
type Tm = Arc<Term>;

enum Relevance {
    Erased,
    Runtime,
}

enum Term {
    Var(u32),
    Universe(Level),
    Global(DefId, Vec<Level>),

    Pi {
        relevance: Relevance,
        domain: Tm,
        codomain: Tm,
    },
    Lam {
        relevance: Relevance,
        domain: Tm,
        body: Tm,
    },
    App { function: Tm, argument: Tm },
    Let { ty: Tm, value: Tm, body: Tm },

    Sigma { domain: Tm, codomain: Tm },
    Pair { sigma: Tm, first: Tm, second: Tm },
    Fst(Tm),
    Snd(Tm),

    Eq { ty: Tm, left: Tm, right: Tm },
    Refl { ty: Tm, value: Tm },
    J(JTerm),

    Constructor(ConstructorApp),
    Elim(EliminatorApp),
}
```

帰納型そのものの宣言は、項の中ではなく `GlobalEnv` に置く。宣言にはパラメータ列、添字列、所属 universe、各コンストラクタの型、および許される eliminator を保存する。`Elim` は、明示された motive と分岐を持つ帰納型の消去であり、任意の Python `match` をそのまま格納するものではない。

```rust
struct GlobalEnv {
    definitions: Map<DefId, Definition>,
    inductives: Map<InductiveId, InductiveDecl>,
}

struct Definition {
    universe_params: Vec<LevelParam>,
    ty: Tm,
    body: Tm,
    transparency: Transparency,
    runtime_role: RuntimeRole,
}
```

最終的な `Term` には `Meta`、`Hole`、未解決のオーバーロードを入れない。elaborator は別の `ElabTerm` を使い、すべての穴を解決してからコア項へ変換する。kernel は、その結果を最初から型検査し直す。

Python の構文とコアの関係は、次のように限定する。

| Surface / HIR の要素   | コアでの扱い                 |
| ------------------- | ---------------------- |
| 関数名、キーワード引数、暗黙引数の指定 | elaborator が解決する       |
| ローカル変数への一度だけの代入     | `Let`                  |
| `lambda`            | `Lam`                  |
| `Vec[T, n]`         | 型族への `App`             |
| `n + m`             | 検査済みの `add` への適用       |
| `match`             | 明示的な motive を持つ `Elim` |
| レコードの属性             | 検査済み projection        |
| 構造的再帰               | 帰納型の recursor          |
| 一般再帰、`raise`、動的属性探索 | コアでは受理しない              |

## 6. Universe System

`Type : Type` は採用しない。universe は `Type₀, Type₁, Type₂, ...` という階層を持ち、各 `Typeᵤ` は `Typeᵤ₊₁` に属する。通常の Python の `type` は、この階層とは無関係な Python オブジェクトとして扱う。

```text
Typeᵤ : Typeᵤ₊₁

A : Typeᵤ
x : A ⊢ B(x) : Typeᵥ
────────────────────────────
Π (x : A). B(x) : Type_max(u,v)

A : Typeᵤ
x : A ⊢ B(x) : Typeᵥ
────────────────────────────
Σ (x : A). B(x) : Type_max(u,v)
```

本案では universe の cumulativity を採用しない。`A : Type[0]` から自動的に `A : Type[1]` と扱う規則を設けず、必要な場合には明示的な lifting を使う。この選択は Lean の非累積的 universe と共通するが、後述する `Prop` や proof irrelevance の扱いは異なる。([Lean Language][4])

表面構文の意味は次のように固定する。

| 表記         | 意味                           |
| ---------- | ---------------------------- |
| `Type`     | `Type[0]`                    |
| `A: Type`  | `A` は `Type₀` の項             |
| `Type[0]`  | 最小の universe                 |
| `Type[1]`  | `Type[0]` を含む次の universe     |
| `u: Level` | 項とは別の universe parameter     |
| `Type[u]`  | level parameter を持つ universe |

例えば `identity[A: Type]` の型全体は `Type₁` に属する。これは `A` の型である `Type₀` 自身が `Type₁` に属するためである。型引数の universe と、関数型全体の universe を同一視してはならない。

Level のコア表現は次で足りる。

```rust
enum Level {
    Zero,
    Succ(Box<Level>),
    Max(Vec<Level>),
    Param(LevelParam),
}
```

elaboration 中にだけ `LevelMeta` を追加する。多相な `Vec` や `refl` の参照では、省略された level に metavariable を生成し、引数や期待型から解決する。裸の `Type` を出現ごとに異なる universe metavariable として扱うことはしない。

初期の level solver は、`max` の正規化、具体的 level の比較、単一 metavariable への代入、occurs check に限定する。`?u = Succ(?u)` のような循環は拒否し、宣言済みの level parameter は代入対象にしない。より複雑な制約が解けなかった場合は注釈を要求し、勝手な level の選択によって公開型を確定しない。

## 7. Elaboration

型付けは bidirectional にする。変数や注釈済み関数の適用では型を合成し、`lambda`、依存対、コンストラクタ、`refl` などでは期待型を利用する。完全な型推論を仕様上の約束にせず、推論の境界を診断可能にする。

```rust
struct Local {
    id: LocalId,
    name: Symbol,
    ty: ValueRef,
    value: ValueRef,
    relevance: Relevance,
    span: Span,
}

struct Context {
    locals: Vec<Local>,
    phase: Phase,
}

struct MetaEntry {
    telescope: Telescope,
    expected_type: Tm,
    solution: Option<Tm>,
    origin: Span,
}

struct MetaContext {
    entries: Map<MetaId, MetaEntry>,
    postponed: Vec<Constraint>,
}
```

API は、合成、検査、単一化を分離する。`expected` には評価済みの型を渡し、型の先頭が Π か Σ かを調べるための不要な正規形生成を避ける。kernel に渡す直前には、metavariable の置換と、未解決制約の検査を行う。

```rust
fn synth(
    ctx: &Context,
    expr: &SurfaceExpr,
    state: &mut ElabState,
) -> Result<(ElabTerm, ValueRef)>;

fn check(
    ctx: &Context,
    expr: &SurfaceExpr,
    expected: ValueRef,
    state: &mut ElabState,
) -> Result<ElabTerm>;

fn unify(
    ctx: &Context,
    left: ValueRef,
    right: ValueRef,
    state: &mut ElabState,
) -> Result<()>;
```

### 例：`identity(Z())`

次の呼び出しを elaboration する。ここで `identity` の宣言は既に検査済みとする。`A` は消去対象だが、型検査中には通常のコア引数として存在する。

```python
identity(Z())
```

| 段階         | 結果                                                       |
| ---------- | -------------------------------------------------------- |
| Python AST | `Call(Name("identity"), [Call(Name("Z"), [])])`          |
| 名前解決       | `identity` と `Z` をそれぞれ固定された `DefId` / constructor ID に解決 |
| 関数型の取得     | `Π⁰ A : Type₀. Πω x : A. A`                              |
| 暗黙引数の挿入    | `identity ?A (Z)`                                        |
| 明示引数の合成    | `Z : Nat`                                                |
| 制約の生成      | `?A ≡ Nat`                                               |
| 解決後のコア項    | `App(App(identity, Nat), Z)`                             |
| 結果型        | `Nat`                                                    |
| 消去後        | `identity(Z())`                                          |

Metavariable は、作成時点の telescope を明示的に持たせる。解を代入するときは occurs check と scope check を行い、後から導入された変数が外へ漏れないようにする。高階単一化は pattern fragment を中心とする不完全な方式を採用し、任意の高階問題を探索し続けない。

暗黙の coercion は限定する。型の定義的等しさによる変換、静的な自然数リテラルの展開、および明示的に定義された少数の構文的変換だけを行う。`list` から `Vec`、`int` から `Nat`、Python の subclass から別のコア型への変換は自動で挿入しない。

## 8. Definitional Equality and Normalization

定義的等しさは、検査済みのコア項に対して定義する。Python の `==`、`__eq__`、`__add__` を呼び出して判定することはない。ユーザーが実行時に変更できるメソッドの振る舞いを、型変換の根拠にしてはならない。

| 規則                                      | 採用                     |
| --------------------------------------- | ---------------------- |
| α-equivalence                           | de Bruijn 表現で扱う        |
| β-reduction                             | 採用する                   |
| ζ-reduction：`let` の展開                   | 採用する                   |
| δ-reduction：定義の展開                       | transparent な検査済み定義に限る |
| ι-reduction：constructor に対する eliminator | 採用する                   |
| Π の η-rule                              | 型指向の変換判定として採用する        |
| Σ・レコードの一般的な η-rule                      | 初期仕様では採用しない            |
| 等式の証明から定義的等しさを導く equality reflection    | 採用しない                  |
| 加算の交換則・結合則による書き換え                       | 定義的等しさには含めない           |

加算は第1引数について定義する。

```text
add Z     m ≡ m
add (S n) m ≡ S (add n m)
```

この選択では `0 + n` は `n` に簡約できる。変数 `n` に対する `n + 0` は、そのままでは簡約できない。したがって、入力例の `zero_right(n)` における `return refl(n)` は受理せず、帰納法による証明を要求する。

### NbE

Normalization by Evaluation は、コア項を意味領域へ評価し、必要なときに構文へ戻す方式で実装する。意味領域の closure は、環境と検査済みコア項を保持し、任意の Python callable を保持しない。closure、穴、暗黙引数、単一化を段階的に実装する参考としては、作者による `elaboration-zoo` の実装が利用できるが、帰納型やモジュールの設計は別途必要になる。([GitHub][5])

```rust
type ValueRef = Arc<Value>;

struct Closure {
    env: Arc<[ValueRef]>,
    body: Tm,
}

enum Value {
    Universe(Level),
    Pi(Relevance, ValueRef, Closure),
    Lam(Closure),
    Sigma(ValueRef, Closure),
    Pair(ValueRef, ValueRef),
    Eq(ValueRef, ValueRef, ValueRef),
    Refl(ValueRef),
    Constructor(ConstructorValue),
    Neutral(Neutral),
}
```

評価と再構成の流れは次になる。

```text
Term
  ↓ eval(term, environment)
semantic Value
  ↓ quote(context_depth, expected_type, value)
Normal Form
```

自由変数や opaque な定義に依存して計算が進まない値は、neutral value として保持する。Π 型での比較では新しい neutral 変数を与えて結果を比較することで、η を扱う。elaborator 用の意味領域では未解決 meta の neutral head も必要だが、kernel が受け取る項には残さない。

正規化は、型の先頭構造の確認、引数の型の照合、添字の比較、`refl` の検査、依存パターンの分岐型の計算などで使う。毎回完全な正規形を構築せず、通常は弱頭正規化と意味値同士の比較で進める。計算量の上限に達した場合は「検査を完了できなかった」と報告し、等しいと仮定して検査を通してはならない。

## 9. Equality

`Eq` は propositional equality を表す型とする。定義的等しさは検査器の判断であり、`Eq` の証明をユーザーが渡す必要がない。逆に `p: Eq[A, x, y]` が存在しても、それだけで型変換器が `x` と `y` を同一視する規則は設けない。

基本表記には `Eq[A, x, y]` を採用する。`Eq[x, y]` も carrier を推論できる場合に限って省略形として認める。診断と公開 API では、どの型の上の等式なのかが明確な3引数表記を推奨する。

```text
A : Typeᵤ
x : A
y : A
─────────────────────
Eq A x y : Typeᵤ

refl : Π⁰ A : Typeᵤ. Π x : A. Eq A x x
```

`refl(x)` を `Eq[A, a, b]` に対して検査するときは、`x` と `a`、および `x` と `b` が定義的に等しいことを要求する。Python の比較式 `a == b` が真になることは、この検査を代替しない。`assert a == b` も証明項には変換しない。

一般的な equality eliminator として `J` をコアに持たせる。`transport`、substitution、congruence は、その上で定義するライブラリ関数とする。これにより、「どの等式操作が信頼されているのか」を `J` とその計算規則まで絞れる。

```text
J :
  Π A : Typeᵤ.
  Π x : A.
  Π C : (Π y : A. Eq A x y → Typeᵥ).
  C x (refl x) →
  Π y : A.
  Π p : Eq A x y.
  C y p

J A x C d x (refl x) ≡ d
```

主要な補助関数は次の型を持つ。

```text
transport :
  Π P : (A → Typeᵥ).
  Eq A x y →
  P x →
  P y

cong :
  Π f : (A → B).
  Eq A x y →
  Eq B (f x) (f y)
```

**Proof irrelevance は採用しない。** 同じ型 `P` の任意の項 `p` と `q` を、定義的に等しいとは扱わない。Lean は `Prop` に definitional proof irrelevance を持つが、DepPy は専用の `Prop` を導入せず、証明の消去を別の使用検査で扱う。([Lean Language][6])

UIP、K、function extensionality、univalence も初期仕様の公理にはしない。特に、等式のパターンマッチを安易な添字単一化として実装すると、意図せず K 相当の規則を受理する危険がある。初期仕様では `Eq` に対する直接の Python `match` を認めず、`J` とその派生関数に限定する。([Agda][7])

## 10. Dependent Pair and Records

Σ 型の標準表記は、要求にある `Sigma[Nat, lambda n: Vec[T, n]]` をそのまま採用する。構築には `Pair(n, xs)`、射影には `.fst` と `.snd` を使う。`Pair` の第2成分の型族は一般には値だけから推論できないため、期待型を利用して検査する。

```text
p : Σ (n : Nat). Vec T n

p.fst : Nat
p.snd : Vec T p.fst
```

レコードは、Σ 型の単なる透明な別名にはしない。**名目的な単一コンストラクタの帰納型**へ変換し、コアに新しい `Record` primitive は追加しない。これにより、Python のクラスとしての区別とコアの型の区別を一致させる。

```text
SomeVec : Typeᵤ → Typeᵤ

MkSomeVec :
  Π⁰ T : Typeᵤ.
  Π n : Nat.
  Vec T n →
  SomeVec T

SomeVec.n :
  Π⁰ T : Typeᵤ.
  SomeVec T → Nat

SomeVec.value :
  Π⁰ T : Typeᵤ.
  Π r : SomeVec T.
  Vec T (SomeVec.n r)
```

透明な Σ の sugar にすると、同じ構造を持つ別々の Python クラスまで定義的に同じ型になる可能性がある。その状態で異なるフィールド名や runtime class を使うと、通常実行との対応が崩れる。本案では `SomeVec[T]` と対応する Σ 型を同型として扱い、変換関数を明示する。

| 設計                    | 利点                        | 不利益                     |
| --------------------- | ------------------------- | ----------------------- |
| Σ の透明な sugar          | コアへの追加が少ない                | Python の名目的なクラスと整合させにくい |
| 独立した Record primitive | レコード用の規則を直接表現できる          | kernel が増える             |
| 単一コンストラクタの帰納型         | 名目的な型と既存の eliminator を使える | Σ との変換が必要になる            |

`@record` は、フィールドの宣言順を依存順として使う。後続フィールドへの依存、循環依存、プロパティ、可変フィールド、ユーザー定義の `__setattr__`、継承は初期仕様で禁止する。通常実行用の decorator はフィールド名からコンストラクタを作るが、依存関係の正しさは Rust 側で検査する。

## 11. Inductive Types

`Nat`、`Vec`、`Fin` は標準 prelude の帰納型とする。初期実装では組み込み宣言として登録するが、型理論上は同じ帰納型の宣言形式で表現する。これにより、後からユーザー定義の帰納型を追加しても、組み込み型だけが別の論理を使う状態を避けられる。

この設計では、通常実行の明瞭さを優先して、`Vec` と `Fin` のコンストラクタにサイズの witness を明示的に持たせる。

```text
Nat : Type₀
Z   : Nat
S   : Nat → Nat

Vec   : Typeᵤ → Nat → Typeᵤ
VNil  : Π⁰ T : Typeᵤ. Vec T Z
VCons : Π⁰ T : Typeᵤ.
        Π n : Nat.
        T → Vec T n → Vec T (S n)

Fin : Nat → Type₀
FZ  : Π n : Nat. Fin (S n)
FS  : Π n : Nat. Fin n → Fin (S n)
```

例えば `FZ(Z())` は `Fin[1]` のゼロであり、`FS(S(Z()), FZ(Z()))` は `Fin[2]` の1である。`FZ` の引数は値そのものの番号ではなく、上限の predecessor である。これは唯一の可能な表現ではないが、添字と実行時パターン変数の対応が明示される利点がある。

目標仕様におけるユーザー定義の indexed datatype は、次のように記述できる。

```python
@inductive(indices=("n",))
class Vec[T: Type, n: Nat]:
    @constructor
    def nil() -> Vec[T, 0]:
        ...

    @constructor
    def cons(
        k: Nat,
        head: T,
        tail: Vec[T, k],
    ) -> Vec[T, S(k)]:
        ...
```

この `...` は constructor 宣言にだけ認める特別な宣言本体である。通常実行では `@inductive` が、それらを実際のコンストラクタへ置き換える。一般の `@dependent` 関数で `...` を書いて証明や値を省略することは許可しない。

帰納型の受理には、型の整形式性、strict positivity、パラメータの扱い、添字とフィールドの universe 条件、および eliminator の整形式性を検査する。初期のユーザー定義機能では、非正位置の再帰や複雑な nested datatype を拒否する。Positivity checking の無効化は、通常の宣言オプションとして提供しない。([Agda][8])

### Dependent elimination

`get` では、`xs: Vec[T, n]` を分解したときに、後続の `i: Fin[n]` の型も変化する。elaborator は `i` を motive の引数として一般化し、次の形の motive を作る。単に分岐内で `n` の名前を置換する処理では、この依存を正しく表現できない。

```text
M(k, xs) = Fin k → T
```

`VNil` の分岐では `i: Fin[0]` になる。`VCons` の分岐では `n = S(k)` に対応する分岐型を使い、再帰呼び出しには `Fin[k]` の値を渡す。実際に生成した eliminator 項を kernel が検査することで、分岐の絞り込みが正当であることを確認する。

## 12. Python Compatibility Boundary

DepPy の領域は次の四種類とする。領域の分類は、関数の型と一緒にインターフェースへ保存する。通常の Python 関数に依存型らしい注釈を書いただけで、純粋なコア関数へ昇格させてはならない。

| 領域          | 意味                              |
| ----------- | ------------------------------- |
| `Dependent` | 純粋・全域で、コアへ elaboration される      |
| `Checked`   | Python の効果を許すが、対応する範囲で型と境界を検査する |
| `Dynamic`   | 通常の Python。依存型の保証は境界で得る         |
| `Unsafe`    | 検査できない表現や外部実装への信頼を明示する          |

`Checked` 関数の戻り値注釈は、原則として正常終了した場合の結果についての条件を表す。そこから関数の停止性や、型内での利用可能性を導いてはならない。`Checked` の関数をコアの Π 型の値として渡したり、型レベル計算で呼び出したりすることは禁止する。

Python の値を依存型領域へ渡す場合は、対応する有限なデータ形式について検証と再構築を行う。例えば Python の列からは、実際に得られた不変な内容に対応する `SomeVec[T]` を作る。外部で主張された長さを、そのまま添字として信用しない。

```text
Python sequence
  ↓ 内容を取得し、必要な要素検証を行う
canonical immutable Vec
  ↓ その値から長さを計算する
Σ (n : Nat). Vec T n
```

任意の依存型を runtime check できるとは仮定しない。特に、任意の Π 型に対する関数の全域性、任意の等式、任意の命題の証明は一般的な境界検査の対象にしない。そのような値は、既に検査済みのコアから得るか、`Unsafe` として扱う。

可変な Python オブジェクトを運ぶ用途には、目標仕様で opaque handle を用意できる。コア内では、その handle の参照先の状態を観測する eliminator を提供せず、単なる不透明な値として保持する。その場合でも、handle を格納する `Vec` の長さについては保証できるが、参照先の可変属性についての依存条件は保証しない。

通常の class、inheritance、protocol、subtyping は Python 側に残す。依存型コアでは、型変換と明示的な関数による変換を使う。Protocol の一致を純粋性や全域性の証明として扱わず、`isinstance` による判定を帰納型のコンストラクタ判定へ一般化しない。

## 13. Mutation and Effects

依存型領域は pure fragment とする。mutation、I/O、一般の例外、async、generator、context manager は、通常の Python 側で使う。初期仕様に包括的な effect system や monad 変換を導入する必要はない。

| 機能                     | `Dependent` での扱い |
| ---------------------- | ---------------- |
| ローカル変数への一度の束縛          | `Let` として許可する    |
| 変数の再代入                 | 初期仕様では禁止する       |
| 可変コンテナの変更              | 禁止する             |
| 属性の更新                  | 禁止する             |
| I/O                    | 禁止する             |
| `raise`、`try`          | 禁止する             |
| `async`、`await`        | 禁止する             |
| `yield`、generator      | 禁止する             |
| ユーザー定義 context manager | 禁止する             |
| 検査済みの構造的再帰             | 許可する             |

不変性は、外側のオブジェクトに更新メソッドがないだけでは足りない。例えば、長さを添字にした可変リストを別名から変更できるなら、元の型は維持できない。本案では canonical な不変構造へ変換し、型が依存する状態を別名から変更できないようにする。

`Vec` の長さだけが保証対象なら、不変の spine と opaque な要素を組み合わせることは可能である。要素の内容も型に現れる場合には、その内容まで純粋な値として固定する必要がある。検証後も共有される可変状態に対して、過去の検証結果を保持し続ける設計は採用しない。

### Totality と例外

停止性は `@dependent` の受理条件に含める。初期実装では、指定された引数の構造的に小さい部分への再帰を検査し、それを recursor へ変換する。Agda にも構造的再帰を検査する方式があるが、DepPy では検査を無効化して全域と宣言する逃げ道を安全な領域に設けない。([Agda][9])

```python
@dependent(decreases="xs")
def append(...):
    ...
```

`decreases="xs"` はユーザーによる証明の代用品ではなく、検査対象を指定するヒントである。検査器はすべての再帰呼び出しを確認し、一般再帰を表す `fix` をコアへ残さない。相互再帰や複雑な well-founded recursion は、初期実装から除外する。

部分関数を「型検査時には展開しない関数」としてコアへ登録するだけでは不十分である。例えば、発散する関数に任意の命題を返す型を与えれば、論理的な全域性の前提を失う。本案では、部分関数をコア項の生成源から除外する。

論理的な停止性と、実機で例外が絶対に起こらないことも区別する。CPython の有限なスタックやメモリ、外部からの中断による失敗は、数学的な停止性の保証に含めない。生成コードの trampoline 化やループ化は可能だが、それでも資源不足まで排除する仕様にはしない。

## 14. Runtime Model

型検査中は、型引数、添字、証明を含めた完全な項を保持する。消去は kernel による型検査と使用検査の後に行う。NbE の途中で証明を捨てる設計にはしない。

| 種類                     | 実行時の扱い                     |
| ---------------------- | -------------------------- |
| Compile-time only term | universe、型式、型族の静的定義などは消去する |
| Erased proof           | 使用検査に合格した証明を消去する           |
| Runtime-relevant index | 本体の計算や公開 API に必要な添字は保持する   |
| Ordinary Python value  | Python 側の通常の値として保持する       |

`Proof[P]` は、初期仕様では引数、戻り値、対応するフィールドの注釈位置に限定する。任意の場所で普通の型コンストラクタとして使えるものにはしない。例えば `Vec[Proof[P], n]` のような表記は、要素の保存方式が別途定義されるまで拒否する。

証明の消去に、論理的な proof irrelevance は必要ない。本案では、消去対象が実行時の分岐、値の構築、I/O などに影響しないことを検査する。これは、Idris 2 が消去対象の変数を数量 `0` で区別する設計と関連するが、DepPy の初期仕様には数量 `1` の線形性は導入しない。([Idris 2 Documentation][10])

例えば次の関数は拒否する。

```python
@dependent
def bad_length[T: Type, n: Nat](xs: Vec[T, n]) -> Nat:
    return n
```

この `n` は消去対象であり、CPython 上でも自然数の実引数として渡されない。実行時に長さが必要なら、通常引数として `n: Nat` を宣言するか、`xs` から構造的に計算する。暗黙引数であることと、実行時に自動で復元されることを同一視しない。

`Vec[T, n]` の注釈内だけに現れる `n` は、実行時の型オブジェクトとして保持しない。一方、第11節の `VCons(k, x, tail)` が持つ `k` は通常のフィールドであり、パターンマッチで使うなら残る。後からこのフィールドを除去する最適化を入れる場合は、呼び出し側、パターン、境界検査をまとめて変換する必要がある。

`transport` の消去も無条件には行わない。初期仕様では、対象の型族が同じ runtime representation を使うことが確認できる場合に限って identity operation へ落とす。一般の `J` を使った計算や、証明から実行時のデータを取り出す計算は、証明を保持するか、消去対象としての宣言を拒否する。

消去は、Python 側の副作用を消してよいという意味ではない。`Checked` 側からの呼び出しでは、実行時引数の評価順序と回数を保持する。消去される引数位置に副作用のある式を置くことは禁止し、通常の引数の評価は必要に応じて一時変数へ展開する。

## 15. Compilation Pipeline

処理系は、Python の構文と DepPy の意味論を分離して実装する。最初の実装では Rust 製 Python parser を選定する必要はなく、対象 CPython の `ast` と compiler を frontend の構文判定に使う。Python AST の生成だけでは検出されない構文上の制約もあるため、実行せずに `compile` できることまで確認する。([Python documentation][11])

```text
.py source
    ↓
対象 CPython による parse / compile 検証
    ↓
Python AST + source spans
    ↓
Rust: DepPy frontend / 名前解決 / 領域分類
    ↓
Rust: HIR / telescope / pattern information
    ↓
Rust: elaboration / metavariables / unification
    ↓
完全に明示化された Dependent Core
    ↓
Rust: kernel type checking / NbE
    ↓
Rust: 使用検査 / erasure
    ↓
Python 用 runtime IR
    ↓
Python AST + 境界 adapter
    ↓
CPython compile / execution
```

| フェーズ             | 責務                                         |
| ---------------- | ------------------------------------------ |
| CPython frontend | 対象文法での受理、AST、ソース位置の取得                      |
| Rust frontend    | import 名の解決、marker の識別、領域分類                |
| HIR              | Python の記法から、束縛と依存関係を明示した表現への変換            |
| Elaboration      | 期待型、暗黙引数、meta、パターンの motive を解決             |
| Kernel           | コア項、帰納型宣言、等式変換を再検査                         |
| Erasure checker  | 消去対象の実行時使用を検査                              |
| Runtime lowering | コンストラクタ、recursor、projection を Python 実装へ変換 |
| Code generation  | 評価順序を保つ AST と境界検査を生成                       |
| CPython          | 生成された通常の Python コードを実行                     |

Python と Rust の境界には、バージョン付きの AST schema を置く。初期実装は CPython の小さな subprocess から AST をシリアライズして Rust に渡す構成で十分である。Rust 側に渡した後は、型検査のために Python のコードやオブジェクトを呼び戻さない。

### Module と import

型検査時には import 文の対象を静的に解決する。ユーザーモジュールを import して `__annotations__` を調べる方式は採用しない。注釈の取得 API 自体にも任意コードを実行する可能性があるため、ソース AST を入力の基準にする。([Python documentation][3])

検査済みインターフェースには、コア型、必要な定義本体、帰納型宣言、universe parameter、消去情報、依存モジュールのハッシュを保存する。型内で展開する定義については、シグネチャだけを保存しても定義的等しさを再現できない。循環した値定義は拒否し、相互依存を認める宣言群も明示的に検査する。

Python の動的な `sys.path` 変更、条件付き import、import hook は、依存型領域の名前解決には使わない。外部モジュールが静的に検査できなければ、`Dynamic` または専用 adapter を通じて参照する。生成コードでは、依存型領域の参照先を可能な範囲で固定し、通常のグローバル変数の再束縛によって意味が変わることを防ぐ。

論理的な trusted computing base と、実行まで含めた trusted computing base は異なる。前者は kernel、定義的等しさ、帰納型の検査であり、elaborator の推論結果は再検査する。後者には source-to-core の意味対応、消去、コード生成、runtime primitive、CPython も含まれるため、小さな kernel だけで実行系全体の正しさまで保証したとは言わない。

## 16. Diagnostics

診断は、元の Python の名前と source span を基準に表示する。de Bruijn index や内部の meta ID は、通常のエラー表示には出さない。型の比較で何が要求され、どの式から異なる型が得られたのかを説明する。

```text
error[DP2104]: 戻り値の長さが注釈と一致しません

  sample.py:8:12
      return xs
             ^^

  xs の型:
      Vec[int, n]

  戻り値に要求される型:
      Vec[int, n + 1]

  引数 n は、sample.py:4:5 で宣言されています。
  この分岐では、xs の長さが n + 1 になることを確認できません。
```

このエラーを `unification failed` だけで終わらせない。添字の展開が原因なら、どの定義まで展開したかを追加表示できるようにする。例えば `n + 0` では、加算が第1引数について再帰し、`n` が未確定なので簡約が停止していることを説明する。

ほかにも、未宣言の添字名、先行フィールド以外への参照、消去対象の実行時使用、停止性の未確認、未知の外部関数の型内呼び出しを別々のエラーにする。未解決の暗黙引数には、候補の型と制約を発生させた位置を示す。計算資源の上限に達したエラーと、型が一致しないエラーも区別する。

## 17. Worked Examples

以下は、それぞれ独立した `.py` ファイルとして記述できる完全な例である。ここで使うコンストラクタと補助関数は、本仕様の `deppy` prelude が提供する。5例について CPython 3.13.5 で構文解析・コンパイルと簡易ランタイム上の動作を確認したが、DepPy の静的検査器そのものを実装・検証した結果ではない。

### 17.1 Identity

```python
from __future__ import annotations
from deppy import dependent, Type, Nat, Z


@dependent
def identity[A: Type](x: A) -> A:
    return x


assert identity(Z()) == Z()
```

Surface type は `identity[A: Type](x: A) -> A` である。Core type は次の形になり、`A` は消去される。末尾の `assert` は通常の Python による動作確認であり、論理的証明としては扱わない。

```text
identity :
  Π⁰ A : Type₀.
  Πω x : A.
  A
```

### 17.2 Vec append

```python
from __future__ import annotations
from deppy import dependent, Type, Nat, Z, S, Vec, VNil, VCons


@dependent(decreases="xs")
def append[T: Type](
    n: Nat,
    m: Nat,
    xs: Vec[T, n],
    ys: Vec[T, m],
) -> Vec[T, n + m]:
    match xs:
        case VNil():
            return ys

        case VCons(k, x, rest):
            return VCons(
                k + m,
                x,
                append(k, m, rest, ys),
            )


z = Z()
one = S(z)

xs = VCons(z, one, VNil())
ys = VCons(z, z, VNil())

assert append(one, one, xs, ys) == VCons(one, one, ys)
```

Surface type は、二つの長さと二つの `Vec` を受け取り、長さがその和になる型である。Core type は次になり、再帰は `xs` の tail に対して行われる。`n` と `m` は通常引数なので、公開された Python の呼び出し規約には残る。

```text
append :
  Π⁰ T : Type₀.
  Π n : Nat.
  Π m : Nat.
  Vec T n →
  Vec T m →
  Vec T (add n m)
```

`VNil` の分岐では `n = Z` に対応する分岐型になり、`add Z m` が `m` に簡約する。`VCons` の分岐では、再帰結果が `Vec T (add k m)` であり、構築結果は `Vec T (S (add k m))` になる。これは期待される `Vec T (add (S k) m)` と定義的に等しい。

### 17.3 Fin による安全な indexing

```python
from __future__ import annotations
from deppy import (
    dependent, Type, Nat, Z, S,
    Vec, VNil, VCons,
    Fin, FZ, FS, fin0_elim,
)


@dependent(decreases="xs")
def get[T: Type](
    n: Nat,
    xs: Vec[T, n],
    i: Fin[n],
) -> T:
    match xs:
        case VNil():
            return fin0_elim(i)

        case VCons(k, x, rest):
            match i:
                case FZ(_):
                    return x

                case FS(_, j):
                    return get(k, rest, j)


z = Z()
one = S(z)
two = S(one)

xs = VCons(one, z, VCons(z, one, VNil()))
i = FS(one, FZ(z))

assert get(two, xs, i) == one
```

Surface type は `get[T](n, xs: Vec[T, n], i: Fin[n]) -> T` である。Core type は次になり、`i` はベクタの長さと同じ添字を持つ。`Fin` の runtime representation を整数に最適化する場合でも、この対応を境界で検証する必要がある。

```text
get :
  Π⁰ T : Type₀.
  Π n : Nat.
  Vec T n →
  Fin n →
  T
```

空のベクタの分岐では `i: Fin[0]` となる。`fin0_elim` は、その型にコンストラクタが存在しないことに基づく検査済みの eliminator である。`raise` を書けば任意の戻り値型を満たせる、という扱いにはしない。

### 17.4 Equality proof

```python
from __future__ import annotations
from deppy import dependent, Nat, Z, S, Eq, refl, cong


@dependent(decreases="n")
def zero_right(n: Nat) -> Eq[Nat, n + 0, n]:
    match n:
        case Z():
            return refl(Z())

        case S(k):
            return cong(S, zero_right(k))


zero_right(S(S(Z())))
```

Surface type は `zero_right(n: Nat) -> Eq[Nat, n + 0, n]` である。Core type は次になり、関数本体は `Nat` の依存 recursor に変換する。戻り値を `Proof[Eq[Nat, n + 0, n]]` と宣言すれば、使用条件を満たす呼び出しについて証明計算を消去できる。

```text
zero_right :
  Π n : Nat.
  Eq Nat (add n Z) n
```

帰納法の仮定は `Eq Nat (add k Z) k` になる。`cong S` によって `Eq Nat (S (add k Z)) (S k)` が得られる。これは `add (S k) Z` の定義を展開した期待型に一致する。

### 17.5 Σ と dependent record

```python
from __future__ import annotations
from deppy import (
    dependent, record, Type,
    Nat, Z, S, Vec, VNil, VCons,
    Sigma, Pair,
)


@record
class SomeVec[T: Type]:
    n: Nat
    value: Vec[T, self.n]


@dependent
def pack[T: Type](
    n: Nat,
    xs: Vec[T, n],
) -> Sigma[Nat, lambda k: Vec[T, k]]:
    return Pair(n, xs)


@dependent
def as_record[T: Type](
    p: Sigma[Nat, lambda k: Vec[T, k]],
) -> SomeVec[T]:
    return SomeVec(p.fst, p.snd)


@dependent
def as_pair[T: Type](
    r: SomeVec[T],
) -> Sigma[Nat, lambda k: Vec[T, k]]:
    return Pair(r.n, r.value)


z = Z()
one = S(z)
xs = VCons(z, one, VNil())

r = as_record(pack(one, xs))

assert r.n == one
assert as_pair(r).snd == xs
```

Surface type では、`pack` が Σ 型を返し、残りの二つがレコードとの変換を行う。Core type は次のように異なる型を明示的に結ぶ。`SomeVec T` と Σ 型を定義的に等しいとは扱わない。

```text
pack :
  Π⁰ T : Type₀.
  Π n : Nat.
  Vec T n →
  Σ k : Nat. Vec T k

as_record :
  Π⁰ T : Type₀.
  (Σ k : Nat. Vec T k) →
  SomeVec T

as_pair :
  Π⁰ T : Type₀.
  SomeVec T →
  Σ k : Nat. Vec T k
```

`p.snd` の型は `Vec T p.fst` なので、`SomeVec(p.fst, p.snd)` を構築できる。逆向きでも、`r.value` の型が `Vec T r.n` であることを使う。レコードの `n` を後から書き換えられる仕様では、この性質を維持できない。

## 18. Unsoundness Risks

Python と同じプロセスで実行する以上、任意の敵対的な Python コードや native code に対する防御と、型システムの保証は区別する。`frozen=True` の dataclass も、不変性を模倣する機能であり、絶対的な保護境界ではない。DepPy は無制限な reflection や native memory access がある環境で、依存型の不変条件を防御し切れるとは主張しない。([Python documentation][12])

| リスク                                 | 扱い               | 規則                                             |
| ----------------------------------- | ---------------- | ---------------------------------------------- |
| 添字に依存する可変オブジェクト                     | 禁止               | core の添字から可変状態を参照しない                           |
| Aliasing による変更                      | 制限・runtime check | canonical な不変構造を再構築し、必要な状態を固定する                |
| 可変要素を含む不変コンテナ                       | 制限               | 長さの保証と、要素内容の保証を分ける                             |
| `Any` から依存型への代入                     | runtime check    | 対応するデータ型だけ検証して取り込む                             |
| `typing.cast`                       | 制限               | 依存型の証拠として使わない                                  |
| 任意の `Eq` や証明の外部入力                   | 禁止・Unsafe        | 一般の runtime validation は提供しない                  |
| `eval`、`exec`                       | 禁止               | 依存型領域から使えない                                    |
| `globals()`、`locals()`、動的 `getattr` | 禁止               | コアの名前解決や値の観測に使えない                              |
| Monkey patch                        | 禁止・Unsafe        | 検査済みの定義や constructor の変更は保証外                   |
| `__code__`、`__class__` などの変更        | 禁止・Unsafe        | runtime representation の改変として扱う                |
| Native extension、FFI、`ctypes`       | Unsafe           | 専用 adapter の契約と実装を信頼する場合だけ接続する                 |
| 注釈中の任意の Python 呼び出し                 | 禁止               | 検査済みの純粋なコア関数だけ許可する                             |
| Python `==` と論理的等式の混同               | 禁止               | `Eq` の導入規則を使う                                  |
| 偽の constructor、subclass             | runtime check    | 登録された representation を確認し、必要なら再構築する            |
| 循環した外部データ                           | runtime check    | 有限帰納値として取り込む際に検出・拒否する                          |
| import 先やインターフェースの不一致               | 制限               | 内容ハッシュと依存関係を照合する                               |
| 部分関数による証明生成                         | 禁止               | `Dependent` に全域性を要求する                          |
| 消去による副作用の欠落                         | 禁止               | 消去位置に効果のある式を置けない                               |
| Bool と整数などの runtime subtype         | runtime check    | `Nat` への変換では、単純な `isinstance(x, int)` だけに依存しない |

`Unsafe` は、任意の仮定を安全な定理として公開するための機能にはしない。外部実装の契約に依存した結果には、その依存をインターフェースへ記録し、通常の安全な定理の export から区別する。安全なビルドでは、そのような仮定を持つ宣言の利用を拒否できるようにする。

型検査時に使う opaque な定義も、無検査の公理とは区別する。opaque は定義的等しさのために本体を展開しないという意味であり、本体の型検査と全域性の確認は必要である。任意の Python 関数を opaque として登録するだけでは、安全な境界にならない。

## 19. Minimal Viable DepPy

MVP は、第17節の例を検査できる範囲に絞る。単に `Type, Nat, Pi, Lam, App, Eq, Refl, Vec, Fin, NbE` を並べるだけでは、帰納法による等式証明と Σ 型の例を十分に扱えない。そこで、Σ、`J`、限定した依存消去、および非再帰の dependent record まで含める。

| 項目               | MVP に含める仕様                                                |
| ---------------- | --------------------------------------------------------- |
| Python frontend  | CPython 3.12〜3.14 の AST と compile 検証                      |
| Opt-in           | `@dependent`、`@record`                                    |
| Universe         | 非累積的な具体的 level の階層。裸の `Type` は `Type[0]`                  |
| 関数               | Π、λ、適用、`let`、明示的な引数型と戻り値型                                 |
| 暗黙引数             | 角括弧内の型引数・自然数引数。消去対象に限定する                                  |
| データ              | 固定 prelude の `Nat`、`Vec`、`Fin`                            |
| Σ                | `Sigma`、`Pair`、2種類の projection                            |
| レコード             | 非再帰・不変・継承なし・単一コンストラクタ                                     |
| Equality         | `Eq`、`refl`、`J`、`cong`、限定した `transport`                   |
| Pattern matching | 組み込み型への constructor pattern と限定した入れ子                      |
| 再帰               | 一つの指定引数に対する構造的再帰                                          |
| 推論               | Bidirectional checking、scope を持つ meta、pattern unification |
| 正規化              | Closure ベースの NbE と型指向の変換判定                                |
| 消去               | 型引数、静的添字、使用条件を満たす証明                                       |
| Python 境界        | 少数の有限データ型に対する検証・再構築                                       |
| モジュール            | 静的 import 解決と検査済みインターフェース                                 |

MVP では、ユーザーが宣言する universe polymorphism と任意の帰納型を入れない。一般の高階単一化、任意の dependent pattern matching、相互再帰、well-founded recursion、型クラス、SMT、effect system、linearity も除外する。Python 側についても、mypy 相当の完全な解析器を同時に実装せず、依存型領域と境界の検査に集中する。

実装順序は、まず非依存の λ 計算ではなく、最初から Π と universe を持つ小さなコアを作るところから始める。次に meta と bidirectional elaboration、固定された `Nat` の eliminator、`Eq` と `J`、`Vec` と `Fin`、Σ とレコードの順で追加する。最後に消去と Python code generation を接続し、ソース実行と生成コード実行の差分テストを行う。

検査器には、受理テストだけでなく拒否テストを同じ程度に用意する。少なくとも `Type : Type`、発散する証明、添字の再代入、meta の scope escape、`Fin[0]` の偽造、不正な消去、暗黙の K の導入をテストする。kernel 単体への不正なコア入力も検査し、frontend が正しい入力しか作らないことに依存させない。

## 20. Future Extensions

MVP 後の拡張は、既存の保証を維持できる単位で追加する。特に推論能力の向上と、コアの論理を強くする変更は分けて扱う。前者は同じコア項を作る別の elaborator として検査できるが、後者は kernel の仕様とメタ理論の再確認を必要とする。

| 拡張                              | 推奨する導入方法                                      |
| ------------------------------- | --------------------------------------------- |
| Universe polymorphism           | `u: Level` と `Type[u]` を追加し、公開定義の level を明示する |
| User-defined inductive families | Positivity と eliminator 生成を段階的に一般化する          |
| 高度な dependent pattern matching  | 必ず明示的な eliminator 項へ変換し、kernel で再検査する         |
| Well-founded recursion          | 停止性の証明をコア項として要求する                             |
| Type classes / traits           | Elaborator が明示的な辞書引数へ変換する                     |
| Refinement types                | 検査済み述語と証明を持つ型へ展開する                            |
| SMT integration                 | solver の回答だけを信用せず、再検査可能な証明を要求する               |
| Effect system                   | `Checked` の効果を追跡し、純粋性をより細かく表現する               |
| Linearity / ownership           | 可変状態を扱う別の保証として導入する                            |
| Theorem proving tactics         | コア項を生成する非 trusted な補助機構にする                    |
| LSP                             | Source span、期待型、局所環境、未解決制約を公開する               |
| mypy / pyright interoperability | 消去後の近似型を stub として出力する                         |

Python 向け stub では、例えば `Vec[T, n]` を添字を持たない不変ベクタの型へ近似する。これは Python 側の補完や通常の型検査には使えるが、依存型の証明を外部の型検査器へ移すものではない。逆に、mypy や pyright が受理したコードを、そのまま DepPy の純粋なコアへ受け入れることもしない。

### 1. 推奨する DepPy の言語仕様

DepPy は、Python の有効な構文上に、純粋・全域な依存型領域を明示的に設ける言語とする。コアには非累積的な universe hierarchy、Π、Σ、intensional equality、検査済みの帰納型と eliminator を採用し、proof irrelevance、equality reflection、一般再帰は採用しない。通常の Python とは検証・再構築を伴う境界で接続し、実行時に使う値と消去対象を使用検査で区別する。

### 2. MVP の仕様

MVP は、固定された `Nat`、`Vec`、`Fin`、Π、Σ、`Eq`、`J`、限定した dependent matching、構造的再帰、および非再帰の dependent record に絞る。Rust 側で elaboration、NbE、kernel、消去を実装し、構文の受理と最終実行には対象 CPython を使う。第17節の5例を受理し、型と実行の意味が食い違う近接例を確実に拒否できることを、最初の到達条件にする。

### 3. まだ決める必要がある設計事項

残る設計事項は、主に実行表現の最適化、外部接続の範囲、およびモジュール間の配布形式である。これらは基礎の型規則を曖昧なまま残す理由にはせず、MVP では保守的な表現と限定した adapter を使う。次の項目を、追加実装前に確定させる必要がある。

| 未決定事項                      | 確定すべき内容                                                     |
| -------------------------- | ----------------------------------------------------------- |
| 高速な runtime representation | Peano 表現やサイズ witness を、どの条件で整数・tuple・compact vector に置き換えるか |
| 境界 adapter の範囲             | どの Python 型を再構築できるか、opaque handle や callback をどこまで許すか       |
| インターフェースと ABI              | 消去後の呼び出し規約、キャッシュ形式、バージョン間の互換性                               |
| 高度な消去                      | 一般の `J`、型に依存する layout、証明を含むデータ構造をどう扱うか                      |
| 保証の形式化                     | Source-to-core、erasure、code generation の意味保存をどの範囲まで機械検証するか  |

この設計で譲らない境界は、**Python として書ける任意の式を、依存型の計算として受け入れないこと**である。注釈の中でも、純粋性、型付け、停止性、束縛、実行表現との対応を満たす式だけを認める。その制限によって、Python の既存構文と実行基盤を維持しながら、依存型部分について検査可能な言語仕様を与えられる。

[1]: https://peps.python.org/pep-0695/ "https://peps.python.org/pep-0695/"
[2]: https://docs.python.org/3.14/reference/executionmodel.html "https://docs.python.org/3.14/reference/executionmodel.html"
[3]: https://docs.python.org/3.14/library/annotationlib.html "https://docs.python.org/3.14/library/annotationlib.html"
[4]: https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/ "https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/"
[5]: https://github.com/AndrasKovacs/elaboration-zoo "https://github.com/AndrasKovacs/elaboration-zoo"
[6]: https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/ "https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/"
[7]: https://agda.readthedocs.io/en/latest/language/without-k.html "https://agda.readthedocs.io/en/latest/language/without-k.html"
[8]: https://agda.readthedocs.io/en/latest/language/positivity-checking.html "https://agda.readthedocs.io/en/latest/language/positivity-checking.html"
[9]: https://agda.readthedocs.io/en/latest/language/termination-checking.html "https://agda.readthedocs.io/en/latest/language/termination-checking.html"
[10]: https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html "https://idris2.readthedocs.io/en/latest/tutorial/multiplicities.html"
[11]: https://docs.python.org/3.14/library/ast.html "https://docs.python.org/3.14/library/ast.html"
[12]: https://docs.python.org/3.14/library/dataclasses.html "https://docs.python.org/3.14/library/dataclasses.html"

# GOAL

ゴールには、**「reverse した Vec を mirror した Fin で参照すると、元と同じ要素が得られる」**を推します。単なる `append` の結合律より一段難しく、`Vec` と `Fin` という2つの indexed datatype、算術補題、dependent pattern matching、`Eq`、`transport`、再帰を全部使えるからです。

```python
@dependent
def reverse_get[T: Type](
    n: Nat,
    xs: Vec[T, n],
    i: Fin[n],
) -> Eq[
    T,
    get(n, reverse(n, xs), mirror(n, i)),
    get(n, xs, i),
]:
    ...
```

数学的には、

```text
∀ T n (xs : Vec T n) (i : Fin n),
  get (reverse xs) (mirror i)
  = get xs i
```

です。`mirror` は `0 ↦ n-1`, `1 ↦ n-2`, … を行う `Fin[n] -> Fin[n]` です。

これを最終定理にすると、途中でかなり良い補題群が必要になります。

```python
# 自然数
zero_right:
    Eq[Nat, n + 0, n]

succ_right:
    Eq[Nat, n + S(m), S(n + m)]

add_assoc:
    Eq[Nat, (a + b) + c, a + (b + c)]

add_comm:
    Eq[Nat, a + b, b + a]
```

次に Vec の代数です。

```python
append_nil_right:
    Eq[
        Vec[T, n],
        append(n, 0, xs, VNil()),
        xs,
    ]
```

ただし実際には `append(n, 0, xs, VNil())` の型が

```text
Vec T (n + 0)
```

なので、

```text
Vec T n
```

との間に `zero_right(n)` を使った `transport` が必要になる可能性があります。これが DepPy の検査器にとって良い試験になります。

さらに、

```python
append_assoc:
    append(append(xs, ys), zs)
    =
    transport(..., append(xs, append(ys, zs)))
```

も必要になります。

そして reverse の中心補題として、

```python
reverse_append:
    reverse(append(xs, ys))
    =
    append(reverse(ys), reverse(xs))
```

を証明します。

ここはかなり非自明です。左辺の長さは、

```text
n + m
```

ですが、右辺は、

```text
m + n
```

になるので、

```python
add_comm(n, m)
```

による `transport` が入ります。

概念的には、

```python
@dependent
def reverse_append[T: Type](
    n: Nat,
    m: Nat,
    xs: Vec[T, n],
    ys: Vec[T, m],
) -> Eq[
    Vec[T, n + m],
    reverse(n + m, append(n, m, xs, ys)),
    transport(
        lambda k: Vec[T, k],
        sym(add_comm(n, m)),
        append(
            m,
            n,
            reverse(m, ys),
            reverse(n, xs),
        ),
    ),
]:
    ...
```

くらいになります。

ここまで行くと、DepPy の

```text
definitional equality
propositional equality
transport
indexed datatype
dependent elimination
normalization
```

の違いが全部表に出ます。

さらに `Fin` 側には、

```python
weaken:
    Fin[n] -> Fin[S(n)]

last:
    (n: Nat) -> Fin[S(n)]

inject_left:
    Fin[n] -> Fin[n + m]

inject_right:
    Fin[m] -> Fin[n + m]
```

などが必要になります。

`mirror` も単純な整数計算ではなく、帰納的に作れます。

```python
@dependent
def mirror(
    n: Nat,
    i: Fin[n],
) -> Fin[n]:
    ...
```

例えば `Fin[S(n)]` のゼロは最後へ移し、

```text
FZ(n)
    ↦ last(n)
```

後続要素については、再帰した結果を適切に埋め込みます。

そして lookup と append の対応も証明します。

```python
get_append_left:
    get(
        n + m,
        append(n, m, xs, ys),
        inject_left(i),
    )
    =
    get(n, xs, i)
```

```python
get_append_right:
    get(
        n + m,
        append(n, m, xs, ys),
        inject_right(j),
    )
    =
    get(m, ys, j)
```

最終的にはだいたい、

```text
Nat arithmetic
      ↓
append algebra
      ↓
Fin embeddings
      ↓
reverse_append
      ↓
mirror properties
      ↓
reverse_get
```

という証明グラフになります。

さらにもう一つ上の定理として、

```python
@dependent
def reverse_involution[T: Type](
    n: Nat,
    xs: Vec[T, n],
) -> Eq[
    Vec[T, n],
    reverse(n, reverse(n, xs)),
    xs,
]:
    ...
```

も置けます。

ただ、**最終デモとしては `reverse_involution` より `reverse_get` の方が面白い**です。`reverse_involution` は主に `Vec` と append の代数ですが、`reverse_get` は `Vec[T,n]` と `Fin[n]` という二つの依存型が同じ index を介して連動します。DepPy が「Python に型注釈を増やしただけ」ではなく、本当に dependent type checker になっていることが見えやすいです。

最終的には、たとえば以下の1ファイルが通ることを DepPy の大きなマイルストーンにできます。

```python
from deppy import *


@dependent
def reverse_get[T: Type](
    n: Nat,
    xs: Vec[T, n],
    i: Fin[n],
) -> Eq[
    T,
    get(n, reverse(n, xs), mirror(n, i)),
    get(n, xs, i),
]:
    match xs:
        case VNil():
            return fin0_elim(i)

        case VCons(k, x, rest):
            ...
```

しかも、この `...` を埋めるために10個前後の補題が必要になる程度に設計できます。DepPy の最初の「大定理」としては、かなり良い難易度です。
