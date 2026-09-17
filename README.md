# DepPy

Pythonの構文で記述する依存型言語の実装です。[Chatlog.md](Chatlog.md)を設計仕様とし、第19節の実装順序に沿って進めています。

現在はRust製kernelと、名前付きASTを入力とする初期elaboratorを実装しています。Pythonソースの検査・実行や、第17節の例全体にはまだ対応していません。

## 実行

RustのCargoを使用します。外部crateへの依存はありません。

```sh
cargo test --workspace --offline
cargo run -p deppy-core --example identity --offline
cargo run -p deppy-elab --example implicit_identity --offline
cargo run -p deppy-elab --example nat_add --offline
cargo run -p deppy-elab --example zero_right --offline
cargo run -p deppy-elab --example vectors --offline
cargo run -p deppy-elab --example sigma --offline
cargo fmt --all -- --check
cargo clippy --workspace --all-targets --offline -- -D warnings
```

進捗と未実装項目は[PROGRESS.md](PROGRESS.md)で管理しています。

## 現在の実装

`crates/deppy-core`は、完全に明示化したコア項を直接検査するライブラリです。

- 非累積的な具体的universe階層（`Type₀ : Type₁`）とΠ型。
- 型注釈付きλ、適用、型注釈付きlet、de Bruijn indexによる束縛。
- Nat、Z、S、universe levelとmotiveを明示した依存eliminator。
- Eq、refl、一般の等式消去J（証明にも依存するmotive）。
- Σ、型注釈付きPair、依存するfst・snd射影。
- Vec・Fin、サイズのwitnessを持つコンストラクタ、依存eliminator、fin0_elim。
- 環境を保持するclosureによるNbE、β・ζ・Nat・Vec・Fin eliminatorとJのι簡約、関数のη変換。
- `Kernel::infer`、`check`、`normalize`、型を指定する`equivalent`。
- 不正なコア入力の拒否と、処理ステップの予算超過時のエラー。

公開APIは閉じた項を受け取ります。正規化・等価性判定も入力を型検査してから評価するため、未検査の自己適用を評価器へ直接渡せません。型の一致はuniverseの持ち上げを行いません。正規化はβ・ζ・ι正規形を返し、ηは等価性判定で扱います。

`Relevance::Erased`は現時点では束縛と型に保持する情報です。実行時使用の検査と消去は未実装であり、kernelの受理だけでは消去やPython実行の安全性を保証しません。エラーはコア項を表示し、Pythonの名前・ソース位置に対応する診断はfrontendとともに追加します。

処理予算は計算回数を制限しますが、再帰的なRust実装に対するスタック・メモリの完全な保護ではありません。universe levelは`u32`で表現し、後続levelを表現できない場合は拒否します。

## Elaboration

`crates/deppy-elab`は、名前付きの`Expr`から完全に明示化したコア項を生成します。`Elaborator::infer`は型を合成し、`check`は期待型から型注釈のないλを検査します。`Expr::app`は先行する暗黙引数を挿入し、`Expr::implicit`で明示指定もできます。

metaは作成時のtelescopeと期待型を保持します。通常引数や期待される戻り値型から制約を解き、occurs checkとscope checkを行います。未解決のmetaは、簡約で使われなくなるものも含めて拒否します。各metaの解と、簡約前の最終コアをkernelで再検査してから`Elaborated { term, ty }`を返します。

この段階の単一化は、metaのtelescopeを相異なるローカル変数で置き換えるpatternに限定しています。解けない制約を保留・探索する機能、metaの引数のpruning、一般の高階単一化はありません。型注釈が不足する場合や、関数型・universeが判定できない場合はエラーになります。引数の型だけから推論した候補のuniverseが不正な場合も、kernelの再検査で拒否します。

入力はRustで組み立てるASTであり、Pythonのparserではありません。let、グローバル定義、キーワード引数、source spanはまだ扱いません。elaborator内の評価は捕獲を避ける置換と弱頭簡約で実装しており、kernelのclosureベースNbEとは別です。意味値を使ったelaborationへの移行は残っています。

## Natと加算

コアの`Term::Nat`、`Zero`、`Succ`はそれぞれNat、Z、Sを表します。`Term::NatElim`は次の型を検査します。`level`は具体的なuniverse levelで、すべての引数を明示します。

```text
P    : Nat → Type[level]
zero : P Z
step : Π (k : Nat). P k → P (S k)
n    : Nat
──────────────────────────────────
NatElim(level, P, zero, step, n) : P n
```

Zではzeroへ、S(k)では`step k (NatElim ... k)`へ簡約します。変数などのneutralな対象ではeliminatorを保持します。どちらの分岐もkernelで検査し、Natにη規則や一般再帰を追加しません。

名前付きASTでも`Expr::Nat`、`Zero`、`succ()`、`nat_elim(...)`を使用できます。`prelude::nat_add()`は第1引数について再帰する加算のASTを返します。専用の加算primitiveや公理は使わず、通常のelaborationとkernel検査を通します。

`add Z m ≡ m`と`add (S k) m ≡ S (add k m)`は定義的等式です。変数nについて`add n Z ≡ n`とは判定しません。この等式は、EqとNatの帰納法で証明します。Pythonの整数や`+`、`match`の読み取りはまだ実装していません。

## 等式と帰納法による証明

`Expr::eq(A, x, y)`で等式型、`x.refl()`で反射律を表します。`refl`のcarrierは引数から推論し、期待型がEqの場合はそのcarrierで引数を検査して両辺との定義的等しさを確認します。コアの`Term::Refl`はcarrierも明示します。

`Expr::j(level, A, x, C, d, y, p)`とコアの`Term::J`は次を検査します。

```text
A : Type[u]    x, y : A    p : Eq A x y
C : (z : A) → Eq A x z → Type[level]
d : C x (refl x)
────────────────────────────────────────
J(level, A, x, C, d, y, p) : C y p
```

証明が`refl`ならdへ簡約し、neutralな証明ではJを保持します。motiveやbaseも簡約前に検査します。等式の証明から定義的等しさを導く規則、proof irrelevance、UIP・Kなどの公理は追加していません。

`prelude::cong(u, v)`と`prelude::transport(u, v)`はJから定義したASTを返します。universeは呼び出し時に具体的なlevelを指定します。transportは型検査と論理的な計算規則に対応し、runtime representationの検査・消去は未実装です。

`prelude::zero_right()`は`(n : Nat) → Eq Nat (add n Z) n`をNat eliminatorで証明します。Zの分岐は`refl Z`、Sの分岐は`cong S ih`です。実行例は一般形をkernelで検査し、`zero_right(2)`が`refl(2)`に正規化されることも確認します。Pythonの再帰関数やmatchからの変換はまだ扱いません。

## Vec・Finと安全な要素取得

`Vec A n : Type[u]`（`A : Type[u]`）、`Fin n : Type[0]`を固定の帰納型として扱います。名前付きASTには`Expr::vec`、`vnil`、`vcons`、`fin`、`fz`、`fs`があります。コンストラクタは次の明示的な引数を持ちます。

```text
VNil(A)              : Vec A Z
VCons(A, k, h, tail)  : Vec A (S k)    h : A, tail : Vec A k
FZ(k)                : Fin (S k)
FS(k, j)             : Fin (S k)      j : Fin k
```

`VCons`の長さはtailの長さ、`FZ`・`FS`のboundは結果の上限の前段です。kernelはこれらのwitnessとフィールドの型を照合します。`Fin Z`を構築するコンストラクタはありません。`Expr::fin0_elim(A, i)`は`i : Fin Z`からAの項を得る消去で、通常のFZやFSを渡すと拒否します。変数などのneutralなiは、そのまま消去項に保持します。

依存eliminatorには、結果のuniverse level、motive、両分岐、添字、分解対象を明示します。Vecではcarrierも指定します。

```text
VecElim(level, A, P, nil, cons, n, xs) : P n xs
  P    : (k : Nat) → Vec A k → Type[level]
  nil  : P Z (VNil A)
  cons : (k : Nat) → (h : A) → (t : Vec A k) →
         P k t → P (S k) (VCons A k h t)

FinElim(level, P, zero, step, n, i) : P n i
  P    : (k : Nat) → Fin k → Type[level]
  zero : (k : Nat) → P (S k) (FZ k)
  step : (k : Nat) → (j : Fin k) → P k j → P (S k) (FS k j)
```

再帰はtailまたはFSの前段だけに進み、neutralな対象では消去項を保持します。elaboratorはmotiveと分岐の期待型から、λの型注釈を補えます。通常の暗黙引数推論では、Vecからcarrier・長さ、Finから上限を推論できます。直接のコンストラクタASTではcarrierを明示します。

`prelude::vec_append(level)`と`prelude::vec_get(level)`は、追加の公理や専用primitiveを使わずeliminatorから定義したASTです。

```text
append : {A : Type[level]} → (n m : Nat) → Vec A n → Vec A m → Vec A (add n m)
get    : {A : Type[level]} → (n : Nat) → Vec A n → Fin n → A
```

getのVec motiveは`P k xs = Fin k → A`です。空の分岐にはfin0_elimを使い、VConsの分岐ではFinElimから導いたcase splitで先頭と再帰呼び出しを選びます。型レベルのNat eliminatorで分岐関数の型を作るため、添字の強制変換は不要です。実行例は`[1] ++ [0] = [1, 0]`と、その2番目の値が0であることをkernelの正規化で確認します。

これらは固定された型と明示的なeliminatorの実装です。ユーザー定義帰納型の宣言検査・positivity checking、Pythonのconstructor patternや再帰関数の変換、実行時のベクタ表現・境界検証は未実装です。

## 依存対

`Expr::sigma("n", Expr::Nat, Expr::vec(Expr::Nat, Expr::name("n")))`で、長さとベクタの依存対型を表せます。`Expr::pair(n, xs)`は期待されるΣ型を使って検査します。単独のPairから型族を推論することはせず、`Elaborator::check`または`.ann(...)`で型を与えます。

```text
Σ (x : A). B x : Type[max(u,v)]   (A : Type[u], B x : Type[v])
p.fst : A
p.snd : B p.fst
(Pair a b).fst ≡ a
(Pair a b).snd ≡ b
```

コアの`Pair { ty, fst, snd }`はΣ型の注釈を保持し、射影で捨てられる成分もkernelで検査します。Σの一般的なη規則は採用しません。`sigma`実行例は一般の`pack`を検査し、`Pair(1, [1])`の両射影と第2成分の型を正規化で確認します。Python構文と名目的なrecordへの接続は未実装です。

## 次の実装段階

1. 非再帰のdependent record、限定した依存パターンと構造的再帰。
2. elaboratorの対応範囲を拡張（let・グローバル定義・保留制約・意味値による評価）。
3. CPython 3.12〜3.14のparse/compile検証、AST schema、静的名前解決を接続。
4. 使用検査、消去、境界の検証・再構築、Pythonコード生成と差分実行テスト。

第17節の5例を検査・実行できることがMVPの到達条件です。未実装の構文や穴を公理・`Any`として受理する機能は設けません。
