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
cargo fmt --all -- --check
cargo clippy --workspace --all-targets --offline -- -D warnings
```

進捗と未実装項目は[PROGRESS.md](PROGRESS.md)で管理しています。

## 現在の実装

`crates/deppy-core`は、完全に明示化したコア項を直接検査するライブラリです。

- 非累積的な具体的universe階層（`Type₀ : Type₁`）とΠ型。
- 型注釈付きλ、適用、型注釈付きlet、de Bruijn indexによる束縛。
- Nat、Z、S、universe levelとmotiveを明示した依存eliminator。
- 環境を保持するclosureによるNbE、β・ζ・Nat eliminatorのι簡約、関数のη変換。
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

`add Z m ≡ m`と`add (S k) m ≡ S (add k m)`は定義的等式です。変数nについて`add n Z ≡ n`とは判定しません。この等式の証明には、今後実装するEqと帰納法が必要です。Pythonの整数や`+`、`match`の読み取りはまだ実装していません。

## 次の実装段階

1. elaboratorの対応範囲を拡張（let・グローバル定義・保留制約・意味値による評価）。
2. Eq、refl、Jを追加し、congとNatの帰納法による証明を検査。
3. Vec、Fin、限定した依存パターンと構造的再帰。
4. Σ、projection、非再帰のdependent record。
5. CPython 3.12〜3.14のparse/compile検証、AST schema、静的名前解決を接続。
6. 使用検査、消去、境界の検証・再構築、Pythonコード生成と差分実行テスト。

第17節の5例を検査・実行できることがMVPの到達条件です。未実装の構文や穴を公理・`Any`として受理する機能は設けません。
