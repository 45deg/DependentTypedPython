# DepPy

DepPyは、Python構文で全域関数と証明を書く `@dependent` と、命令的な部分言語を検証する `@verified` を備えた依存型言語です。生成した証明はRust製kernelで検査します。

Rust製kernel、名前付きASTのelaborator、Ruffを使ったPython frontendと、分離した任意のruntime backendを実装しています。identity・append・get・zero_right・SomeVecの例について、型検査から生成コードの実行まで通ります。対応範囲と残る制約は[実装リファレンス](docs/reference.md#実行mvp)に記載しています。

Pythonでの証明項・公理・ライブラリ利用は [証明言語のガイド](docs/proofs.md) を参照してください。[reverse_explicit.py](crates/deppy-python/examples/reverse_explicit.py) はRustに補題を追加せず、Pythonのeliminatorとライブラリだけで証明する例です。

[lagrange.py](crates/deppy-python/examples/lagrange.py) は、有限群のラグランジュの定理を単一ファイルで証明する例です。群の公理を満たす演算、判定可能な部分群、全要素を重複なく列挙したリストを受け取り、`|G| = |H| × k` を満たす自然数 `k` の存在を示します。有限集合の分割と剰余類の要素数の補題も同じファイルに定義し、追加の公理なしで検査します。2元群の自明な部分群・全体部分群への適用例を含みます。

```sh
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/lagrange.py
```

[fermat.py](crates/deppy-python/examples/fermat.py) は上のラグランジュの定理を使い、有限体の非零元の乗法群について `a^(p−1) = 1` を証明します。入力は乗法群、非零元の全要素列挙、`p = 1 + 非零元の個数` の証拠です。元を含む可換な部分群を構成し、その要素の積とラグランジュの定理から、まず任意の有限群で `a^|G| = 1` を導きます。巡回部分群や元素の位数、累乗の結論は仮定しません。3元体の乗法群への適用例を含み、数学の定義と証明はPythonだけで実装しています。素数判定や整数の剰余演算から体を構成する部分は対象外です。

```sh
cargo run -p deppy-python --locked --offline -- --elaboration-steps 100000000 crates/deppy-python/examples/fermat.py
python3 scripts/check_fermat.py
```

`--elaboration-steps N` は各宣言の検査budgetを指定します。省略時は従来どおり1,000,000で、正の整数のみ受け付けます。budgetの増加は型検査や公理の扱いを変更しません。

`@verified`（局所再代入・分岐・単一while・仕様・手書きVC証明）の構文と検査境界は
[verifiedガイド](docs/verified.md)を参照してください。whileの不変条件・自然数尺度による停止性を検査できます。`verified_spec` で検査済み仕様を後続の定理から再利用できます。戻り値の `Refined[Nat/Bool, predicate]` と同時代入に対応し、[Fibonacciの実例](crates/deppy-python/examples/fibonacci.py)で停止性と再帰的仕様との一致を証明しています。

## 実行

RustのCargoを使用します。kernelとelaboratorに外部crate依存はありません。Python frontendはRuffのparser・AST・text size crateを `=0.0.12` に固定し、推移的な依存はCargo.lockで固定しています。初回は `cargo fetch --locked` で依存を取得してください。使用するRust toolchainでの検証手順は以下を参照してください。

数学APIのSphinxドキュメントは、証明ソースを実行せずdocstringを静的に抽出する。

```sh
uv run --with 'sphinx>=8.2,<9' sphinx-build -W -b html docs docs/_build/html
```

```sh
cargo test --workspace --offline
cargo run -p deppy-core --example identity --offline
cargo run -p deppy-elab --example implicit_identity --offline
cargo run -p deppy-elab --example nat_add --offline
cargo run -p deppy-elab --example zero_right --offline
cargo run -p deppy-elab --example vectors --offline
cargo run -p deppy-elab --example sigma --offline
cargo run -p deppy-elab --example records --offline
cargo run -p deppy-elab --example structural --offline
cargo run -p deppy-python --example check --locked --offline
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/basics.py
cargo fmt --all -- --check
cargo clippy --workspace --all-targets --offline -- -D warnings
```

進捗と未実装項目は[PROGRESS.md](PROGRESS.md)で管理しています。

## Crate構成

- `crates/deppy-core`：明示的なcore term、kernel、NbE、変換判定、公理依存に加え、kernel検査済みtermからruntime IRへのchecked projectionを提供します。trusted coreの中心です。
- `crates/deppy-elab`：名前付きAST、bidirectional elaboration、meta、定義と再帰の検査を担当します。
- `crates/deppy-python`：Ruffを使ったPython frontend、静的module解決、`@dependent`・`@verified`のloweringとVC生成を担当します。
- `crates/deppy-runtime`：`deppy-core`が生成したruntime IRを消費し、Pythonコード生成、runtime shim、公開境界wrapperと生成用CLIを提供する任意backendです。型検査と証明の妥当性には必要ありません。

`@verified`層はVerified HIRとWP/VC generationを持ち、`@dependent`と同じkernelで証明を検査します。生成したVCはdependent coreの証明としてkernelで再検査し、`verified_spec`として後続の証明から再利用します。現行機能と未実装の目標は[設計方針](docs/deppy2.md)で区別しています。

## ドキュメント

- [文書一覧と読む順序](docs/README.md)
- [実装状況と残件](PROGRESS.md)
- [設計方針と検査境界](docs/deppy2.md)
- [実装リファレンス](docs/reference.md)
- [証明言語のガイド](docs/proofs.md)と[一般帰納型・pattern matching](docs/dependent-phase1.md)
- [verifiedの仕様と証明](docs/verified.md)
- [数学ライブラリの現状と整備計画](docs/math-library.md)
