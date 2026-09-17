# 実装進捗

Chatlog.md第19節の順序に沿ったチェックリストです。チェック済みは実装・検証済み、未チェックは未実装または作業中です。MVP全体は未完成です。

## 1. 明示的コアとkernel

- [x] Rust workspaceと依存なしの`deppy-core`。
- [x] 非累積的な具体的universe階層、Π、λ、適用、let。
- [x] de Bruijn indexによる束縛、relevanceの保持。
- [x] closureベースのNbE、β・ζ簡約、Πのη変換。
- [x] 型合成・検査・正規化・型指定の等価性判定。
- [x] 不正なコア入力と処理予算超過の拒否。
- [x] 受理・拒否テスト19件、identity実行例。

## 2. Elaboration（初期実装済み）

- [x] kernelと独立した名前付き入力ASTと、metaを持つ内部項。
- [x] bidirectional checking：期待型からλの引数型を補う。
- [x] 暗黙引数の挿入と明示指定。
- [x] telescope・期待型を保持するmeta。
- [x] 制限付きpattern unification、occurs check、scope check。
- [x] 未解決metaの拒否と、metaを含まないコアへの変換。
- [x] metaの解と最終コアをkernelで再検査。
- [x] 推論の受理・拒否テスト、実行例。

対応範囲は、名前付きAST、具体的universe、Π・λ・適用・注釈・期待型付きholeです。暗黙引数の明示指定は位置指定です。単一化は、metaに付随するtelescopeの引数が相異なるローカル変数である範囲に限定しています。

残る拡張：

- [ ] elaboratorのletとグローバル定義。
- [ ] キーワードによる暗黙引数指定。
- [ ] 制約の保留・再試行、meta引数のpruning、より広い高階patternの解決。
- [ ] elaboratorの意味値・closureによる評価（現在は束縛の捕獲を避けた置換と弱頭簡約）。
- [ ] Pythonの名前とsource spanに基づく診断。

## 3. 帰納型と証明

- [ ] Nat、Z、S、依存eliminator、加算。
- [ ] Eq、refl、J、cong、限定したtransport。
- [ ] Vec、Fin、fin0_elim。
- [ ] constructor patternと限定した入れ子の依存パターン。
- [ ] 指定引数に対する構造的再帰とrecursorへの変換。
- [ ] Σ、Pair、projection。
- [ ] 非再帰・不変なdependent record。

## 4. Pythonとの接続

- [ ] CPython 3.12〜3.14によるparse/compile検証（ユーザーコードは実行しない）。
- [ ] バージョン付きAST schema、source span、静的名前解決。
- [ ] `@dependent`・`@record`の認識とHIRへの変換。
- [ ] 静的importと検査済みインターフェース。
- [ ] 消去対象の使用検査、消去、runtime IR。
- [ ] ランタイムと境界データの検証・再構築。
- [ ] Pythonコード生成とソース／生成コードの差分実行。

## 5. MVP受け入れ条件

- [ ] 第17.1節：Pythonのidentity例。
- [ ] 第17.2節：Vec append例。
- [ ] 第17.3節：Finによるget例。
- [ ] 第17.4節：zero_right証明例。
- [ ] 第17.5節：Σとrecordの例。
- [x] `Type : Type`の拒否（kernel）。
- [ ] 発散する証明・添字への再代入の拒否（Python frontend）。
- [x] metaのscope escapeの拒否（内部項と名前付き入力AST）。
- [ ] `Fin[0]`の偽造・不正な消去・暗黙のKの拒否。

## 現在の制約

消去の安全性やPython実行の意味保存はまだ検証できません。計算ステップの予算はRustのスタック・メモリを完全に保護するものではありません。ソース位置付き診断、universe polymorphism、一般の高階単一化は未実装です。

## 検証記録（2026-09-18）

- `cargo test --workspace --offline`：52件成功（kernel 19件、meta内部11件、elaboration統合22件）。
- `cargo clippy --workspace --all-targets --offline -- -D warnings`：成功。
- `cargo fmt --all -- --check`：成功。
- `cargo run -p deppy-elab --example implicit_identity --offline`：暗黙型引数を補ったコアの生成とkernel再検査が成功。
- Pythonの構文検査・実行、コード生成の検証は未実施。

次は固定preludeのNatと依存eliminatorを実装し、elaborationへ接続します。
