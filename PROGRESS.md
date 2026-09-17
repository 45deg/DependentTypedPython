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

対応範囲は、名前付きAST、具体的universe、Π・λ・適用・注釈・期待型付きhole、Nat・Z・S・明示的なNat eliminator、Eq・refl・J、Vec・Finとそれらの依存eliminator、fin0_elim、Σ・Pair・fst・snd、名前付きrecord宣言と検査済みコア項の埋め込みです。暗黙引数の明示指定は位置指定です。単一化は、metaに付随するtelescopeの引数が相異なるローカル変数である範囲に限定しています。

残る拡張：

- [ ] elaboratorのletとグローバル定義。
- [ ] キーワードによる暗黙引数指定。
- [ ] 制約の保留・再試行、meta引数のpruning、より広い高階patternの解決。
- [ ] elaboratorの意味値・closureによる評価（現在は束縛の捕獲を避けた置換と弱頭簡約）。
- [ ] Pythonの名前とsource spanに基づく診断。

## 3. 帰納型と証明

- [x] Nat、Z、Sのコア項・型検査・NbE。
- [x] Natの依存eliminatorとι簡約。
- [x] 第1引数について再帰する加算、elaboratorへの接続。
- [x] Eq、refl、Jのコア項・型検査・NbEとelaboratorへの接続。
- [x] Jから導いたcong・transportの型検査と計算規則。
- [x] Natの帰納法によるzero_right証明（名前付きAST、一般形の検査と数値での正規化）。
- [x] proof irrelevance・equality reflection・K形motiveの拒否テスト。
- [ ] transportのruntime representation検査と安全な消去。
- [x] Vec、VNil、VCons、Fin、FZ、FSのコア項・型検査・NbE。
- [x] Vec・Finの依存eliminator、ι簡約、fin0_elim。
- [x] elaboratorへの接続、carrier・長さ・上限の暗黙引数推論。
- [x] appendとgetの名前付きAST、一般形の型検査と実行例。
- [ ] ユーザー定義帰納型の宣言検査・positivity checking。
- [ ] constructor patternと限定した入れ子の依存パターン。
- [ ] 指定引数に対する構造的再帰とrecursorへの変換。
- [x] Σ、期待型によるPairの検査、依存するfst・snd射影。
- [x] 名前付きASTによるpackの一般形と射影の実行例。
- [x] 非再帰dependent recordの名前付き宣言、名目的な単一コンストラクタ型と依存射影への変換。
- [x] 先行フィールドへの依存、宣言の原子的な登録、同じ形の型の区別とΣとの明示的な相互変換。
- [ ] Python runtimeのrecord class生成・不変性の保証。

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
- [x] `Fin[0]`の偽造・不正なfin0_elimの拒否（kernelとelaborator）。
- [ ] 不正なruntime消去とPythonのパターンからの暗黙のKの拒否。

## 現在の制約

消去の安全性やPython実行の意味保存はまだ検証できません。計算ステップの予算はRustのスタック・メモリを完全に保護するものではありません。ソース位置付き診断、universe polymorphism、一般の高階単一化は未実装です。

## 検証記録（2026-09-18）

- `cargo test --workspace --offline`：197件成功（kernel 79件、meta内部19件、elaboration統合99件）。
- `cargo clippy --workspace --all-targets --offline -- -D warnings`：成功。
- `cargo fmt --all -- --check`：成功。
- `cargo run -p deppy-elab --example implicit_identity --offline`：暗黙型引数を補ったコアの生成とkernel再検査が成功。
- `cargo run -p deppy-elab --example nat_add --offline`：加算をelaborateしてkernelで検査し、`2 + 3 = 5`を正規化で確認。
- `0 + n ≡ n`と`S(n) + m ≡ S(n + m)`を確認。`n + 0 ≡ n`の型変換は拒否。
- `cargo run -p deppy-elab --example zero_right --offline`：一般の`n + 0 = n`の証明をkernelで検査し、`zero_right(2)`の正規形が`refl(2)`になることを確認。
- 証明に依存するJ、neutralなJの保持、異なるuniverseでのcong・transport、依存する型族のtransportを検査。
- `cargo run -p deppy-elab --example vectors --offline`：appendとFinによるgetをkernelで検査・正規化して期待値を確認。
- 添字・分解対象の両方に依存するVec/Fin motive、neutralな消去、分岐の帰納法仮定、長さ・上限の偽造拒否を検査。
- 小さなベクタのappend・全位置のget、型を要素にするベクタ、変数の長さに対するgetのFZ/FS計算規則を検査。
- `cargo run -p deppy-elab --example sigma --offline`：packの一般形と、長さ・ベクタの射影および依存する結果型を確認。
- Σのuniverse・束縛・暗黙引数推論、成分のhole解決、不正な成分・Σのη・scope escapeの拒否を検査。
- `cargo run -p deppy-elab --example records --offline`：SomeVecの宣言、pack・as_record・as_pairの一般形、両射影の計算を確認。
- 名目的な型の区別、空record・型を保持するrecord・依存するパラメータ列、自己参照・前方参照・不正なuniverse・不正なeliminatorの拒否を検査。
- Pythonの構文検査・実行、コード生成の検証は未実施。

次は限定した依存パターンと構造的再帰のeliminatorへの変換へ進みます。Pythonのmatchや再帰関数からの変換はまだ実装していません。
