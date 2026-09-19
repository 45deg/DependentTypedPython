# 実装進捗

Chatlog.md第19節の順序に沿ったチェックリストです。チェック済みは実装・検証済み、未チェックは未実装または作業中です。既存のidentity・append・get・zero_right・SomeVecを型検査からPython生成・実行まで通す実行MVPは完了しました。Chatlogの全仕様を実装したものではなく、残る拡張は未チェックのまま管理します。

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

- [x] elaboratorのlet、検査済みの透明なグローバル定義、型の中での定義展開。
- [ ] キーワードによる暗黙引数指定。
- [ ] 制約の保留・再試行、meta引数のpruning、より広い高階patternの解決。
- [ ] elaboratorの意味値・closureによる評価（現在は束縛の捕獲を避けた置換と弱頭簡約）。
- [x] Pythonの名前解決・構文エラーのsource range、宣言単位の型エラー位置。
- [ ] elaborator内部の式単位のsource spanと詳細な型エラー診断。

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
- [x] 関数HIRのNat・Vec・Fin constructor pattern、網羅性検査、限定した入れ子のFin分岐。
- [x] 関数HIRの指定引数に対する直接の構造的再帰、後続引数の一般化、recursorへの変換。
- [x] append・get・zero_rightを、明示的なmotiveを持たない分岐と自己呼び出しから生成。
- [x] Pythonのmatch・return・自己呼び出しから関数HIRへの変換（match、let列とreturn、motive universeの具体値指定）。
- [x] Σ、期待型によるPairの検査、依存するfst・snd射影。
- [x] 名前付きASTによるpackの一般形と射影の実行例。
- [x] 非再帰dependent recordの名前付き宣言、名目的な単一コンストラクタ型と依存射影への変換。
- [x] 先行フィールドへの依存、宣言の原子的な登録、同じ形の型の区別とΣとの明示的な相互変換。
- [ ] Python runtimeのrecord class生成・不変性の保証。

## 4. Pythonとの接続

- [x] Ruff parser・AST・text sizeを0.0.12に固定し、Rustから直接解析。
- [x] Python 3.12・3.13・3.14のtarget指定、バージョンによる構文制限の拒否。
- [x] Ruff ASTから名前付きExprへの変換、source range、ローカル名・検査済みグローバル名の解決。
- [x] 裸の`@dependent`、型引数・型注釈・不変の代入・returnの検査。
- [x] トップレベルpreludeと責務別deppy APIの静的import・別名。ユーザーコード・注釈は実行しない。
- [x] fixtureをCPython 3.12.0・3.14.3でcompile検証。
- [ ] CPython 3.13のcompile検証。
- [x] Pythonの`match`・構造的再帰を既存関数HIRへ接続。Nat・Vec・Finと暗黙型引数の補完。
- [x] cong・空Fin消去のPython接続と、Fin boundのワイルドカード。
- [x] 再帰分岐内のreturn前のlet。期待型・依存型・停止性検査を保持。
- [x] match前のローカル定義。分岐前の検査を保持し、依存する値を各分岐で再展開。入れ子のFin分岐にも対応。
- [x] Pythonの`@record`を既存record宣言へ接続。先行フィールド参照・型引数・コンストラクタ・射影。
- [x] recordの同名フィールドを受け手の名目的な型から選択。連続する射影・型別名・let・関数HIRに対応。
- [x] frontendのrecord level・再帰motive levelの具体値指定。
- [ ] Vecコンストラクタ・cong・fin0_elimのuniverse指定（現在0）。
- [ ] 静的importと検査済みインターフェース。
- [x] 消去対象の使用検査、型・暗黙引数の消去、runtime IR。一般のJでは証明トークンを保持。
- [x] Nat・Vec・Fin・Sigma・recordの不変runtime表現と、対応する境界データの検証・再構築。
- [x] Pythonコード生成CLIとソース／生成コードの差分実行。
- [ ] `Proof[...]` 構文、高階・任意の型族の境界検査。
- [x] 使用条件を満たす証明結果・証明letの計算全体の消去（下記2026-09-20追記）。

## 5. MVP受け入れ条件

- [x] 第17.1節：Pythonのidentity宣言の静的検査と、生成コアの計算。
- [x] 第17.1節：Pythonランタイムでの実行と消去。
- [x] 第17.2節：PythonのVec append宣言の静的検査と生成コアの計算。
- [x] 第17.2節：Pythonランタイムでのappend実行。
- [x] 第17.3節：Pythonのget宣言の静的検査と生成コアの計算。
- [x] 第17.3節：Pythonランタイムでのget実行。
- [x] 第17.4節：Pythonのzero_right証明の静的検査と生成コアの計算。
- [x] 第17.4節：Pythonランタイムでの実行。証明のpayloadと公開結果は消去し、内部Jのトークンは保持。
- [x] 第17.5節：PythonのΣとSomeVecの静的検査、相互変換と生成コアの計算。
- [x] 第17.5節：Pythonランタイムでのrecord生成・実行。
- [x] `Type : Type`の拒否（kernel）。
- [ ] 発散する証明・添字への再代入の拒否（Python frontend）。
- [x] metaのscope escapeの拒否（内部項と名前付き入力AST）。
- [x] `Fin[0]`の偽造・不正なfin0_elimの拒否（kernelとelaborator）。
- [ ] 不正なruntime消去とPythonのパターンからの暗黙のKの拒否。

## 現在の制約

使用検査の拒否テストと、対象fixtureでのソース／生成コードの差分実行を実施しています。一般的な意味保存の形式証明はありません。外部Pythonからの証明入力は拒否し、消去した添字が境界検査に必要な関数・高階の境界・任意の型族はコード生成時に拒否します。型パラメータはopaqueな不変データとして扱い、任意のPythonクラスを検証する仕組みではありません。計算ステップの予算はRustのスタック・メモリを完全に保護するものではありません。型エラーの位置は関数宣言単位です。universe polymorphism、一般の高階単一化は未実装です。

## 検証記録（2026-09-19）

- `cargo test --workspace --offline`：293件成功（kernel 88件、meta内部19件、elaboration統合133件、Python frontend・runtime 53件）。
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
- `cargo run -p deppy-elab --example structural --offline`：関数HIRから生成したappend・get・zero_rightをkernelで検査し、具体値での計算を確認。
- 直接の部分構造以外への再帰、変更された固定引数・不正な添字、非網羅・重複分岐、名前の捕獲、対応外の入れ子の分岐を拒否。
- letの依存型・シャドーイング・metaのscope・未使用の不正な値の拒否を検査。
- グローバル定義の登録失敗時の状態保持、自己／前方参照・重複登録の拒否、closure内での展開と予算消費を検査。
- `cargo run -p deppy-python --example check --locked --offline`：Pythonの5宣言を型検査し、twice(Z)・reflexive(Z)を生成コアで計算。
- Python CLIの実行成功。Unicodeの名前とbyte range、再代入・名前の捕獲・型不一致・target-version構文エラーの拒否を検査。
- `scripts/check_python_syntax.py`：CPython 3.12.0・3.14.3でfixtureのコンパイル成功。ユーザーコードは実行していない。
- Python add・append・Fin rankの静的検査と生成コアの計算を確認。不正な再帰・非網羅／重複分岐・captureのscope違反を拒否。
- Python getを長さ1〜4の全位置で計算し、zero_right(0〜4)の正規形がreflになることを確認。不正な証拠・再帰先を拒否。
- Python SomeVecとΣの往復変換、型引数の推論・明示、空record、構造的再帰内でのrecord利用と依存する射影を検査。
- 名目的な型の取り違え、長さの不一致、自己／前方参照、未知のフィールド・受け手の型が不明な射影を拒否。フィールド名とλ／import名の捕捉防止を検査。
- 再帰分岐内letによる帰納法仮定の保持、期待Sigma型の伝播、未使用の不正な値・scope違反・別名経由の再帰先の拒否を検査。
- 同名・異なる型のrecordフィールドを型から選び、依存する結果型・連続する射影・高いuniverse・失敗した再登録後の保持を検査。
- `branch_fields.py` をPython frontendのCLIで静的検査し、生成コアでcount(2) = 2を確認。
- Pythonの高いrecord／motive levelの検査と生成コアの計算、level不整合・不正リテラル・未知／重複オプションの拒否を検査。
- match前letのNat・Vec・Finに対する絞り込み、入れ子のFin分岐、期待Sigma型、未使用の不正な値・名前の捕捉・再帰先の別名化の拒否を検査。
- runtime統合10件：get、zero_right、record往復、append、Fin再帰、match前let、消去の誤用、型・添字・可変値・証明入力の拒否、256のリテラル生成を検証。リテラル検査はRustの再帰的走査用に16 MiBのテストスレッドを使用。
- `scripts/check_python_runtime.py`：Python 3.12.0・3.14.3それぞれでソース／生成コードの244比較成功。参照モデルはテスト専用。
- 大きなaddの生成closure呼び出しでPythonのRecursionErrorを確認。スタック制約の解消は未実装。

実行MVPの完了条件は達成済みです。universe指定の追加やモジュール間インターフェースなどは、その後の拡張として扱います。

## reverse_getの証明（2026-09-19）

- `examples/reverse.py` に `snoc`・`reverse`・`last`・`weaken`・`mirror` と参照補題、`reverse_get` を実装。
- 添字値に依存する戻り値型を持つ入れ子のFin分岐と、Jから導く `trans` に対応。kernelの規則・公理は追加せず、Python frontendの検査予算を1,000,000に拡大。
- Python 3.12・3.13・3.14を対象とするfrontendで一般の証明を検査。長さ1〜4の全位置で証明の正規形が `refl` になること、誤った証明・添字・つながらない等式を拒否することを検証。
- 生成Pythonで長さ0〜6の反転、全位置のmirrorと参照結果、証明の実行、Fin[0]入力の拒否を検証。

## 汎用的な証明項とPythonライブラリ（2026-09-20）

- Pythonから型注釈付き／期待型によるλ、暗黙λとPi、J、Nat/Vec/Fin/record eliminator、明示的な高universeのVec構築、型付き定数を記述可能。
- 等式補題を `stdlib/deppy/equality.py`、Finの依存分岐を `fin.py`、ベクタ操作と参照補題を `vectors.py` に実装。frontendのcong/trans専用変換を除去し、Rustのtrans定義を削除。
- 静的なソースimport・alias・再export・名目的recordのimportに対応。CLIのファイル解決と、Rust APIからのSourceResolverを追加。循環・未検査名・名前の衝突を拒否。
- Python APIを `core`・`nat`・`equality`・`sigma`・`fin`・`vectors`・`records` に分割。組み込みとPython製の派生定義を同じモジュールから公開し、トップレベル `deppy` をpreludeとして構成。
- kernelに型検査済みの不透明な公理宣言を追加。等式反映や新しい簡約規則は追加せず、公理依存を型・定義・record経由で追跡。実行時の公理をダミー実装せず、コード生成時に拒否。
- `reverse_explicit.py` で、構造的match変換を使わないPythonの明示的な証明を検査・正規化・実行。`axioms.py` は関数外延性を仮定する例。
- 詳細な構文・ライブラリ・制約は `docs/proofs.md` に記載。一般の再帰帰納型やuniverse polymorphismは未対応のまま。

検証：workspace全テスト、追加のCLI・生成Python実行テスト、Clippy（警告をエラー化）、fmtが成功。CPython 3.12.0・3.14.3で標準ライブラリを含む14ソースの構文検証、既存5fixtureの各244ケースの差分実行が成功。


### 2026-09-20：使用条件を満たす証明の消去

- `Eq` の結果位置で証明計算を消去し、使用のない証明letを除去。暗黙の証明引数の使用検査にも適用。
- 計算用の証明と消去済み結果のマーカーを区別。データを返すJ、高階引数、let・データフィールドでは必要な証明を保持。
- 計算に必要なグローバルは本体を展開して検査し、公理・消去指定の証明が計算用トークンに化けることを拒否。
- kernelの定義的等しさ・公理依存情報は不変。明示引数と証明フィールドの自動削除は対象外。
- 検証：`cargo test --workspace --locked --offline`、Clippy（全target・警告をエラー扱い）、fmtを通過。生成Pythonの実行テストで証明再帰の除去、計算用Jの保持、公理・消去済み結果の誤使用拒否を確認。CPython 3.12/3.14で15ファイルのcompile検証、各244件の既存ソース／生成コード比較を通過。
