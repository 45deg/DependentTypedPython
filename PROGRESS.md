# 実装状況と残件

2026-09-21時点の作業ツリーに基づく現状です。時系列の作業ログではなく、対応範囲と未完了事項を管理します。構文・検査境界の詳細は[文書一覧](docs/README.md)から参照してください。

## 実装済み

| 領域 | 現在の対応範囲 | 詳細 |
| --- | --- | --- |
| Kernel | 非累積的な具体的universe、Π・Σ・Eq/J、一般帰納型、positivity、NbE、公理依存、処理予算 | [リファレンス](docs/reference.md) |
| Elaboration | 暗黙引数、制限付きpattern unification、metaのscope/occurs check、最終coreの再検査 | [リファレンス](docs/reference.md#elaboration) |
| 証明言語 | 静的import、構造的再帰、依存pattern matching、hole/goal、opaque theorem、検査済み依存snapshotの再利用 | [証明ガイド](docs/proofs.md)、[帰納型](docs/dependent-phase1.md) |
| 標準型 | Nat・Vec・Finを一般帰納型へ移行。List・Bool・Sum・Option・Decidable、Listの四定理 | [帰納型](docs/dependent-phase1.md) |
| Verified | Nat/Bool、局所再代入・同時代入、分岐、純粋関数呼び出し、型注釈主体の契約、requires/ensures、限定した自動証明と手書きVC証明、名前付きVC goal | [verified](docs/verified.md) |
| ループ | 関数直下の単一while、局所Refinedからの不変条件候補、明示的不変条件、自然数尺度、初期化・保存・減少・終了のVCと名前付き証明 | [whileと停止性](docs/verified.md#whileと停止性) |
| 仕様の再利用 | opaqueなcompanion theorem、verified_spec、import/reexport、公理依存追跡、引数・戻り値・局所変数のRefined | [仕様の再利用](docs/verified.md#verified_specによる仕様の再利用) |
| 契約合成 | 単一whileの本文・終了後を含む契約合成、局所Refinedの代入VC、不変条件からの局所条件の復元、同じ基底型の条件変換 | [契約合成](docs/verified.md#契約による関数の合成と名前付きvc) |
| Runtime | checked projection、Python生成、不変データ表現、依存境界検査、高階field・関数引数のwrapper | [実行MVP](docs/reference.md#実行mvp) |
| 数学 | 加算・順序・リストの基礎API、Lagrange・Fermatの例、Fibonacciループの仕様との一致 | [整備計画](docs/math-library.md)、[Fibonacci](docs/verified.md#fibonacciの実例) |

## 残件

- **Elaboration**：キーワードによる暗黙引数指定、制約の保留・再試行、meta引数のpruning、より広い単一化、意味値・closureによる評価。
- **型体系・分岐**：universe polymorphism、相互帰納型、既存型作用素を介したnested recursion、非線形・中立な関数適用を含む添字pattern。一般の高階単一化や完全な自動証明探索は当面の非目標。
- **Verified**：ループ前の初期化での契約呼び出し、式中・同時代入内の契約呼び出し、ネスト・複数while、辞書式尺度・一般の整礎関係、局所Refined以外からの一般的な不変条件推論、一般の算術・証明探索、異なる基底型のrefinement変換と暗黙のrefinement subtyping。
- **数学ライブラリ**：乗算の残りの法則、例とstdlibの型の共有、有限列挙・並べ替え・群論のstdlib化。優先順と完了条件は[整備計画](docs/math-library.md)で管理。
- **Runtime・互換性**：外部Pythonからの証明入力、`Proof[...]`、任意の型族や消去した情報が必要な公開境界、ソース互換のrecord class、CPython 3.13での実行検証。
- **保証の拡張**：元のCPythonソースとVerified HIRの意味保存、extractionの一般的な意味保存、深い再帰に対するスタック・メモリ保証。verifiedの新APIの生成Python実行は未検証。

## 検証の入口

[開発・検証手順](docs/development.md)に再現コマンドと検証範囲をまとめています。テスト件数や過去の成功ログは進捗の根拠として固定せず、変更対象に応じて実行結果を確認してください。
