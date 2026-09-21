# ドキュメント一覧

初めて使う場合は[プロジェクトのREADME](../README.md)から実行方法を確認してください。

| 文書 | 内容 |
| --- | --- |
| [実装状況と残件](../PROGRESS.md) | 対応済みの機能と未完了事項 |
| [設計方針](deppy2.md) | dependent・verified・kernel・runtimeの責務と検査境界 |
| [実装リファレンス](reference.md) | core、elaborator、frontend、runtimeの詳細と例 |
| [証明言語のガイド](proofs.md) | 証明項、ライブラリ、公理、hole、opaque定義 |
| [一般帰納型とpattern matching](dependent-phase1.md) | 帰納型宣言、依存分岐、受理範囲 |
| [verifiedの仕様と証明](verified.md) | VC、while、Refined、verified_spec、Fibonacci |
| [数学ライブラリ](math-library.md) | 実装済みAPIと今後の整備計画 |
| [数学APIリファレンス](math-api.rst) | Sphinxで生成するdocstringベースのAPI文書 |
| [開発・検証手順](development.md) | 再現コマンドと検証の限界 |

現行仕様は各ガイド、横断的な実装状況はPROGRESS、将来の方針は設計・整備計画に記載します。作業ログや過去のテスト件数は蓄積しません。機能を変更した際は、対応する仕様と残件を更新してください。
