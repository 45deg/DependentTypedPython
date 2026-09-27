# DepPy 日本語ガイド

DepPyはPython風の構文を持つ依存型言語です。`@dependent` で全域関数と証明を書き、`@verified` で命令的な部分言語から検証条件を生成します。証明項はRust製kernelが検査します。入力のPythonファイルは静的に読み取り、証明を得るために実行しません。

```sh
cargo test --workspace --locked --offline
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/core/basics.py
cargo run -p deppy-python --locked --offline -- --goals path/to/proof.py
```

詳しい仕様は英語の[文書一覧](../README.md)から参照してください。特に[証明](../proofs.md)、[帰納型](../inductives.md)、[verified](../verified.md)、[未対応項目](../roadmap.md)を参照できます。
