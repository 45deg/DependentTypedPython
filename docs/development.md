# 開発・検証手順

リポジトリのルートで実行します。Rustの依存はCargo.lockに従います。初回は `cargo fetch --locked` で取得してください。runtime統合試験には `python3` が必要です。

## Rust

```sh
cargo test --workspace --locked --offline
cargo fmt --all -- --check
cargo clippy --workspace --all-targets --locked --offline -- -D warnings
```

対象を絞る場合は `cargo test -p deppy-python --locked --offline --test refined` のように統合テストを指定できます。検査器には受理例だけでなく、不正な型・証明・停止性・境界値の拒否試験があります。

## Python

```sh
uv run --no-project --offline --python 3.12 scripts/check_python_syntax.py
uv run --no-project --offline --python 3.14 scripts/check_python_syntax.py
uv run --no-project --offline --python 3.12 scripts/check_python_runtime.py
uv run --no-project --offline --python 3.14 scripts/check_python_runtime.py
python3 scripts/check_fermat.py
```

構文検証はソースをcompileするだけで、証明やプログラムを実行しません。runtime差分試験は既存fixtureとテスト専用参照モデルを比較します。参照モデルは型検査器ではなく、差分一致は任意のPythonとの意味保存の証明ではありません。CPython 3.13の構文targetは対応していますが、実行検証は残件です。

## ドキュメント

```sh
uv run --with 'sphinx>=8.2,<9' sphinx-build -W -b html docs docs/_build/html
```

数学APIは `docs/_ext/deppy_api.py` がdocstringを静的に抽出し、証明ソースを実行しません。Markdownのガイドはリポジトリで参照し、Sphinxは数学APIを生成します。Markdownの相対リンクは別に確認してください。
