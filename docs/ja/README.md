# DepPy 日本語ガイド

DepPyはPython風の構文を持つ依存型言語です。`@dependent` で全域関数と証明を書き、`@verified` で命令的な部分言語から検証条件を生成します。証明項は入力コードを実行せずに検査します。

DepPyは実験段階で、開発中です。対応するPython構文は一部に限られ、元のPythonコードと生成コードの動作が一般に一致することは証明されていません。制約は英語版READMEの[Current limitations](../../README.md#current-limitations)にまとめています。

詳しい仕様は英語の[文書一覧](../README.md)から参照してください。特に[証明](../proofs.md)、[帰納型](../inductives.md)、[verified](../verified.md)、[未対応項目](../roadmap.md)を参照できます。

## 元の定義ファイルを Python で実行する

Python 3.14 の環境にパッケージをインストールすると、元の `.py` を直接実行できます。

```sh
uv venv --python 3.14
uv pip install --python .venv/bin/python -e .
source .venv/bin/activate
python crates/deppy-python/examples/verified/direct.py
# 42
```

VS Code では、この `.venv/bin/python` を Python インタープリターに選択してください。
`deppy` の各モジュールと、生成したスタブによるコンストラクタの import 解決に対応しています。
標準ライブラリの定義は Rust の検査器と Python パッケージで共有しています。

直接実行時には証明や契約を検査しません。検証が必要な場合は同じファイルを別途
`deppy-python` で検査してください。`if __name__ == "__main__":` 内の呼び出しや
`print` は通常の Python として実行され、検査対象には含まれません。
暗黙の値引数の推論や消去された証拠に依存する実行には制限があります。
詳しくは [Python 実行ガイド](../python-runtime.md)を参照してください。
