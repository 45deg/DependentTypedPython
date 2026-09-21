# DepPy2の設計方針

DepPy2は、Python構文を共有する二つの層を、小さな依存型kernelで接続する。

- `@dependent`は、Agdaのように全域関数と証明を書くための独立した証明支援系である。
- `@verified`は、命令的なPythonの部分言語から検証条件（VC）を生成する層である。

`@verified`を実装するために`@dependent`をVC専用の内部言語へ縮小しない。反対に、命令的プログラムの状態や制御構造をkernelへ直接追加しない。両者は、`@verified`が生成した命題とその証明を、`@dependent`が検査・再利用する境界で接続する。

```text
Python source
├── @dependent
│     └── elaboration / goals / totality checking
│
└── @verified
      └── Verified HIR / WP / VC generation
                    │
                    ▼
          dependent core proof
                    │
                    ▼
              small kernel
                    │
                    └── verified_specとして再利用
```

## 残す基盤

### Small coreとkernel

kernelは、完全に明示化した小さな型理論だけを検査する。長期的に残す中核は次のとおりである。

- universe階層
- Π型
- Σ型
- `Eq`、`refl`、等式消去`J`
- グローバル定義と明示的な公理
- NbEによる正規化と変換判定
- 公理依存の追跡
- 最終的な証明項の再検査

一般の再帰帰納型とindexed familyを実装済みで、Nat・Vec・Finは通常の検査済み `DataDecl` として登録する。専用core項・型検査規則・NbE規則は削除済み。公開構文・Rust builder・Pythonのint/tuple表現は互換adapterとして維持する。

### `@dependent`: 独立した証明支援系

`@dependent`は、`@verified`がなくても利用できる全域な依存型言語として完成させる。現在すでに、具体的なuniverse、Π・Σ・等式、Nat・Vec・Fin、限定された構造的再帰、module、静的import、透明定義、公理依存追跡を利用できる。

次の基盤は実装済みである。受理範囲の制約は[一般帰納型の仕様](dependent-phase1.md)を参照。

- パラメータとindexを持つユーザー定義帰納型
- strict positivity checking
- dependent pattern matchingと網羅性検査
- 構造的再帰の停止性検査
- 型付きhole、局所文脈、goal表示
- 式単位のsource spanと型エラー診断
- 本体を変換判定で展開しないopaque theorem
- 一般帰納型の上に構築するList、Bool、Sum、Option、Decidableなどの標準ライブラリ

一般の高階単一化や完全な自動証明探索を前提にはしない。明示的な証明項とbidirectional elaborationを基本にし、補助的な自動化は後から追加できる境界を保つ。

### Moduleと名前解決

moduleは標準ライブラリとユーザーライブラリの単位として残す。トップレベルの`deppy`をpreludeとし、`deppy.equality`や`deppy.vectors`などの責務別moduleも提供する。kernel primitiveとPythonで記述した派生定義は、利用者からは同じmoduleの定義として見える。

ユーザー定義帰納型、opaque theorem、検査済みverified仕様も同じ名前環境と検査済みinterfaceを通す。Python moduleの実行結果を名前解決に使わず、ソースと検査済みinterfaceを静的に読む方針を維持する。

## `@verified`: 命令的Pythonの検証層

`@verified`は`@dependent`とは別のfrontend層として実装する。対象プログラムをVerified HIRへlowerし、weakest precondition（WP）または同等の規則からVCを生成する。

現在の対象は次の範囲に限定する。構文と制約は[verifiedガイド](verified.md)を参照。

- Nat・Boolなどの値と局所変数
- 局所再代入と平坦なtupleの同時代入、局所Refinedの代入VC、同じ基底型の条件変換
- `if`
- 関数直下の単一 `while`
- pureな関数呼び出しと、単一whileの本文・終了後を含むverified契約の合成
- `requires`と`ensures`
- loopの`invariant`と`decreases`
- `proofs` による名前付きVCの証明と、未指定goalの表示

VCには、事前条件、分岐、invariantの初期化・保存、loop終了後の事後条件、decreasesの非負性と減少を含める。heap、alias、例外、I/O、asyncなどの効果は、この最初のVerified HIRには含めない。

VCは別の論理式やsolver固有の式で完結させず、dependent coreの命題へ変換する。VCの証明は、まず`@dependent`で書いた通常の証明項として受け取り、kernelで再検査する。tacticやSMTを追加する場合も、同じ検査境界を変えない。

## `verified_spec`による接続

検証済み関数の仕様は、`verified_spec(f, 引数..., 事前条件の証拠)` で後続の `@dependent` / `@theorem` から利用できる。`Refined[Nat/Bool, predicate]` は戻り値では事後条件へ、引数では事前条件へ変換する。引数の条件と明示的な `requires` の証拠は宣言順のΣでまとめ、呼び出し時に検査する（条件が一つなら直接使う）。

関数登録後に `requires(inputs) → ensures(inputs, f(inputs))` を型とするcompanion theoremをkernelで再検査し、opaqueとして登録する。関数本体のVC証明を使い、ループでは標準ライブラリの `loop_correct` による停止性と事後条件の証明を保持する。無検査の公理は追加しない。

import alias・再exportでも関数の由来と定理IDを保持し、通常関数や局所変数をverified関数として扱うことは拒否する。ユーザー公理への依存は利用先へ伝播する。具体例は[仕様の再利用](verified.md#verified_specによる仕様の再利用)を参照。

呼び出し元のverifiedコードでも、このcompanion theoremを使う。呼び出し時の事前条件を証明した上で、
続きの証明を任意の結果とその事後条件について構成し、実際の結果と仕様の証拠へ適用する。
これにより呼び出し先の本体に依存せず契約を合成する。現在の構文と制約は
[契約合成](verified.md#契約による関数の合成と名前付きvc)で管理する。

## Runtimeとextractionの位置づけ

実行とPythonコード生成は、証明の妥当性を決めるkernelとは別の関心事である。現在は、kernel検査済みtermから`RuntimeTerm`・`RuntimeType`を導くchecked projection（`Kernel::erase`と`runtime_signature`）を`deppy-core`に残し、その結果を消費するPythonコード生成、runtime shim、公開境界wrapperとCLIを`crates/deppy-runtime`へ分離している。

このruntime経路は、既存の証明付きプログラムを実行する用途と、将来のextraction実験のために保持する。ただしchecked projectionを含め、次のものの成立条件にはしない。

- kernelのTCB
- `@dependent`の型検査成立条件
- `@verified`からVCを生成する論理
- DepPy2の主要な研究貢献

`@verified`の実行対象は、原則として検証したものと同じPython subsetである。既存のpure coreからPythonを生成するbackendを、そのまま命令的Pythonの意味論として拡張しない。Verified HIRの意味論とruntime extractionは別々に検証できる境界を置く。

## Crate境界

責務は次のように分ける。

| Crate | 責務 |
|---|---|
| `deppy-core` | 明示的なcore term、型検査、NbE、変換判定、公理依存。現在は検査済みtermからruntime IRへのchecked projectionも保持する。TCBの中心。 |
| `deppy-elab` | 名前付きAST、bidirectional elaboration、meta、定義・帰納型・再帰の検査。 |
| `deppy-python` | Python構文の解析、module解決、`@dependent` frontend、`@verified`の構文入口、Verified HIRへのloweringとVC生成。 |
| `deppy-runtime` | `deppy-core`のruntime IRを消費するPython生成、runtime shim、境界wrapperとCLI。型検査から分離した任意backend。 |

Verified HIR、WP、VC generationが大きくなった場合は、`deppy-python`の内部moduleから独立crateへ切り出す。最初からcrateを増やすこと自体は目標にしない。

## 実装境界を保つ方針

- Python生成・runtime shim・境界wrapper・生成CLIは `deppy-runtime` に置く。`deppy-python` は静的検査だけで利用できる。
- `J`、eliminator、明示lambda、型注釈は低水準のproof-term APIとして維持する。
- resolver、module graph、builtin registry、linkerは静的に処理する。Python moduleの実行結果を信頼しない。
- Python versionと処理予算は `FrontendOptions` に集約する。
- 公理依存を表示し、将来solverを接続する場合も、証明再構成とkernelの再検査を境界にする。

## 段階的ロードマップ

### Phase 1: 証明支援系の基盤（実装済み）

1. ユーザー定義帰納型とindexed family
2. positivity、coverage、termination
3. dependent pattern matching
4. holeとgoal表示
5. opaque theoremと検査済みmodule interface
6. 一般帰納型上の標準ライブラリ
7. Nat、Vec、Finの専用実装から標準ライブラリへの段階的移行

受け入れ例は、Rust側に定理固有のprimitiveを加えず、Listの`append_assoc`、`map_identity`、`map_composition`、`reverse_involution`と、Vecの安全な操作を記述・検査できることとする。

### Phase 2: `@verified`とVC generation（単一whileまで実装済み）

1. Verified HIRとその明示的な意味論
2. `requires`、`ensures`
3. 局所代入と`if`
4. `while`、`invariant`、`decreases`
5. WPとVC生成
6. 生成VCを`@dependent`のgoalとして提示

カウントダウン、累積、Fibonacciの例で、手書き証明による部分正当性と停止性を扱う。ネスト・複数ループ、一般の整礎関係、自動証明探索は範囲外である。

### Phase 3: proof-producing bridge（実装済み）

1. VC proofのkernel再検査
2. 検証済み仕様からcore theoremを構築
3. `verified_spec`で後続の証明から再利用
4. 公理依存とtrusted boundaryの表示

この段階で、命令的Pythonの検証結果をdependent theoremとして合成できることを示す。

### Phase 4: 任意の自動化とbackend（今後の拡張）

- tactic
- SMT certificateまたはproof reconstruction
- proof erasureとextractionの意味保存
- runtime backendの対応範囲拡大

これらは前段のsoundness境界を置き換えず、上に追加する。

## 当面の非目標

次はDepPy2の初期ship条件に含めない。

- funext、UIP、K、univalence、排中律をkernelへ組み込むこと
- 一般の高階単一化
- 完全な自動証明探索
- universe polymorphismとcumulativity
- 相互帰納型、coinduction、quotient
- heap、alias、object mutation、例外、I/O、asyncを含む一般effect system
- solver自体を信頼して証明済みと扱うこと
- 任意のPythonプログラムとの互換性
- runtime extractionをkernelの正しさやVC bridgeの前提にすること

funextなどは「未実装の定理」ではなく基礎体系の選択として扱う。必要な原理は明示的な公理として宣言し、依存関係を追跡する。

## 文書の役割

この文書は構成と設計方針を定める。現在の対応範囲と残件は[PROGRESS](../PROGRESS.md)、正確な構文と制約は[一般帰納型](dependent-phase1.md)・[verified](verified.md)・[実装リファレンス](reference.md)で管理する。元のCPythonソースとの意味保存は未実装であり、Verified HIRの検査成立と区別する。
