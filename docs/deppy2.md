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

現在はNat、Vec、Finなどを専用のコア項として持つ。これは現行実装であり、最終形ではない。一般の再帰帰納型とindexed familyが実装できた段階で、Nat、Vec、Finを標準ライブラリの定義へ移し、専用の型検査・簡約規則を一般の帰納型機構へ統合する。移行が完了するまでは、既存の証明能力を保つため専用実装を残す。

### `@dependent`: 独立した証明支援系

`@dependent`は、`@verified`がなくても利用できる全域な依存型言語として完成させる。現在すでに、具体的なuniverse、Π・Σ・等式、Nat・Vec・Fin、限定された構造的再帰、module、静的import、透明定義、公理依存追跡を利用できる。

Agdaに近い利用体験へ進むため、次を追加する。

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

将来のユーザー定義帰納型、opaque theorem、生成VCも同じ名前環境と検査済みinterfaceを通す。Python moduleの実行結果を名前解決に使わず、ソースと検査済みinterfaceを静的に読む方針を維持する。

## `@verified`: 命令的Pythonの検証層

`@verified`は`@dependent`とは別のfrontend層として実装する。対象プログラムをVerified HIRへlowerし、weakest precondition（WP）または同等の規則からVCを生成する。

最初の対象は次の範囲に限定する。

- Nat・Boolなどの値と局所変数
- 代入
- `if`
- `while`
- pureな関数呼び出し
- `requires`と`ensures`
- loopの`invariant`と`decreases`

VCには、事前条件、分岐、invariantの初期化・保存、loop終了後の事後条件、decreasesの非負性と減少を含める。heap、alias、例外、I/O、asyncなどの効果は、この最初のVerified HIRには含めない。

VCは別の論理式やsolver固有の式で完結させず、dependent coreの命題へ変換する。VCの証明は、まず`@dependent`で書いた通常の証明項として受け取り、kernelで再検査する。tacticやSMTを追加する場合も、同じ検査境界を変えない。

## `verified_spec`による接続

検証済み関数の仕様は、後続の`@dependent`コードから`verified_spec`として利用できるようにする。

```python
@dependent
def use_sum_loop(n: Nat) -> Eq[Nat, logical_result(sum_loop, n), triangular(n)]:
    return verified_spec(sum_loop, n)
```

`verified_spec`を無検査の公理として追加してはならない。少なくとも次を結ぶ検査済みの項または証明生成規則として設計する。

- verified functionの仕様と対象となる意味論
- 生成したVC
- VCに対するcore proof
- 公開する定理の型

最終的な定理は通常のcore proofとしてkernelが検査し、公理や未検査のsolver結果への依存も既存の依存追跡で確認できるようにする。この接続がDepPy2の研究上の中心である。

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
| `deppy-python` | Python構文の解析、module解決、`@dependent` frontend。将来は`@verified`の構文入口とVerified HIRへのloweringも担当する。 |
| `deppy-runtime` | `deppy-core`のruntime IRを消費するPython生成、runtime shim、境界wrapperとCLI。型検査から分離した任意backend。 |

Verified HIR、WP、VC generationが大きくなった場合は、`deppy-python`の内部moduleから独立crateへ切り出す。最初からcrateを増やすこと自体は目標にしない。

## 整理・分離の判断

今回、Pythonコード生成、runtime shim、公開境界wrapper、生成用CLIとruntime統合テストを`deppy-runtime`へ移した。これにより、`deppy-python`は静的検査だけで利用でき、実行backendは証明支援系の成立条件ではなくなった。旧`--emit-python`と`deppy-python`の生成APIは互換層を置かずに削除した。

次の機能は、現時点では削らない。

- Nat・Vec・Finの専用実装：一般のindexed inductiveが同等の例を検査できるまでのbootstrap実装かつ回帰試験である。
- recordの`InductiveDecl`経路：一般帰納型へ進むための、名目的な宣言・constructor・eliminatorの実装基盤である。
- `J`、各eliminator、明示lambda、型注釈などの低水準proof-term API：pattern matching、hole、elaborationが未完成な間のescape hatchである。トップレベル`deppy`は引き続き通常のpreludeとして使え、責務別moduleからも明示的にimportできる。
- 公理依存追跡：将来のVC、solver、ユーザー公理のtrusted boundaryを表示するために必要である。
- 静的module resolver：Pythonを実行せず、入力サイズ、root逸脱、循環importを制限する信頼境界である。

次の分離は、対応する機能を追加するときに行う。

- 最初のsource分類passで、module内の文を`DependentDecl`、`VerifiedDecl`、host Python、importへ分ける。現在の`@dependent` lowererへ`@verified`の意味論を混在させない。
- module処理をsource resolver、module graph、builtin registry、各frontendのlinkerへ分け、`@dependent`と`@verified`で同じ静的graphを共有する。
- Python version指定をfrontend optionへ閉じ込める。複数versionの構文回帰試験は残し、通常のAPIでversion差を過剰に露出しない。
- kernelには定義IDの依存走査を残し、名前と由来を扱うreport層で`UserAxiom`、検査済みVC、未再構成のsolver結果を区別する。

Nat・Vec・Finの専用core項を削除するのは、一般帰納型へのstdlib移行と回帰試験が完了した後である。先にfeature flagや別crateへ分けると、kernel、NbE、elaboratorに二つの経路を維持することになるため行わない。

## 段階的ロードマップ

### Phase 1: `@dependent`を証明支援系として完成させる

1. ユーザー定義帰納型とindexed family
2. positivity、coverage、termination
3. dependent pattern matching
4. holeとgoal表示
5. opaque theoremと検査済みmodule interface
6. 一般帰納型上の標準ライブラリ
7. Nat、Vec、Finの専用実装から標準ライブラリへの段階的移行

受け入れ例は、Rust側に定理固有のprimitiveを加えず、Listの`append_assoc`、`map_identity`、`map_composition`、`reverse_involution`と、Vecの安全な操作を記述・検査できることとする。

### Phase 2: `@verified`とVC generation

1. Verified HIRとその明示的な意味論
2. `requires`、`ensures`
3. 局所代入と`if`
4. `while`、`invariant`、`decreases`
5. WPとVC生成
6. 生成VCを`@dependent`のgoalとして提示

受け入れ例は、loopで書いた加算、乗算、累積和などの部分正当性と停止性を検証できることとする。

### Phase 3: proof-producing bridge

1. VC proofのkernel再検査
2. 検証済み仕様からcore theoremを構築
3. `verified_spec`で後続の証明から再利用
4. 公理依存とtrusted boundaryの表示

この段階で、命令的Pythonの検証結果をdependent theoremとして合成できることを示す。

### Phase 4: 任意の自動化とbackend

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

## 現在地の読み方

この文書は目標設計を含む。現在実装済みの範囲は[README](../README.md)と[PROGRESS](../PROGRESS.md)を正とする。Phase 1は実装済みで、一般帰納型・positivity・依存pattern matching・Listの四定理・holeとgoal表示・opaque theorem・検査済み依存snapshotの再利用に対応する。既存Nat・Vec・Finとruntimeも一般帰納型へ移行した。受理する構文と制約は[実装状況](dependent-phase1.md)に記載する。ループなしの `@verified`、command HIRの純粋な意味論、意味論からのWP/VC構築、手書きVC証明のkernel検査は実装済み。受理範囲と境界は[verifiedガイド](verified.md)に記載する。単一の `while` と不変条件・自然数尺度のVC、有限反復がguard偽で終了することの一般定理も実装済み。`verified_spec` は関数自体を参照するopaque定理をkernelで再検査して公開し、import・再export・公理依存の追跡にも対応する。戻り値専用の `Refined[Nat/Bool, predicate]` と同時代入も実装済みで、Fibonacciループの停止性・再帰的仕様との一致・仕様の再利用を検査できる。一般のrefinement引数・局所型・subtyping、ネストしたwhile、自動証明探索、元のCPythonソースとの意味保存は未実装である。
