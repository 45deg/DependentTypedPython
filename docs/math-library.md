# 数学ライブラリの現状と整備計画

## P0 実装状況

P0 の最初の公開面を stdlib に実装した。基礎型は新しく宣言せず、`deppy.nat.Nat`、
`deppy.data.Decidable`、`deppy.lists.List` を共有する。

- `deppy.equality`: `cong2`、transport の恒等則・合成則。
- `deppy.data` / `deppy.logic`: `Sum` の除去、否定・積・和・含意の決定手続き。
  `deppy.logic` は同じ宣言の再exportであり、別の名目的型を作らない。
- `deppy.nat`: 加算・乗算、加算の結合・交換、乗算の交換・結合・両側の分配、
  後者と等式の消去、加算の左右消去。
- `deppy.nat_order`: `LE`、`LT`、反射・step・推移、透明な `le_decide` / `lt_decide`、
  反対称性、厳密順序の非反射性・推移、加算・乗算の左右の単調性、正の数の前者が減少する `pred_lt`。
- `deppy.lists`: `length`、`Mem`、`NoDup`、`All`、`Any`、`filter`、要素除去、
  map による所属保存、append・map・reverse の長さ、filter の長さと count の一致、
  count の上界、count と reject の分割。既存の append・map・reverse と同じ `List` 上に置く。
- `deppy.fin` / `deppy.vectors`: Fin の自然数変換と上界、Vec の map・append・reverse 後の参照。
- `deppy.finite`: `Enumeration`、列挙順によらない count、全単射による count 保存。
  `proof_case/common.py` は標準の `List`・`Decidable`・`Enumeration` とこれらの証明を再exportする。

公開APIは具体値の正規化、異なるimport経路での名目的同一性、公理依存が空であることを
回帰テストで検査する。空のindexed familyの除去には既存の `absurd(type, value)` を使う。
`LE[S(n), 0]` は除去できるが、未確定の `LE[n, 0]` やinhabitedな添字は拒否する。
この範囲はfrontendとkernelに実装済みであり、順序用の専用規則は追加しない。
新しい順序の証明補題は `@theorem`、判定手続きは `@dependent` とする。
正の数での乗算の消去は未実装。`verified` と単一whileのVC生成・自然数尺度による停止性証明は実装済みで、詳細は[verifiedガイド](verified.md)で扱う。一般の整礎関係による停止性証明は未対応。

以下はstdlibと `lagrange.py`、`fermat.py`、`fermat2.py` の共通化計画。
以下のモジュール名・API名は、実装済みと明記したもの以外は提案である。

最優先は、型の統一、自然数の基本補題、有限列挙と並べ替え、有限和・有限積。
その上に群論を移す。整数論や線形代数を先に広げると、同じ基礎を分野ごとに作り直すことになる。

## 現状から分かったこと

| 領域 | 実装済み | 整備上の問題 |
| --- | --- | --- |
| 等式 | `deppy.equality` の `sym`, `trans`, `cong`, `transport` | 3つの証明例からstdlibを利用。`cong2` はstdlibに実装済み。依存関数向け補題の整備が残る |
| 論理・判定 | `deppy.data` の `Empty`, `Unit`, `Sum`, `Option`, `Not`, `Decidable` | `common.py` は標準型を互換名で再export。例固有の判定補題の移行が残る |
| 自然数 | 公開 `deppy.nat.Nat` と、一般帰納型の例である `deppy.naturals.Nat` | 別の名目的な型。後者の `add` は前者へそのまま適用できない |
| リスト | `deppy.lists` の `List`, `append`, `map`, `reverse` と基本等式 | `common.py` のListは標準型に統一済み。残る例固有の補題を移行する |
| 有限性 | `deppy.finite` の `Enumeration`, `same_count`, `bijection_count` | 標準のListとDecidableを使用。有限述語判定などが残る |
| 有限積 | `proof_case/common.py` の `product`, `same_product`, `bijection_product` | 重複は解消済み。逆元を使わない部分まで `Group` を要求している |
| 群 | `Group`, `Subgroup`, 剰余類、ラグランジュ、有限群の累乗定理 | stdlibでは未提供。判定可能性が `Subgroup` の定義に含まれている |
| 数論・体 | 有限体の非零元の乗法群としてのFermat | `Prime`, 除算・剰余、整数、有限体そのものの構成は未実装 |

証明例の共通定義は `proof_case/common.py` に集約した。stdlibへ移すときには
再exportで同じ型を共有する必要がある。同じ形の帰納型を別々に宣言しても同じ型にはならない。

根拠となる実装:

- [標準の論理データ型](../crates/deppy-python/stdlib/deppy/data.py)
- [標準のリスト](../crates/deppy-python/stdlib/deppy/lists.py)
- [別宣言の自然数](../crates/deppy-python/stdlib/deppy/naturals.py)と[それを使う添字型](../crates/deppy-python/stdlib/deppy/indexed.py)
- [有限列挙と個数保存](../crates/deppy-python/stdlib/deppy/finite.py)、[群・有限積の共有定義](../crates/deppy-python/examples/proof_case/common.py)
- [有限集合の分割・ラグランジュ](../crates/deppy-python/examples/proof_case/lagrange.py)
- [判定可能性・有限積・有限群の累乗](../crates/deppy-python/examples/proof_case/fermat.py)
- [可換群での直接証明](../crates/deppy-python/examples/proof_case/fermat2.py)

## 先に固定する設計

### 基礎型は一系統にする

新しい数学APIは、既存の整数リテラル・`Fin`・`Vec`と接続する公開 `deppy.nat.Nat` を使う。
これは現在すでに一般帰納型のkernel経路を通るので、専用kernelへ戻す方針ではない。
`deppy.naturals` と `deppy.indexed` は当面、一般帰納型の回帰用として分離する。
既存テストを調べずに名前だけ置換したり、削除したりしない。

`List` は `deppy.lists.List`、判定結果は `deppy.data.Decidable` に統一する。
例の `Either` → `Sum`、`Decision` → `Decidable`、`Unit_` → `MkUnit` は、
利用側のimportとconstructorをまとめて移行する。互換名を残すなら別宣言でなく再exportにする。

自然数演算の再帰方向もAPIの一部として扱う。現在の例では `add` は第一引数、
`mul` は第二引数で再帰する。名前を合わせても定義的等しさが変われば `refl` や型検査に影響する。
移行初期はこの計算規則を保ち、変更時は等式補題と移行テストを用意する。

### 計算可能性と数学的な構造を分ける

`Subgroup` の本質は所属述語と閉性であり、一般の部分群が判定可能とは限らない。
基礎の部分群から `decide` を分離し、要素数を数える定理には別引数か
`DecidableSubgroup` のような包装で渡す。既存の例のAPIは移行用adapterで維持できる。

`Enumeration[A]` は単なる「有限であるという主張」ではなく、
重複のない完全な列挙とその証明を持つ計算用データとする。
`fermat.py` はこれから等式の判定を構成しているので、等式判定を独立した公理にしなくてよい。

任意の型上の有限部分集合は、まず重複のないリストで表す。
所属判定・和集合・差集合などには必要な等式判定を明示的に渡す。
全要素を列挙する `Enumeration[A]` と、Aの一部分だけを表す有限集合は別APIにする。

### 証明の等しさを暗黙に仮定しない

現在の述語は `A -> Type` であり、専用の `Prop` や一般的なproof irrelevanceを前提にしない。
`Sigma[A, P]` の二つの値は、第一成分が同じでも第二成分の証拠が異なれば、
自動的に等しいとは扱えない。有限部分集合の個数はまず元のcarrier上の所属判定で数える。

関数・準同型は点ごとの等式、述語は相互含意で比較する。
点ごとの等式から関数自体の `Eq` を得るfunextは、通常の補題として紛れ込ませない。
同様に、同値関係の分割は有限列挙上で扱い、一般の商型を前提にしない。
基礎体系の方針は[設計文書](deppy2.md)と揃える。

### `@theorem` と `@dependent` は公開する挙動で選ぶ

等式・閉性などの証明は原則 `@theorem`。
演算、型族、constructorを返す計算は原則 `@dependent`。
ただし戻り値だけで機械的に分類しない。

例えば現在の `equality_decide`, `all_decide`, `find_removal` にはopaqueなものがある。
証明から使う分には問題ないが、具体値で `Yes` / `No` や除去後の列を正規化したい
ライブラリAPIでは、透明な実装とopaqueな正しさの補題を分けるのが適している。
存在証明の証人や等式証明を計算に使う場合も、展開の必要性を確認する。
既存の「証明が `refl` に正規化する」テストは、公開する計算契約かどうかを先に判断する。

## 優先度の高いモジュール

| 優先度 | モジュール案 | 最初に揃える内容 | 根拠・用途 |
| --- | --- | --- | --- |
| P0 | `deppy.equality` | 既存4補題の共有、`cong2`、必要なtransportの合成則 | ほぼ全ての証明で使う |
| P0 | `deppy.data` / `deppy.logic` | `Decidable` の積・和・否定・含意、決定の正しさ、論理同値 | `decide_pair`, `implication_decide` を移せる |
| P0 | `deppy.nat` / `deppy.nat_order` | 加乗算、0・1・結合・交換・分配、消去、`LE`・`LT`・判定・単調性 | 個数・帰納法・指数の共通基礎 |
| P0 | `deppy.lists` | `length`, `Mem`, `NoDup`, `All`, `Any`, filter、除去、mapとの関係 | 今の `Has`, `NoDup`, `Removal` を共有する |
| P1 | `deppy.functions` | 合成、単射、全射、逆写像付き `Bijection`、恒等・合成・逆 | 全単射の左右逆を毎回引数列で渡している |
| P1 | `deppy.finite` | `Enumeration`、等式判定、列挙に依らない個数、述語の個数、全称・存在判定 | 群論以外の有限数学にもそのまま使える |
| P1 | `deppy.permutations` | リストの並べ替え、所属・NoDup・長さの保存、写像・合成 | `same_count` と `same_product` の構造を共有できる |
| P1 | `deppy.monoids` / `deppy.folds` | Monoid、累乗、順序付きfold、可換な因子の並べ替え、有限和・有限積 | `product` にGroupを要求しなくてよくなる |
| P1 | `deppy.relations` / `deppy.partitions` | 同値関係、判定可能な同値類、分割の個数、等サイズ分割 | `uniform_partition` は群に依存しない |
| P1 | `deppy.groups` | 群、可換性、消去、逆元、準同型、部分群、剰余類 | 現在の証明をほぼそのまま受け入れられる |
| P1 | `deppy.finite_groups` | Lagrange、中心化群、有限群の累乗、必要に応じて元素の位数 | 既存の例の定理を公開APIにする |
| P2 | `deppy.divisibility` / `deppy.number_theory` | 整除、除算・剰余、gcd、素数、互いに素 | 自然数のFermatやEulerへ進むための不足 |
| P2 | `deppy.rings` / `deppy.fields` | 環・体の構造、単元、有限体の非零元の乗法群 | 現状では群と個数の接続を利用者が与えている |
| P2 | `deppy.zmod` | 有限剰余表現、合同、剰余演算の法則、素数法での逆元 | `Prime(p)` から通常の剰余版Fermatへ到達する |

P0は型と基本演算の共通化、P1は既存証明の再利用、P2は新しい数学の構築。
全モジュールを最初から作る意味ではない。中身が小さい間は同居させ、依存が明確になってから分割する。

### 特に一般化する価値がある箇所

`same_count` と `same_product` は、要素を一つ除去して帰納する同じ骨格を持つ。
並べ替えの証拠とfold保存の補題へまとめれば、個数・和・積を同じ枠組みで扱える。
ただし非可換な積は任意の並べ替えで保存されない。全体が可換なMonoidの場合と、
Fermatの例のように積に現れる因子だけが互いに可換な場合を区別する。

累乗はMonoidまで一般化する。逆元を使う消去・負の指数はGroupの層に置く。
まず `Monoid` と `Group` と明示的な変換を用意し、巨大な型クラス階層や暗黙探索を先に作らない。

関係の `EquivalenceRelation` と、二つの型の間の `Bijection` は別名にする。
現在の `Equivalence` は前者なので、名前の衝突を避ける。

`Divisible` は現状の「乗数と等式の証拠」という表現を引き継げる。
ただし将来の `order(a)` は別途、最小の正の周期を構成して正しさを証明する必要がある。
現在の `finite_group_power` はその構成を使わずに証明できている。

## 実装順と完了条件

1. **共通型と等式を一本化する。** examplesの基本型をstdlibへ接続し、例から独自の
   `List`, `Decision`, 等式補題を除けるようにする。異なるimport経路でも同じ型として使えることを検査する。
2. **自然数・リスト・判定を移す。** `length`, `Mem`, `NoDup`, `All`, `count`, 除去と基本算術を移行する。
   具体値の演算・判定の計算と、一般形の補題の両方を確認する。
3. **全単射・並べ替え・有限列挙を整備する。** 列挙順を変えても個数が変わらないこと、
   有限列挙から等式判定を構成できること、有限述語の判定を確認する。
4. **Monoid・fold・Group・分割を移す。** 2通りのFermat証明が同じ `power`・有限積APIを使えるようにする。
   `SameCountAt`, `SameProductAt`, `PartitionAt` など帰納法用の実装補助を通常の利用者から隠す。
5. **大定理を利用例に戻す。** Lagrangeと2通りのFermatをstdlib利用で再検査する。
   stdlibからexamplesへの依存をなくす。2通りのFermatは結論を共有しても、直接証明がLagrange定理に依存しない構造を保つ。
6. **次の到達点を選ぶ。** 通常の数論へ進むなら除算・剰余・素数・ZMod。
   有限組合せ論なら鳩の巣原理・二重計数・群作用。両方の基礎を同時に拡大しない。

公理依存が空であること、誤った等式・不正な列挙・閉性不足を拒否することを回帰条件にする。
計算用APIには具体値の正規化テストを置く。runtimeを公開するAPIでは生成Pythonの検証も別に行う。
検査budgetは明示し、同じ条件で移行前後を比較する。行数減少だけで成功と判断しない。

## 後回しにするものと実装上の制約

実数・解析・位相・測度論・一般の圏論を最初の範囲には入れない。
整数・有理数も、数論や線形代数の到達目標が決まってから追加する。
線形代数へ進む場合は、先に環・体と有限添字・有限和を整備し、行列から始める。

一般の商型、関数外延性、選択原理、proof irrelevanceは「補題の不足」と分けて扱う。
必要になれば基礎体系の選択として明示し、公理依存を追跡する。
一方、有限で判定可能な場合の代表元選択は、具体的な列挙からPythonで構成する余地がある。

当面はType₀のcarrierを対象とする。現状の一般帰納型・等式補題にはuniverse polymorphismがない。
述語をfieldに持つrecordは、現在の `Subgroup` 同様に上位universeが必要になる場合がある。

数学の定義・証明はPythonで実装する。ただし組み込みstdlibとして配布する場合、
[registry](../crates/deppy-python/src/modules/registry.rs)へのモジュール登録は別途必要。
これはimportの配線であり、数学専用のkernel規則を追加することではない。

ライブラリ分割でimport先の公開定義が増えすぎる問題も確認する。
現状は[lowerer](../crates/deppy-python/src/lower.rs)が宣言を公開名へ登録するので、
先頭にunderscoreを付けるだけで非公開になるとは仮定しない。
当面は内部モジュールを分け、必要な名前だけを公開入口で再exportする。
