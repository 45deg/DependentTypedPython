# DepPy

Pythonの構文で記述する依存型言語の実装です。[Chatlog.md](Chatlog.md)を初期設計仕様とし、第19節の実装順序に沿って進めています。今後の二層構成と実装境界は[DepPy2の設計方針](docs/deppy2.md)にまとめています。

Rust製kernel、名前付きASTのelaborator、Ruffを使ったPython frontendと、分離した任意のruntime backendを実装しています。identity・append・get・zero_right・SomeVecの例について、型検査から生成コードの実行まで通ります。対応範囲と残る制約は下記の実行MVPの節に記載しています。

Pythonでの証明項・公理・ライブラリ利用は [証明言語のガイド](docs/proofs.md) を参照してください。`examples/reverse_explicit.py` はRustに補題を追加せず、Pythonのeliminatorとライブラリだけで証明する例です。

## 実行

RustのCargoを使用します。kernelとelaboratorに外部crate依存はありません。Python frontendはRuffのparser・AST・text size crateを `=0.0.12` に固定し、推移的な依存はCargo.lockで固定しています。初回は `cargo fetch --locked` で依存を取得してください。検証環境はRust 1.97.1です。

```sh
cargo test --workspace --offline
cargo run -p deppy-core --example identity --offline
cargo run -p deppy-elab --example implicit_identity --offline
cargo run -p deppy-elab --example nat_add --offline
cargo run -p deppy-elab --example zero_right --offline
cargo run -p deppy-elab --example vectors --offline
cargo run -p deppy-elab --example sigma --offline
cargo run -p deppy-elab --example records --offline
cargo run -p deppy-elab --example structural --offline
cargo run -p deppy-python --example check --locked --offline
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/basics.py
cargo fmt --all -- --check
cargo clippy --workspace --all-targets --offline -- -D warnings
```

進捗と未実装項目は[PROGRESS.md](PROGRESS.md)で管理しています。

## Crate構成

- `crates/deppy-core`：明示的なcore term、kernel、NbE、変換判定、公理依存に加え、kernel検査済みtermからruntime IRへのchecked projectionを提供します。trusted coreの中心です。
- `crates/deppy-elab`：名前付きAST、bidirectional elaboration、meta、定義と再帰の検査を担当します。
- `crates/deppy-python`：Ruffを使ったPython frontend、静的module解決、`@dependent`のloweringを担当します。
- `crates/deppy-runtime`：`deppy-core`が生成したruntime IRを消費し、Pythonコード生成、runtime shim、公開境界wrapperと生成用CLIを提供する任意backendです。型検査と証明の妥当性には必要ありません。

DepPy2では`@dependent`を独立した証明支援系として発展させ、その上にVerified HIRとWP/VC generationを持つ`@verified`層を追加します。生成したVCはdependent coreの証明としてkernelで再検査し、`verified_spec`として後続の証明から再利用します。現行機能と未実装の目標は[設計方針](docs/deppy2.md)で区別しています。

## 現在の実装

`crates/deppy-core`は、完全に明示化したコア項を直接検査するライブラリです。

- 非累積的な具体的universe階層（`Type₀ : Type₁`）とΠ型。
- 型注釈付きλ、適用、型注釈付きlet、de Bruijn indexによる束縛。
- 検査済みの閉じた透明なグローバル定義、定義の参照と展開。
- Nat、Z、S、universe levelとmotiveを明示した依存eliminator。
- Eq、refl、一般の等式消去J（証明にも依存するmotive）。
- Σ、型注釈付きPair、依存するfst・snd射影。
- 一般のindexed inductive、複数constructor、strict positivity、依存eliminatorとNbE。非再帰recordには依存射影を生成。
- Vec・Fin、サイズのwitnessを持つコンストラクタ、依存eliminator、fin0_elim。
- 環境を保持するclosureによるNbE、β・ζ・Nat・Vec・Fin eliminatorとJのι簡約、関数のη変換。
- `Kernel::infer`、`check`、`normalize`、型を指定する`equivalent`。
- 不正なコア入力の拒否と、処理ステップの予算超過時のエラー。

公開APIは閉じた項を受け取ります。正規化・等価性判定も入力を型検査してから評価するため、未検査の自己適用を評価器へ直接渡せません。型の一致はuniverseの持ち上げを行いません。正規化はβ・ζ・ι正規形を返し、ηは等価性判定で扱います。

`Kernel::erase` はkernel検査後に消去対象の変数の実行時使用を検査し、`RuntimeTerm` を生成します。参照するグローバル定義も検査します。このchecked projectionと`RuntimeType`・境界スキーマの導出は現在`deppy-core`にあります。型検査だけを行う`deppy-python`の`check_module`と、この結果を消費してPythonを生成する`deppy-runtime`の`compile_module`は別APIです。エラーはコア項を表示し、frontendは式のsource spanをelaborationへ保持します。import先の診断にもsourceと行・列を付けます。構造的分岐の検査など、式に対応づけられないエラーは宣言単位です。

処理予算は計算回数を制限しますが、再帰的なRust実装に対するスタック・メモリの完全な保護ではありません。universe levelは`u32`で表現し、後続levelを表現できない場合は拒否します。

## Elaboration

`crates/deppy-elab`は、名前付きの`Expr`から完全に明示化したコア項を生成します。`Elaborator::infer`は型を合成し、`check`は期待型から型注釈のないλを検査します。`Expr::app`は先行する暗黙引数を挿入し、`Expr::implicit`で明示指定もできます。

metaは作成時のtelescopeと期待型を保持します。通常引数や期待される戻り値型から制約を解き、occurs checkとscope checkを行います。未解決のmetaは、簡約で使われなくなるものも含めて拒否します。各metaの解と、簡約前の最終コアをkernelで再検査してから`Elaborated { term, ty }`を返します。

この段階の単一化は、metaのtelescopeを相異なるローカル変数で置き換えるpatternに限定しています。解けない制約を保留・探索する機能、metaの引数のpruning、一般の高階単一化はありません。型注釈が不足する場合や、関数型・universeが判定できない場合はエラーになります。引数の型だけから推論した候補のuniverseが不正な場合も、kernelの再検査で拒否します。

elaborator単体の入力はRustで組み立てるASTです。Pythonの解析は別crateの `deppy-python` が担当します。キーワード引数とelaborator内部の詳細なsource spanは未対応です。elaborator内の評価は捕獲を避ける置換と弱頭簡約で実装しており、kernelのclosureベースNbEとは別です。意味値を使ったelaborationへの移行は残っています。

## letとグローバル定義

`Expr::let_in(name, annotation, value, body)` は不変のローカル定義です。注釈は省略でき、期待型はbodyへ伝わります。値は名前の参照時に置換されるため、型の中でも使えます。値自身では新しい束縛を参照できません。未使用の値も検査し、最終コアに型付きλの適用として保持して再検査します。現段階では値の共有を最適化していません。

`Elaborator::define(name, optional_type, body)` は型と本体を検査し、名前と定義IDを登録します。後続の式と関数HIRから `Expr::name(name)` で参照でき、ローカル名が優先されます。コアには `Term::Global(id)` を残し、kernelの評価とelaboratorの単一化で本体を展開します。型の別名にも使えます。

登録は成功時だけ反映され、同名・同IDの置換、自己参照、前方参照を拒否します。グローバル定義のuniverseは具体値で、通常の定義は透明です。公理は型を検査した本体なしの定数として宣言でき、依存する公理を追跡します。`@dependent(opaque=True)` は本体を検査して保持し、変換判定では展開しません。公理依存は本体も走査します。universe parameterは未実装です。IDは環境内の識別子なので、得られた項は同じelaboratorの `kernel()` で検査・正規化してください。

## Python frontend

`deppy-python` はRuffのASTから既存の `Expr`・関数HIR・record宣言を生成し、宣言順にelaboratorで検査・登録します。[Ruffの公開crate](https://docs.rs/crate/ruff_python_parser/0.0.12)は内部APIが不安定なため、parser・AST・text sizeを同時に更新し、受理・拒否テストを通す運用とします。Ruffの型は変換層に閉じ込めています。

- `lower_module(source, Target)`：Python 3.12・3.13・3.14を選び、構文エラーとバージョン制限の両方を検査。各宣言の名前・型・本体・UTF-8 byte rangeを返します。
- `check_module(source, Target)`：新しい環境で全宣言を型検査し、検査済みの定義とelaboratorを返します。失敗時に部分的な環境は返しません。
- CLI：ファイルを読み込み、Python 3.14構文として静的検査します。エラーはファイル名・行・列付きで表示します。

対応するのは裸の `@dependent`、注釈付き位置引数、`[A: Type]` などの暗黙引数、戻り値注釈、不変の単一ローカル代入、最後の `return` です。`from __future__ import annotations` と、対応する `deppy` モジュールからの静的importを要求します。importの別名にも対応します。

トップレベルの `deppy` がpreludeです。通常のコードはここから言語構文、基本型、コンストラクタ、消去子、等式補題をimportします。APIは同時に責務別にも分かれており、`deppy.core` は宣言と関数型、`deppy.nat` は自然数、`deppy.equality` は等式、`deppy.sigma` は依存対、`deppy.fin` は有限添字、`deppy.vectors` はベクタ、`deppy.records` はrecordを公開します。各モジュールはkernel primitiveとPythonで記述した派生定義を区別せず同じ場所から公開します。

```python
from deppy import dependent, Type, Nat, Z, S, Eq, refl, cong, Vec, VNil, VCons
from deppy.vectors import get
```

式は `Type`・`Type[level]`、Nat・Vec・Fin・Eq・Pi・Sigma、コンストラクタ、refl・cong・trans・fin0_elim、Pairとfst/snd、位置引数による適用、角括弧による暗黙引数指定、Natの加算と0〜1024の整数リテラルに対応します。`VNil()` と `VCons(k, head, tail)` の要素型のuniverseは現在Type₀です。`FZ(k)` と `FS(k, pred)` はboundを明示します。例は `crates/deppy-python/examples/basics.py` にあります。

未検査の名前、対応外の自己参照・前方参照、再代入、可変長・デフォルト・キーワード引数、任意の属性アクセス、文字列注釈、未対応の構文は拒否します。Pythonの関数スコープに合わせ、代入前のローカル名をグローバル名として解釈しません。静的なライブラリimportに対応し、ソースを実行せず検査します。引数のない `@dependent` 宣言は型付き定数として扱います。

`@dependent(decreases="parameter")` では、不変のローカル定義列に続く `match` または `return` を関数HIRへ変換します。Natの `Z()` / `S(k)`、Vecの `VNil()` / `VCons(k, head, tail)`、Finの `FZ(k)` / `FS(k, pred)` に対応します。網羅性・添字・直接の部分構造への再帰を既存HIRで検査し、kernelで再検査します。自己呼び出しは関数名による位置引数適用に限定し、暗黙型引数は現在の型引数を補います。例は `crates/deppy-python/examples/structural.py` のadd・appendです。

再帰関数のmotive universeは省略時0で、`@dependent(decreases="n", motive_level=1)` のように具体値を指定できます。guard、Finのbound以外のワイルドカード、キーワードpattern、コンストラクタpatternの入れ子、自己呼び出しの明示的型引数は未対応です。入れ子のmatchは既存HIRの制限に従います。patternのcapture名にもPythonの関数全体のローカルスコープを適用します。`lower_module` の本体は `DeclarationBody::Expression` / `Structural` / `Record` / `Axiom` で区別されます。

`cong(f, proof)` と等式の推移律 `trans(p, q)` はPythonライブラリ `deppy.equality` のJから導いた定義を適用し、`fin0_elim(i)` は戻り値の期待型を使って空のFinを消去します。現在はType₀が対象です。`Eq`・`refl`・`J` も同じ `deppy.equality` から、`Fin`・`FZ`・`FS`・各消去子も `deppy.fin` からimportできます。Fin patternのboundは `FZ(_)` / `FS(_, j)` と省略でき、他の名前を捕捉しない内部名を生成します。`crates/deppy-python/examples/proofs.py` にChatlogのget・zero_right宣言があります。これらの静的検査と生成コアの計算をテストしています。

`@record class SomeVec[T: Type]` は名目的な非再帰recordを宣言します。フィールドには値のない型注釈を使い、先行フィールドは `self.n` のように参照します。`SomeVec[T]` は型、`SomeVec(n, xs)` / `SomeVec[T](n, xs)` はコンストラクタ、`r.n` / `r.value` は生成した射影へ変換します。型名と補助関数を同じelaborator環境に登録します。`CheckedModule.definitions` には関数とrecord型の公開名を返します。

recordのuniverseは省略時0で、`@record(level=1)` のように具体値を指定できます。levelは非負のu32整数リテラルに限定し、型との整合性や後続levelのoverflowはkernelで検査します。`examples/universes.py` に型を保持するrecordと型を返す再帰関数の例があります。継承・メタクラス・メソッド・フィールドのデフォルト値・再帰recordは未対応で、`self`・`fst`・`snd` はフィールド名に使えません。同名フィールドを持つ複数のrecordに対応し、射影は受け手から推論した名目的な型で選びます。受け手の型が不明な場合は推測せず拒否します。`crates/deppy-python/examples/records.py` のSomeVecとΣ型の相互変換、依存する射影を検査・計算しています。生成runtimeではclassではなく、モジュール固有の名目的なタグと不変tupleで表現します。公開コンストラクタ・関数でフィールドと依存する長さを検査します。

再帰分岐の `return` 前では、`previous: Nat = count(k)` のように再帰結果を保持できます。既存のlet検査へ変換し、依存型と期待型を保ちます。未使用の不正な値も拒否します。再帰先を別名に置き換えることは認めず、直接の部分構造だけを許す停止性検査を維持します。`crates/deppy-python/examples/branch_fields.py` は分岐内letと同名フィールド・連続する射影の例です。

`match` 前の代入・値付き型注釈にも対応します。定義を分岐前の文脈で検査し、分岐内では絞り込んだ引数に合わせて定義を再展開します。`saved: Vec[T, n] = xs` や等式の証拠を保持でき、既存の入れ子のFin分岐にも対応します。元の定義も検査対象に残すため、未使用の不正な定義は拒否します。例は `crates/deppy-python/examples/before_match.py` です。patternで既存のローカル名・グローバル名を隠すことはできません。この変換は計算の共有を保証しません。受理する本体は純粋な計算に限定し、生成runtimeで結果の一致を検証しています。

通常の未装飾関数とモジュール内のassertは解析のみで、型検査・実行・証明としての利用はしません。コンパイラはユーザーモジュールや注釈を実行しません。生成物には検査済み宣言だけが含まれます。Ruffの解析とCPythonのcompile検証は別です。意味保存は対象fixtureの差分実行で検証しており、一般的な形式証明は行っていません。

fixtureのCPythonコンパイル検証は `uv run --no-project --offline --python 3.14 scripts/check_python_syntax.py` で再現できます（対応するPythonがインストール済みであること）。3.12.0と3.14.3で成功しました。CPython 3.13は未検証です。

## Natと加算

コアの`Term::Nat`、`Zero`、`Succ`はそれぞれNat、Z、Sを表します。`Term::NatElim`は次の型を検査します。`level`は具体的なuniverse levelで、すべての引数を明示します。

```text
P    : Nat → Type[level]
zero : P Z
step : Π (k : Nat). P k → P (S k)
n    : Nat
──────────────────────────────────
NatElim(level, P, zero, step, n) : P n
```

Zではzeroへ、S(k)では`step k (NatElim ... k)`へ簡約します。変数などのneutralな対象ではeliminatorを保持します。どちらの分岐もkernelで検査し、Natにη規則や一般再帰を追加しません。

名前付きASTでも`Expr::Nat`、`Zero`、`succ()`、`nat_elim(...)`を使用できます。`prelude::nat_add()`は第1引数について再帰する加算のASTを返します。専用の加算primitiveや公理は使わず、通常のelaborationとkernel検査を通します。

`add Z m ≡ m`と`add (S k) m ≡ S (add k m)`は定義的等式です。変数nについて`add n Z ≡ n`とは判定しません。この等式は、EqとNatの帰納法で証明します。Python frontendでも整数・`+`・対応する`match`を読み取れます。

## 等式と帰納法による証明

`Expr::eq(A, x, y)`で等式型、`x.refl()`で反射律を表します。`refl`のcarrierは引数から推論し、期待型がEqの場合はそのcarrierで引数を検査して両辺との定義的等しさを確認します。コアの`Term::Refl`はcarrierも明示します。

`Expr::j(level, A, x, C, d, y, p)`とコアの`Term::J`は次を検査します。

```text
A : Type[u]    x, y : A    p : Eq A x y
C : (z : A) → Eq A x z → Type[level]
d : C x (refl x)
────────────────────────────────────────
J(level, A, x, C, d, y, p) : C y p
```

証明が`refl`ならdへ簡約し、neutralな証明ではJを保持します。motiveやbaseも簡約前に検査します。等式の証明から定義的等しさを導く規則、proof irrelevance、UIP・Kなどの公理は追加していません。

`prelude::cong(u, v)`と`prelude::transport(u, v)`はJから定義したASTを返します。universeは呼び出し時に具体的なlevelを指定します。runtimeのJは証明トークンを確認してbaseを返します。証明引数まで消去する一般のtransport最適化は行いません。

`prelude::zero_right()`は`(n : Nat) → Eq Nat (add n Z) n`をNat eliminatorで証明します。Zの分岐は`refl Z`、Sの分岐は`cong S ih`です。実行例は一般形をkernelで検査し、`zero_right(2)`が`refl(2)`に正規化されることも確認します。Python frontendでもこの証明例を検査できます。

## Vec・Finと安全な要素取得

`Vec A n : Type[u]`（`A : Type[u]`）、`Fin n : Type[0]`を固定の帰納型として扱います。名前付きASTには`Expr::vec`、`vnil`、`vcons`、`fin`、`fz`、`fs`があります。コンストラクタは次の明示的な引数を持ちます。

```text
VNil(A)              : Vec A Z
VCons(A, k, h, tail)  : Vec A (S k)    h : A, tail : Vec A k
FZ(k)                : Fin (S k)
FS(k, j)             : Fin (S k)      j : Fin k
```

`VCons`の長さはtailの長さ、`FZ`・`FS`のboundは結果の上限の前段です。kernelはこれらのwitnessとフィールドの型を照合します。`Fin Z`を構築するコンストラクタはありません。`Expr::fin0_elim(A, i)`は`i : Fin Z`からAの項を得る消去で、通常のFZやFSを渡すと拒否します。変数などのneutralなiは、そのまま消去項に保持します。

依存eliminatorには、結果のuniverse level、motive、両分岐、添字、分解対象を明示します。Vecではcarrierも指定します。

```text
VecElim(level, A, P, nil, cons, n, xs) : P n xs
  P    : (k : Nat) → Vec A k → Type[level]
  nil  : P Z (VNil A)
  cons : (k : Nat) → (h : A) → (t : Vec A k) →
         P k t → P (S k) (VCons A k h t)

FinElim(level, P, zero, step, n, i) : P n i
  P    : (k : Nat) → Fin k → Type[level]
  zero : (k : Nat) → P (S k) (FZ k)
  step : (k : Nat) → (j : Fin k) → P k j → P (S k) (FS k j)
```

再帰はtailまたはFSの前段だけに進み、neutralな対象では消去項を保持します。elaboratorはmotiveと分岐の期待型から、λの型注釈を補えます。通常の暗黙引数推論では、Vecからcarrier・長さ、Finから上限を推論できます。直接のコンストラクタASTではcarrierを明示します。

`prelude::vec_append(level)`と`prelude::vec_get(level)`は、追加の公理や専用primitiveを使わずeliminatorから定義したASTです。

```text
append : {A : Type[level]} → (n m : Nat) → Vec A n → Vec A m → Vec A (add n m)
get    : {A : Type[level]} → (n : Nat) → Vec A n → Fin n → A
```

getのVec motiveは`P k xs = Fin k → A`です。空の分岐にはfin0_elimを使い、VConsの分岐ではFinElimから導いたcase splitで先頭と再帰呼び出しを選びます。型レベルのNat eliminatorで分岐関数の型を作るため、添字の強制変換は不要です。実行例は`[1] ++ [0] = [1, 0]`と、その2番目の値が0であることをkernelの正規化で確認します。

これらは固定された型と明示的なeliminatorの実装です。一般のユーザー定義帰納型とpositivity checkingは別途追加済みです。対応する構文と分岐の制約は[Phase 1の実装状況](docs/dependent-phase1.md)を参照してください。生成runtimeのVecは不変tupleで、境界で長さと既知の要素型を検査します。

## reverseとmirrorの参照等式

`crates/deppy-python/stdlib/deppy/vectors.py` に末尾追加 `snoc`、`reverse`、`mirror` と参照補題があります。`crates/deppy-python/examples/reverse.py` はこれらをimportして次の証明を定義します。

```python
@dependent(decreases="xs")
def reverse_get[T: Type](n: Nat, xs: Vec[T, n], i: Fin[n]) -> Eq[
    T, get(n, reverse(n, xs), mirror(n, i)), get(n, xs, i),
]:
    ...
```

実装はVecの構造的帰納法です。空のVecでは `fin0_elim`、先頭では末尾追加した要素を参照する補題、後続では末尾追加が既存の要素を保つ補題と帰納法の仮定を `trans` でつなぎます。公理や新しいkernel primitiveは追加していません。

```sh
cargo run -p deppy-python --locked --offline -- crates/deppy-python/examples/reverse.py
cargo test -p deppy-python --locked --offline --test reverse
```

Python frontendのelaboration・kernel検査予算は、依存するFin motiveと証明の合成を扱うため1,000,000ステップに設定しています。有限の具体例だけでなく宣言の一般形を型検査し、テストでは具体的な証明の `refl` への正規化、誤った証明の拒否、生成Pythonでの実行も確認します。

## 依存対

`Expr::sigma("n", Expr::Nat, Expr::vec(Expr::Nat, Expr::name("n")))`で、長さとベクタの依存対型を表せます。`Expr::pair(n, xs)`は期待されるΣ型を使って検査します。単独のPairから型族を推論することはせず、`Elaborator::check`または`.ann(...)`で型を与えます。

```text
Σ (x : A). B x : Type[max(u,v)]   (A : Type[u], B x : Type[v])
p.fst : A
p.snd : B p.fst
(Pair a b).fst ≡ a
(Pair a b).snd ≡ b
```

コアの`Pair { ty, fst, snd }`はΣ型の注釈を保持し、射影で捨てられる成分もkernelで検査します。Σの一般的なη規則は採用しません。`sigma`実行例は一般の`pack`を検査し、`Pair(1, [1])`の両射影と第2成分の型を正規化で確認します。Python frontendはSigma・Pair・fst/sndにも対応しています。

## Dependent record

`Elaborator::declare_record(id, RecordDecl { parameters, fields, level })`で、名前付きのパラメータ列とフィールド列を登録できます。型は先行する名前を参照でき、フィールドは宣言順に検査されます。パラメータは暗黙引数、フィールドは明示的な引数です。次の宣言が`SomeVec`に相当します。

```rust
RecordDecl {
    parameters: vec![("T".into(), Expr::Universe(0))],
    fields: vec![
        ("n".into(), Expr::Nat),
        ("value".into(), Expr::vec(Expr::name("T"), Expr::name("n"))),
    ],
    level: 0,
}
```

返された`Record`から`ty()`、`constructor()`、`projection("value")`などの関数式を取得します。型引数の明示指定には`.implicit(...)`を使います。コンストラクタ・射影の適用では、通常の暗黙引数推論を利用できます。型検査・正規化には、宣言を保持する同じ`elaborator.kernel()`を使います。

コアは`InductiveDecl`を検査してから登録し、`Inductive`・`Constructor`・`Elim`で表します。宣言IDはkernelの環境内で一意で、登録後の置換・変更APIはありません。同じフィールド構成でも別IDの型は区別し、Σとの変換も明示します。各フィールドのuniverseは宣言したlevel以下に制限します。自己参照・前方参照、範囲外の変数、重複名、不正な型は拒否します。射影は依存eliminatorから生成し、record専用primitiveや一般的なη規則は追加しません。

名前付きASTの `expr.field("field_name")` は、受け手を一度型推論し、その名目的なrecord IDに登録された射影を選びます。推論済みの型引数と受け手を、既存の生成済み射影へ適用します。新しいコアprimitiveは追加せず、依存する結果型もkernelで再検査します。型の別名、let、連続する射影、関数HIRにも対応します。未知のフィールドや不明な受け手の型は拒否します。

`Expr::Core`は閉じたコア項の埋め込みです。入力をkernelで検査してからelaboratorに取り込み、最終結果も再検査します。`records`実行例では、第17.5節の`pack`・`as_record`・`as_pair`を名前付きASTで検査し、値を正規化して確認します。Pythonの`@record`にも接続しています。runtimeはタグ付き不変tupleを使います。再帰型は一般の`@inductive`で宣言できます。`@record`は非再帰のままです。

## 分岐と構造的再帰の変換

`lower::Function`は、パラメータ列・戻り値型・`decreases`・具体的な`motive_level`・本体を持つ関数HIRです。`Body::Let { name, ty, value, body }`で不変のローカル定義を置き、`Body::Match`の各`Arm`に`Pattern`と本体を記述し、`Expr::Recur(arguments)`で自己呼び出しを表します。自己呼び出しの引数列には、暗黙パラメータを含む全引数を宣言順に渡します。

`Elaborator::compile_function`はmotiveと帰納法の仮定を生成し、関数全体を元の型に照らしてelaborateした後、kernelで再検査します。`lower_function`は変換した注釈付きASTだけを返すため、それだけでは型検査済みではありません。例として`prelude::structural::{add, append, get, zero_right, fin_rank}`を用意しています。

- 外側の分岐は`decreases`で指定した`Nat`・`Vec`・`Fin`引数を分解し、両コンストラクタを一度ずつ網羅します。
- 再帰先は直前に分解したコンストラクタの直接の部分構造に限定します。Vec・Finの再帰では添字もそのwitnessに一致させます。
- 分解対象より前の引数は、添字以外を固定します。後続の引数はmotiveに一般化し、再帰時に変更できます。`get`では`Fin n → A`というmotiveを生成します。
- 入れ子の分岐は、唯一の後続引数が`Fin (S k)`で、戻り値型がそのindex値に依存するケースにも対応します。依存する分岐は型レベルのNat motiveで型族も一般化し、添字の強制変換なしに導きます。空の分岐では明示的な`fin0_elim`を使います。

対応範囲外の型の別名や添字式、固定した前方引数の添字依存、pattern名による既存のローカル名・グローバル名の隠蔽、さらに深い分岐は拒否します。`motive_level`は後続引数を含むmotiveの結果universeで、間違った値はkernel検査を通りません。全域性の検査を無効化する設定、一般再帰・相互再帰・Eqのpattern matchingはありません。

このHIRはプログラムからの構築に加え、上記のPython frontendからも生成します。

## 実行MVP

`deppy-runtime`の`compile_module(source, Target)`または生成用CLIで、外部パッケージ不要のPythonモジュールを生成します。

```sh
cargo run -p deppy-runtime --locked --offline -- crates/deppy-python/examples/proofs.py > /tmp/deppy_proofs.py
uv run --no-project --offline --python 3.12 python -c "import runpy; f = runpy.run_path('/tmp/deppy_proofs.py')['exports']; print(f['get'](3, (10, 20, 30), (3, 1))); print(f['zero_right'](3))"
```

出力は `20` と `None` です。名前の衝突を防ぐため、公開宣言は `exports['名前']` から呼び出します。型の暗黙引数は渡しません。record宣言の名前はコンストラクタになります。

| コアの値 | Python表現 |
| --- | --- |
| Nat | 非負のint（boolは拒否） |
| Vec | 要素の不変tuple |
| Fin | `(上限, 0始まりの位置)` |
| Sigma | `(第1成分, 第2成分)` |
| record | モジュール固有タグとフィールドtuple。`exports` のコンストラクタで生成 |
| 型 | `None` |
| 等式の証明 | 内部ではpayloadなしのトークン、公開結果では `None` |

公開関数は引数・結果のスキーマを検査し、不変の値を再構築します。Vecの長さ、Finの上限、Sigma・recordの依存フィールドを検査し、リストなどの可変値、偽造した添字・異なるrecordのタグを拒否します。消去した型パラメータの要素はopaqueな不変データとして扱い、元の具体的なPythonクラスを検証する仕組みではありません。既知の `Vec[Nat, n]` なら各要素のNatも検査します。

これは既存例を実行できるMVPです。次は対応範囲外です。

- 外部Pythonからの証明入力。内部の証明トークンを渡しても拒否します。`Proof[...]` の構文は未実装です。証明結果と実行時使用のない証明letの計算は消去します。消去条件と残る制約は [証明の消去](docs/proofs.md#証明の消去) を参照してください。
- 高階関数・任意の型族を公開境界で検証すること。消去した値添字が境界のサイズ検査に必要な場合も、コンパイル時に拒否します。
- 一般Pythonとの混在コンパイル、ソース互換のruntime class。検査済みモジュールはソースを静的に読み込み、同じkernel環境で再検査します。
- 深い項や大きな再帰に対するスタック・メモリ保証。recursor自体はループを使いますが、生成closureの呼び出しにはPythonのスタック上限があります。Rustの再帰的な検査にもスタック制約があります。

検証は `cargo test --workspace --locked --offline` と、次の差分実行で再現できます。Rustのruntime統合テストには `python3` が必要です。

```sh
uv run --no-project --offline --python 3.12 scripts/check_python_runtime.py
uv run --no-project --offline --python 3.14 scripts/check_python_runtime.py
```

Python 3.12.0・3.14.3で各244ケースが一致しました。比較するのはリポジトリの5fixtureです。ソース側にはテスト専用の `scripts/reference_deppy.py` を使います。この参照モデルは型検査器・証明検査器ではありません。

残る拡張はuniverse polymorphism、CPython 3.13の実行検証、一般のpattern matrix、検査済みinterfaceを使うlinking、一般帰納型のruntime移行などです。これらを既存例の実行MVPの完了条件には含めません。未対応の構文や未解決の穴を公理として受理する機能は設けません。


## 証明の作成途中の解析

`hole("名前")` は期待型のある位置で使えます。`analyze_module` はgoalの期待型、局所変数・局所定義、式のsource spanを返します。未完成の宣言は登録せず、依存する宣言はエラーになります。解析中に独立した通常の関数宣言の検査は続けます。構文エラーやrecord・公理の宣言エラーでは解析を終了します。

```sh
cargo run -p deppy-python --locked --offline -- --goals proof.py
cargo run -p deppy-python --locked --offline -- --json proof.py
```

holeや診断が残る場合、CLIは非ゼロ終了し、`Analysis.checked` は `None` です。`check_module` は引き続き未完成のmoduleを拒否します。

`FrontendOptions` でPython target、loweringとelaborationの処理予算を指定できます。`CheckedModule.interface` は公開名・型・宣言種別・record constructor・公理依存を、検査時のkernel snapshotとともに提供します。保存済みinterfaceの読み込みや検査省略は行いません。

Phase 1全体の完成状況と残件は [実装状況](docs/dependent-phase1.md) を参照してください。

一般帰納型の標準ライブラリとして`deppy.data`、`deppy.lists`、`deppy.naturals`、`deppy.indexed`を追加しています。Listの四定理と一般Natを添字にした安全なgetを、公理なしで検査できます。既存API・証明群・runtimeの移行は未完了であり、専用Nat・Vec・Fin coreは保持しています。構文と残件は[Phase 1の実装状況](docs/dependent-phase1.md)を参照してください。
