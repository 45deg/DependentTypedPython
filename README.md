# DepPy

Pythonの構文で記述する依存型言語の実装です。[Chatlog.md](Chatlog.md)を設計仕様とし、第19節の実装順序に沿って進めています。

現在はRust製kernel、名前付きASTのelaborator、Ruffを使ったPython frontendを実装しています。Pythonソースの非再帰関数と、対応する構造的再帰関数を静的に型検査できます。Python実行・コード生成と、第17節の例全体への対応は未実装です。

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

## 現在の実装

`crates/deppy-core`は、完全に明示化したコア項を直接検査するライブラリです。

- 非累積的な具体的universe階層（`Type₀ : Type₁`）とΠ型。
- 型注釈付きλ、適用、型注釈付きlet、de Bruijn indexによる束縛。
- 検査済みの閉じた透明なグローバル定義、定義の参照と展開。
- Nat、Z、S、universe levelとmotiveを明示した依存eliminator。
- Eq、refl、一般の等式消去J（証明にも依存するmotive）。
- Σ、型注釈付きPair、依存するfst・snd射影。
- 非再帰・単一コンストラクタの名目的帰納型、依存eliminator、そこから生成する射影。
- Vec・Fin、サイズのwitnessを持つコンストラクタ、依存eliminator、fin0_elim。
- 環境を保持するclosureによるNbE、β・ζ・Nat・Vec・Fin eliminatorとJのι簡約、関数のη変換。
- `Kernel::infer`、`check`、`normalize`、型を指定する`equivalent`。
- 不正なコア入力の拒否と、処理ステップの予算超過時のエラー。

公開APIは閉じた項を受け取ります。正規化・等価性判定も入力を型検査してから評価するため、未検査の自己適用を評価器へ直接渡せません。型の一致はuniverseの持ち上げを行いません。正規化はβ・ζ・ι正規形を返し、ηは等価性判定で扱います。

`Relevance::Erased`は現時点では束縛と型に保持する情報です。実行時使用の検査と消去は未実装であり、kernelの受理だけでは消去やPython実行の安全性を保証しません。エラーはコア項を表示し、frontendは構文・名前解決のエラーを元のソース範囲に、elaborationのエラーを関数宣言の範囲に対応させます。

処理予算は計算回数を制限しますが、再帰的なRust実装に対するスタック・メモリの完全な保護ではありません。universe levelは`u32`で表現し、後続levelを表現できない場合は拒否します。

## Elaboration

`crates/deppy-elab`は、名前付きの`Expr`から完全に明示化したコア項を生成します。`Elaborator::infer`は型を合成し、`check`は期待型から型注釈のないλを検査します。`Expr::app`は先行する暗黙引数を挿入し、`Expr::implicit`で明示指定もできます。

metaは作成時のtelescopeと期待型を保持します。通常引数や期待される戻り値型から制約を解き、occurs checkとscope checkを行います。未解決のmetaは、簡約で使われなくなるものも含めて拒否します。各metaの解と、簡約前の最終コアをkernelで再検査してから`Elaborated { term, ty }`を返します。

この段階の単一化は、metaのtelescopeを相異なるローカル変数で置き換えるpatternに限定しています。解けない制約を保留・探索する機能、metaの引数のpruning、一般の高階単一化はありません。型注釈が不足する場合や、関数型・universeが判定できない場合はエラーになります。引数の型だけから推論した候補のuniverseが不正な場合も、kernelの再検査で拒否します。

elaborator単体の入力はRustで組み立てるASTです。Pythonの解析は別crateの `deppy-python` が担当します。キーワード引数とelaborator内部の詳細なsource spanは未対応です。elaborator内の評価は捕獲を避ける置換と弱頭簡約で実装しており、kernelのclosureベースNbEとは別です。意味値を使ったelaborationへの移行は残っています。

## letとグローバル定義

`Expr::let_in(name, annotation, value, body)` は不変のローカル定義です。注釈は省略でき、期待型はbodyへ伝わります。値は名前の参照時に置換されるため、型の中でも使えます。値自身では新しい束縛を参照できません。未使用の値も検査し、最終コアに型付きλの適用として保持して再検査します。現段階では値の共有を最適化していません。

`Elaborator::define(name, optional_type, body)` は型と本体を検査し、名前と定義IDを登録します。後続の式と関数HIRから `Expr::name(name)` で参照でき、ローカル名が優先されます。コアには `Term::Global(id)` を残し、kernelの評価とelaboratorの単一化で本体を展開します。型の別名にも使えます。

登録は成功時だけ反映され、同名・同IDの置換、自己参照、前方参照を拒否します。グローバル定義のuniverseは具体値で、現在は透明な定義のみ対応します。不透明な定義・公理・universe parameter・モジュール間インターフェースは未実装です。IDは環境内の識別子なので、得られた項は同じelaboratorの `kernel()` で検査・正規化してください。

## Python frontend

`deppy-python` はRuffのASTから既存の `Expr`・関数HIR・record宣言を生成し、宣言順にelaboratorで検査・登録します。[Ruffの公開crate](https://docs.rs/crate/ruff_python_parser/0.0.12)は内部APIが不安定なため、parser・AST・text sizeを同時に更新し、受理・拒否テストを通す運用とします。Ruffの型は変換層に閉じ込めています。

- `lower_module(source, Target)`：Python 3.12・3.13・3.14を選び、構文エラーとバージョン制限の両方を検査。各宣言の名前・型・本体・UTF-8 byte rangeを返します。
- `check_module(source, Target)`：新しい環境で全宣言を型検査し、検査済みの定義とelaboratorを返します。失敗時に部分的な環境は返しません。
- CLI：ファイルを読み込み、Python 3.14構文として静的検査します。エラーはファイル名・行・列付きで表示します。

対応するのは裸の `@dependent`、注釈付き位置引数、`[A: Type]` などの暗黙引数、戻り値注釈、不変の単一ローカル代入、最後の `return` です。`from __future__ import annotations` と、対応APIの `from deppy import ...` を要求します。importの別名にも対応します。

式は `Type`・`Type[level]`、Nat・Vec・Fin・Eq・Pi・Sigma、コンストラクタ、refl・cong・fin0_elim、Pairとfst/snd、位置引数による適用、角括弧による暗黙引数指定、Natの加算と0〜1024の整数リテラルに対応します。`VNil()` と `VCons(k, head, tail)` の要素型のuniverseは現在Type₀です。`FZ(k)` と `FS(k, pred)` はboundを明示します。例は `crates/deppy-python/examples/basics.py` にあります。

未検査の名前、対応外の自己参照・前方参照、再代入、可変長・デフォルト・キーワード引数、引数のない関数、任意の属性アクセス、文字列注釈、未対応の構文は拒否します。Pythonの関数スコープに合わせ、代入前のローカル名をグローバル名として解釈しません。外部モジュールの静的importは未対応です。

`@dependent(decreases="parameter")` では、単一の `match`、または不変のローカル定義列に続く `return` を関数HIRへ変換します。Natの `Z()` / `S(k)`、Vecの `VNil()` / `VCons(k, head, tail)`、Finの `FZ(k)` / `FS(k, pred)` に対応します。網羅性・添字・直接の部分構造への再帰を既存HIRで検査し、kernelで再検査します。自己呼び出しは関数名による位置引数適用に限定し、暗黙型引数は現在の型引数を補います。例は `crates/deppy-python/examples/structural.py` のadd・appendです。

再帰関数のmotive universeは省略時0で、`@dependent(decreases="n", motive_level=1)` のように具体値を指定できます。`match` の前に置くローカル定義、guard、Finのbound以外のワイルドカード、キーワードpattern、コンストラクタpatternの入れ子、自己呼び出しの明示的型引数は未対応です。入れ子のmatchは既存HIRの制限に従います。patternのcapture名にもPythonの関数全体のローカルスコープを適用します。`lower_module` の本体は `DeclarationBody::Expression` / `Structural` / `Record` で区別されます。

`cong(f, proof)` はJから導いた定義を適用し、`fin0_elim(i)` は戻り値の期待型を使って空のFinを消去します。現在はType₀が対象です。Fin patternのboundは `FZ(_)` / `FS(_, j)` と省略でき、他の名前を捕捉しない内部名を生成します。`crates/deppy-python/examples/proofs.py` にChatlogのget・zero_right宣言があります。これらの静的検査と生成コアの計算をテストしています。

`@record class SomeVec[T: Type]` は名目的な非再帰recordを宣言します。フィールドには値のない型注釈を使い、先行フィールドは `self.n` のように参照します。`SomeVec[T]` は型、`SomeVec(n, xs)` / `SomeVec[T](n, xs)` はコンストラクタ、`r.n` / `r.value` は生成した射影へ変換します。型名と補助関数を同じelaborator環境に登録します。`CheckedModule.definitions` には関数とrecord型の公開名を返します。

recordのuniverseは省略時0で、`@record(level=1)` のように具体値を指定できます。levelは非負のu32整数リテラルに限定し、型との整合性や後続levelのoverflowはkernelで検査します。`examples/universes.py` に型を保持するrecordと型を返す再帰関数の例があります。継承・メタクラス・メソッド・フィールドのデフォルト値・再帰recordは未対応で、`self`・`fst`・`snd` はフィールド名に使えません。同名フィールドを持つ複数のrecordに対応し、射影は受け手から推論した名目的な型で選びます。受け手の型が不明な場合は推測せず拒否します。`crates/deppy-python/examples/records.py` のSomeVecとΣ型の相互変換、依存する射影を検査・計算しています。Python runtimeのclass生成や不変性の保証は未実装です。

再帰分岐の `return` 前では、`previous: Nat = count(k)` のように再帰結果を保持できます。既存のlet検査へ変換し、依存型と期待型を保ちます。未使用の不正な値も拒否します。再帰先を別名に置き換えることは認めず、直接の部分構造だけを許す停止性検査を維持します。`crates/deppy-python/examples/branch_fields.py` は分岐内letと同名フィールド・連続する射影の例です。

通常の未装飾関数とモジュール内のassertは解析のみで、型検査・実行・証明としての利用はしません。ユーザーモジュールや注釈を実行する経路はありません。Ruffの解析はCPythonのcompile検証とは別で、消去やPython実行時の意味保存も保証しません。

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

`prelude::cong(u, v)`と`prelude::transport(u, v)`はJから定義したASTを返します。universeは呼び出し時に具体的なlevelを指定します。transportは型検査と論理的な計算規則に対応し、runtime representationの検査・消去は未実装です。

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

これらは固定された型と明示的なeliminatorの実装です。ユーザー定義帰納型の宣言検査・positivity checking、対応範囲外のPython pattern、実行時のベクタ表現・境界検証は未実装です。

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

`Expr::Core`は閉じたコア項の埋め込みです。入力をkernelで検査してからelaboratorに取り込み、最終結果も再検査します。`records`実行例では、第17.5節の`pack`・`as_record`・`as_pair`を名前付きASTで検査し、値を正規化して確認します。Pythonの`@record`にも接続しています。runtime class・不変性の実装、一般の帰納型や再帰・positivity checkingは未実装です。

## 分岐と構造的再帰の変換

`lower::Function`は、パラメータ列・戻り値型・`decreases`・具体的な`motive_level`・本体を持つ関数HIRです。`Body::Match`の各`Arm`に`Pattern`と本体を記述し、`Expr::Recur(arguments)`で自己呼び出しを表します。自己呼び出しの引数列には、暗黙パラメータを含む全引数を宣言順に渡します。

`Elaborator::compile_function`はmotiveと帰納法の仮定を生成し、関数全体を元の型に照らしてelaborateした後、kernelで再検査します。`lower_function`は変換した注釈付きASTだけを返すため、それだけでは型検査済みではありません。例として`prelude::structural::{add, append, get, zero_right, fin_rank}`を用意しています。

- 外側の分岐は`decreases`で指定した`Nat`・`Vec`・`Fin`引数を分解し、両コンストラクタを一度ずつ網羅します。
- 再帰先は直前に分解したコンストラクタの直接の部分構造に限定します。Vec・Finの再帰では添字もそのwitnessに一致させます。
- 分解対象より前の引数は、添字以外を固定します。後続の引数はmotiveに一般化し、再帰時に変更できます。`get`では`Fin n → A`というmotiveを生成します。
- 入れ子の分岐は、唯一の後続引数が`Fin (S k)`で、戻り値型がそのindex値に依存しないケースに対応します。`get`の`FZ`・`FS`分岐はこの範囲です。空の分岐では明示的な`fin0_elim`を使います。

対応範囲外の型の別名や添字式、固定した前方引数の添字依存、pattern名による関数引数の隠蔽、さらに深い分岐は拒否します。`motive_level`は後続引数を含むmotiveの結果universeで、間違った値はkernel検査を通りません。全域性の検査を無効化する設定、一般再帰・相互再帰・Eqのpattern matchingはありません。

このHIRはプログラムからの構築に加え、上記のPython frontendからも生成します。

## 次の実装段階

1. frontendのuniverse指定と、`match` の前に置くローカル定義への対応を追加。
2. CPython 3.13のcompile検証、モジュール間の静的importと検査済みインターフェース、詳細な型エラー位置を追加。
3. 使用検査、消去、境界の検証・再構築、Pythonコード生成と差分実行テスト。

第17節の5例を検査・実行できることがMVPの到達条件です。未実装の構文や穴を公理・`Any`として受理する機能は設けません。
