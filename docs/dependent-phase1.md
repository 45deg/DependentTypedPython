# 一般帰納型と依存pattern matching

Phase 1の実装を完了した。一般帰納型、依存pattern matching、検査済み依存の再利用、stdlibとruntimeの移行を実装し、Nat・Vec・Finの専用core項・型規則・評価規則を削除した。Listの四定理とVecの安全な参照を、定理固有のprimitiveや追加の公理なしで検査できる。受理する構文と境界の制約は以下に記載する。

## 実装済みの基盤

- 式のsource identity・spanをPythonからelaborationと構造的loweringへ伝播。
- 診断の種別、source、行・列、関連する宣言位置、型照合の期待型・実際の型。型の形のエラーとreflの不一致にも型情報を付ける。
- 重複・型違いのpatternはそのpattern、非網羅の分岐はそのmatchを診断位置にする。入れ子・import先のsourceを保持する。
- resolver・builtin registry・module graph・dependent linkerの分離、`FrontendOptions`。
- 名前付きholeと局所文脈付きgoal、`analyze_module`、`--goals`、`--json`。goal IDは解析全体で一意にする。
- opaqueな検査済み定義と、公理を区別した依存追跡。
- kernel snapshotに結びついた読み取り専用interface。一般帰納型・constructorの宣言種別と、parameter/index telescope・constructor metadataを公開する。
- 公開import aliasをcanonicalな検査済みIDへ対応付け、record射影も同じinterface snapshotで公開する。
- `CheckSession::check`は依存sourceと検査optionsが同じ場合、検査済み依存snapshotを再利用する。rootは毎回検査し、依存source変更時には無効化する。失敗した検査でcacheを更新しない。sourceの解決・解析とloweringは毎回行う。

未完成の宣言は環境に登録されない。独立した通常関数の解析は続け、依存する宣言は未解決名として診断する。診断があるmoduleは未検証として返す。構文・公理・record・帰納型宣言のエラーでは収集を打ち切る。

## 一般帰納型

kernelの`DataDecl`はparameter telescope、index telescope、複数constructor、具体的universeを持つ。各constructorはfield telescopeと戻り先の添字を宣言する。型・constructor・eliminatorをkernelで検査し、直接再帰とΠ型の正位置に対する帰納法仮定を生成する。NbEとelaboratorの簡約は同じconstructor計算規則に従う。neutralな消去も保持する。

登録は型名と全constructorを含めて原子的に行う。負位置・二重負位置、再帰時のparameter変更、戻り先添字の自己参照、自己eliminatorを使うconstructor型を拒否する。型別名を展開した後もpositivityを検査する。既存の型作用素の引数に帰納型を入れるnested recursion、相互再帰、universe polymorphismは未対応。

Pythonでは次のように宣言する。

```python
from __future__ import annotations
from deppy import inductive, constructor, dependent, Type

@inductive
class List[A: Type]:
    @constructor
    def Nil() -> List[A]: ...
    @constructor
    def Cons(head: A, tail: List[A]) -> List[A]: ...

@dependent(decreases="xs")
def append[A: Type](xs: List[A], ys: List[A]) -> List[A]:
    match xs:
        case Nil():
            return ys
        case Cons(head, tail):
            return Cons(head, append(tail, ys))
```

class内のconstructor名は検査対象moduleの公開名として登録する。constructor名を重複させることはできない。parameterは`Cons[A](head, tail)`のように明示でき、省略時は推論する。型の添字はparameterの後に指定する。これらは静的な宣言構文であり、classやdecoratorを実行して検査するものではない。

`@inductive(level=1)`でuniverseを指定できる。添字はclassのconstructor宣言より前に`length: Index[Nat]`のように記述する。各constructorは自分のfieldで添字の証拠を束縛し、`IVec[A, S(k)]`のように戻り先を指定する。classのindex名はconstructorのローカル値ではない。

明示的な消去は`induct(level, value, motive, *branches)`。motiveは各添字と分解対象を受け取り、branchは宣言順のfield、その後に再帰fieldごとの帰納法仮定を受け取る。関数型の再帰fieldには関数型の帰納法仮定が渡る。

`absurd(type, value)`は空型、および全constructorの戻り先添字と対象の添字がconstructorの不一致で矛盾する場合に使用できる。未確定の添字や任意の等式から矛盾を推測しない。

## 分岐とライブラリ

一般帰納型のconstructor patternを順序付きpattern matrixとしてコンパイルする。入れ子constructor、capture、wildcard、入れ子match、網羅性・到達不能な重複・arity・名目的な型を検査する。複数の直接再帰fieldへの自己呼び出し、後続引数の一般化、添字の精緻化に対応する。入れ子の分解で取り出した子孫への再帰は、一般帰納法で構成した履歴から帰納法仮定を取得する。明示的な`decreases`のないmatchは最初のmatch対象を構造的引数にする。関数型の再帰fieldへの帰納法は明示的な`induct`で記述する。

固定・複合添字は、正規化すると変数とconstructorからなる線形patternになる場合に分岐できる。constructorの不一致で不可能な分岐は省略できる。motiveを添字で分岐させ、対象外の添字にはinhabitedな型を返すため、新しい公理やkernelの特例を必要としない。入れ子の固定添字matchでは必要な局所文脈を一般化し、暗黙引数の消去も保持する。一般IVec/IFinの`get`は入れ子matchで定義している。

- `deppy.data`: Empty、Unit、Bool、Sum、Option、Not、Decidable。
- `deppy.lists`: List、append、map、snoc、reverse、append_assoc、map_identity、map_composition、reverse_snoc、reverse_involution。
- `deppy.naturals`: 一般帰納型によるNat・Z・S、add、zero_right。
- `deppy.indexed`: 一般Natを添字にしたIVec・IFin、fin_case、get。型と消去に専用Nat・Vec・Fin coreを使わない。

Listの四定理を一般形で検査し、具体値の証明の正規形がreflになることも確認している。IVecのgetは具体的な二つの位置を計算し、不正なboundを拒否する。これらは公理に依存しない。一般帰納型のconstructor・eliminator・absurdをruntime IRへ消去し、standalone Pythonへ生成できる。

runtimeの一般帰納値は、recordと別の名目的なtag、constructor番号、immutableなfield tupleで表す。消去は全fieldの後に再帰fieldのIHを渡し、複数の再帰fieldと関数型の再帰fieldに対応する。直接再帰の評価と境界検査には明示的なstackを使う。

公開境界では、型parameterに対応するschema、constructorのarity、fieldの依存型、constructorが返す添字を検査する。再帰型のschemaは有限な宣言templateへの参照として生成する。List・木・一般Natを添字にしたIVec/IFinに対応し、内部計算で必要な等式証明は保持する。第一階の値parameterにも対応する。高階fieldと関数引数には、呼び出し時に引数・結果を検査するwrapperを付ける。後続fieldのschemaは検査済みの先行fieldから計算する。添字の比較はNat/Fin/Vecと、具体的なcarrierを持つ一般帰納値に制限し、型・証明・関数など消去で区別が失われる値を含む添字を拒否する。

## 既存APIの移行と対応範囲

既存Nat・Vec・Finは、一般`DataDecl`として通常のpositivity・型検査を通して登録する。具体的universeのVec宣言も同じ検査を使う。elaboratorの既存構文とRustの互換builderは一般`Data`項へ変換する。trustedな`Term`・意味値・neutral値にNat・Vec・Fin専用variantはない。既存Vec証明群の検査とruntime回帰も、この経路を使用する。

Pythonの既存int・tuple・有限添字の表現は境界adapterとして維持する。計算は一般eliminatorに統一し、専用Python recursorは削除した。

以下は受理範囲外として明示的に拒否する。未対応の構文を公理や未検査のcoreへ変換することはない。

- guard、keyword pattern、OR pattern、任意の等式証明を使う分岐探索、非線形・中立な関数適用を含む添字pattern。
- 相互帰納型、既存型作用素を介したnested recursion、universe polymorphism。
- 外部Pythonからの証明入力、runtimeで消去した値が必要な境界検査、任意の型族のruntime schema。
- 既存builtin構文のpattern拡張は従来の互換経路の範囲に従う。一般pattern matrixは`@inductive`で宣言した帰納型に適用する。

処理予算とRust/Pythonのstack制約は残る。外部callbackの停止性はruntime wrapperでは証明しない。

## 変更時の検証

workspaceに、一般帰納型の型検査・positivity・原子的登録・NbE・neutralな消去・公理依存、Pythonの宣言・import alias・複数fieldへの再帰・indexed get・absurd・Listの四定理・偽の等式の拒否を追加した。pattern位置、型の形のエラー、一般帰納型のgoal表示にも回帰試験がある。

一般帰納型のruntime実行は専用の統合試験で検証する。Listのappend・長さ・和、二分木、関数型の再帰field、証明fieldを経由するJ、IVec/IFinのget、深さ2,000のList、不正なtag・arity・field・添字の拒否を確認する。既存のruntime差分試験とCPythonの構文compile検証も維持する。

実行コマンドと検証範囲は[開発・検証手順](development.md)を参照。
