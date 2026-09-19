# `@dependent` Phase 1の実装状況

Phase 1全体は未完了。一般帰納型とListの四定理、一般Natを添字にしたVec/Fin相当の安全な参照まで検査できる。既存のNat・Vec・Finの専用coreとruntime経路は、既存証明の移行が終わるまで保持する。

## 実装済みの基盤

- 式のsource identity・spanをPythonからelaborationと構造的loweringへ伝播。
- 診断の種別、source、行・列、関連する宣言位置、型照合の期待型・実際の型。型の形のエラーとreflの不一致にも型情報を付ける。
- 重複・型違いのpatternはそのpattern、非網羅の分岐はそのmatchを診断位置にする。入れ子・import先のsourceを保持する。
- resolver・builtin registry・module graph・dependent linkerの分離、`FrontendOptions`。
- 名前付きholeと局所文脈付きgoal、`analyze_module`、`--goals`、`--json`。goal IDは解析全体で一意にする。
- opaqueな検査済み定義と、公理を区別した依存追跡。
- kernel snapshotに結びついた読み取り専用interface。一般帰納型・constructorの宣言種別と、parameter/index telescope・constructor metadataを公開する。

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

一般帰納型の平坦なconstructor patternに対し、網羅性・重複・arity・名目的な型を検査する。複数の直接再帰fieldへの自己呼び出し、後続引数の一般化、添字の精緻化、wildcard fieldに対応する。明示的な`decreases`のないmatchは最初のmatch対象を構造的引数にする。関数型の再帰fieldへの帰納法は明示的な`induct`で記述する。

- `deppy.data`: Empty、Unit、Bool、Sum、Option、Not、Decidable。
- `deppy.lists`: List、append、map、snoc、reverse、append_assoc、map_identity、map_composition、reverse_snoc、reverse_involution。
- `deppy.naturals`: 一般帰納型によるNat・Z・S、add、zero_right。
- `deppy.indexed`: 一般Natを添字にしたIVec・IFin、fin_case、get。型と消去に専用Nat・Vec・Fin coreを使わない。

Listの四定理を一般形で検査し、具体値の証明の正規形がreflになることも確認している。IVecのgetは具体的な二つの位置を計算し、不正なboundを拒否する。これらは公理に依存しない。一般帰納型のruntime projectionは未対応なので、Pythonコード生成では拒否する。

## 残る実装

1. **一般のpattern matrix:** 入れ子constructor pattern、一般帰納型の入れ子match、固定・複合添字のmatch、証明可能な不可能分岐の自動省略。現在の構造的indexed matchは相異なる先行parameterを添字にする。`absurd`の明示的な空消去と、分岐の自動省略は区別する。
2. **module interface linking:** interfaceは検査済みsnapshotとmetadataを公開するが、importは静的ソースの集約と再検査を続ける。snapshotを再利用するlinking、公開alias・射影を含む名前環境の統一、残る診断種別の型情報が必要。
3. **既存stdlib・runtimeの移行:** 既存Vec証明群と公開APIを一般Nat・Vec・Finへ移し、一般帰納型の消去・runtime表現・境界検査を実装する。
4. **専用core削除:** 既存証明とruntime回帰を一般機構で通してからNat・Vec・Finの専用項・規則を削除する。新しいライブラリの検査成功だけを削除の根拠にはしない。

## 変更時の検証

workspaceに、一般帰納型の型検査・positivity・原子的登録・NbE・neutralな消去・公理依存、Pythonの宣言・import alias・複数fieldへの再帰・indexed get・absurd・Listの四定理・偽の等式の拒否を追加した。pattern位置、型の形のエラー、一般帰納型のgoal表示にも回帰試験がある。

既存のruntime差分試験とCPythonの構文compile検証は、新しい一般帰納型のruntime実行を検証するものではない。

2026-09-20の検証: workspace 366件、全targetのClippy（警告をエラー化）、fmt、diff checkが成功。CPython 3.14.7で25ソースの構文compileと既存runtime差分244件が成功。
