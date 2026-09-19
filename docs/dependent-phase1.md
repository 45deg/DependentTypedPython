# `@dependent` Phase 1の実装状況

設計方針のPhase 1全体は未完了。既存のNat・Vec・Finは専用coreのまま残している。

## 追加済みの基盤

- 式のsource identity・spanをPythonからelaborationと構造的loweringへ伝播。
- 診断の種別、source、行・列、関連する宣言位置、通常の型照合における期待型・実際の型。
- resolver・builtin registry・module graph・dependent linkerの分離、`FrontendOptions`。
- 名前付きholeと局所文脈付きgoal、`analyze_module`、`--goals`、`--json`。
- opaqueな検査済み定義と、公理を区別した依存追跡。
- kernel snapshotに結びついた読み取り専用の公開interface。

未完成の宣言は環境に登録されない。独立した通常関数の解析は続け、依存する宣言は未解決名として診断する。解析に診断がある場合はmodule全体を未検証として返す。構文・公理・record宣言のエラーでは収集を打ち切る。

## 現在の基盤の仕上げ

goal IDは解析全体で一意とし、診断内のgoalと`Analysis.goals`で同じ値を保持する。hole診断の主位置は最初のhole式、関連位置は宣言とする。`Diagnostic`の表示はsource名・行・列がある場合にそれを使う。

`analyze_module_with_options`でresolverを使わない解析にも処理予算を指定できる。`Analysis.set_root_source_name`は診断・goal・関連位置のroot source名を一括設定し、import先のsource名を保持する。CLIもこのAPIを使う。

`ann`によるholeの型指定、日本語を含む行の列番号、diamond importでのopaque宣言ID共有を回帰試験で確認している。

## 次段階に残す実装

1. **診断・名前環境の仕上げ:** pattern固有の位置、全エラー種別の型情報、帰納型・constructor・射影を統一した名前環境。現在のinterfaceは検査後の公開snapshotであり、importは静的ソースの集約と再検査を続ける。一般帰納型のmetadataとinterfaceを介したlinkingは未実装。
2. **一般帰納型:** parameter/index telescope、複数constructor、直接再帰とΠ型の正位置、kernelでのpositivity検査、一般eliminatorとNbE。Pythonの `@inductive` / `@constructor` / `Index` / `induct` 構文は未実装。
3. **一般の分岐:** constructor pattern matrix、非再帰match、index精緻化と証明可能な不可能分岐の消去、一般の停止性検査、`absurd`。既存のNat・Vec・Fin向けloweringを置き換える。
4. **stdlibと削除:** Empty・Unit・Bool・List・Sum・Option・Not・Decidable、続いてNat・Vec・FinをPython定義へ移行。Listの四定理と既存Vec証明が一般機構で検査できてから専用項と専用規則を削除し、runtime projectionも移行する。

## 変更時の検証

workspaceテストに、opaqueの本体検査・非展開・公理追跡、holeの位置・局所文脈・未使用時の拒否、複数goal、式とimport先の診断、処理予算、CLI、interface snapshotの回帰を追加した。

一般帰納型以降の受け入れ条件は未達成であり、専用coreを削除する根拠にはしない。
