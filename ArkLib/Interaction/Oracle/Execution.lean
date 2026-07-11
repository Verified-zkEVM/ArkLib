/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Core

set_option linter.style.longFile 1700

/-!
# Oracle Reduction Execution

Concrete execution of oracle-decorated reductions. The oracle decoration adds
per-sender-node oracle interfaces that grow the ambient `OracleSpec` as the
protocol progresses. This module provides:

- `simulateQ` lemmas for splitting, appending, and casting oracle query handlers
- `run` / `execute`: running an `OracleVerifier` or `OracleReduction` against
  an oracle-aware prover, reducing to `OracleComp` computations
- `mapExecuteWitness` / `forgetExecuteWitness`: post-processing the witness
  output of an executed oracle reduction
- equivalence lemmas between running against concrete oracle implementations
  and running via `simulateQ`-based composition

## See also

- `Oracle/Core.lean` — oracle decoration definitions and query handle algebra
- `Oracle/Continuation.lean` — chained (multi-stage) oracle composition
-/

open OracleComp OracleSpec
open Interaction.TwoParty

namespace Interaction

namespace OracleDecoration

theorem simulateQ_map
    {ι : Type _} {spec : OracleSpec ι}
    {r : Type _ → Type _}
    [Monad r] [LawfulMonad r]
    {α β : Type _}
    (impl : QueryImpl spec r)
    (f : α → β)
    (oa : OracleComp spec α) :
    simulateQ impl (f <$> oa) = f <$> simulateQ impl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind t oa ih =>
      simp [ih]

/-! ## Composition infrastructure

To compose oracle reductions, we need that `toMonadDecoration` distributes over
`Spec.append` and `Spec.stateChain`. The accumulated oracle spec after the first phase
serves as the starting spec for the second phase. -/

/-- Lift a transcript-split oracle index family to the fused append transcript. -/
abbrev liftAppendOracleIdx
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type) :
    Spec.Transcript (spec₁.append spec₂) → Type :=
  Spec.Transcript.liftAppend spec₁ spec₂ ιₛ

/-- Lift a transcript-split oracle statement family to the fused append
transcript. -/
abbrev liftAppendOracleFamily
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type) :
    (tr : Spec.Transcript (spec₁.append spec₂)) → liftAppendOracleIdx spec₁ spec₂ ιₛ tr → Type :=
  fun tr i =>
    let split := Spec.Transcript.split spec₁ spec₂ tr
    OStmt split.1 split.2 (Spec.Transcript.unliftAppend spec₁ spec₂ ιₛ tr i)

/-- View a fused append-oracle query as a query to the split append oracle family
without first rewriting the transcript back to `append tr₁ tr₂`. -/
def splitLiftAppendOracleQuery
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type)
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)]
    (tr : Spec.Transcript (spec₁.append spec₂))
    (qOut : ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt tr]ₒ).Domain) :
    let split := Spec.Transcript.split spec₁ spec₂ tr
    ([OStmt split.1 split.2]ₒ).Domain := by
  exact ⟨Spec.Transcript.unliftAppend spec₁ spec₂ ιₛ tr qOut.1, qOut.2⟩

/-- View an answer to the split append oracle family as an answer to the fused
append oracle family. -/
def answerSplitLiftAppendQuery
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type)
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)]
    (tr : Spec.Transcript (spec₁.append spec₂))
    (qOut : ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt tr]ₒ).Domain) :
    ([OStmt (Spec.Transcript.split spec₁ spec₂ tr).1
      (Spec.Transcript.split spec₁ spec₂ tr).2]ₒ).Range
        (splitLiftAppendOracleQuery spec₁ spec₂ ιₛ OStmt tr qOut) →
    ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt tr]ₒ).Range qOut
  | a => a

/-- At an appended transcript `append tr₁ tr₂`, the fused lifted oracle family
reduces to the split oracle family after unpacking the lifted index. -/
theorem liftAppendOracleFamily_append_eq
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type)
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)]
    (tr₁ : Spec.Transcript spec₁)
    (tr₂ : Spec.Transcript (spec₂ tr₁))
    (i :
      liftAppendOracleIdx spec₁ spec₂ ιₛ
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)) :
    liftAppendOracleFamily
        spec₁ spec₂ ιₛ OStmt
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂) i =
      OStmt tr₁ tr₂
        (Spec.Transcript.unpackAppend spec₁ spec₂ ιₛ tr₁ tr₂ i) := by
  let iSplit := Spec.Transcript.unpackAppend spec₁ spec₂ ιₛ tr₁ tr₂ i
  have hi :
      Spec.Transcript.packAppend spec₁ spec₂ ιₛ tr₁ tr₂ iSplit = i := by
    dsimp [iSplit]
    exact Spec.Transcript.packAppend_unpackAppend spec₁ spec₂ ιₛ tr₁ tr₂ i
  calc
    liftAppendOracleFamily
        spec₁ spec₂ ιₛ OStmt
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂) i =
      liftAppendOracleFamily
        spec₁ spec₂ ιₛ OStmt
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
        (Spec.Transcript.packAppend spec₁ spec₂ ιₛ tr₁ tr₂ iSplit) := by
      rw [← hi]
    _ = OStmt tr₁ tr₂ iSplit := by
      calc
        OStmt
            (Spec.Transcript.split spec₁ spec₂
                (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).fst
            (Spec.Transcript.split spec₁ spec₂
                (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).snd
            (Spec.Transcript.unliftAppend spec₁ spec₂ ιₛ
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
              (Spec.Transcript.packAppend spec₁ spec₂ ιₛ tr₁ tr₂ iSplit)) =
          OStmt tr₁ tr₂
            (Spec.Transcript.unliftAppend
              spec₁ spec₂ (fun _ _ => ιₛ tr₁ tr₂)
              (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
              (Spec.Transcript.packAppend
                spec₁ spec₂ (fun _ _ => ιₛ tr₁ tr₂) tr₁ tr₂ iSplit)) := by
          simpa [liftAppendOracleFamily] using
            (Spec.Transcript.rel_unliftAppend_append
              spec₁ spec₂
              ιₛ
              (fun _ _ => ιₛ tr₁ tr₂)
              (fun tr₁' tr₂' i j => OStmt tr₁' tr₂' i = OStmt tr₁ tr₂ j)
              tr₁ tr₂ iSplit iSplit)
        _ = OStmt tr₁ tr₂ iSplit := by
          have hConst :
              Spec.Transcript.unliftAppend
                  spec₁ spec₂ (fun _ _ => ιₛ tr₁ tr₂)
                  (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)
                  (Spec.Transcript.packAppend
                    spec₁ spec₂ (fun _ _ => ιₛ tr₁ tr₂) tr₁ tr₂ iSplit) =
                iSplit := by
            let rec h :
                ∀ {s₁ : Spec} {s₂ : Spec.Transcript s₁ → Spec}
                  (A : Type _)
                  (tr₁ : Spec.Transcript s₁) (tr₂ : Spec.Transcript (s₂ tr₁))
                  (x : A),
                  Spec.Transcript.unliftAppend s₁ s₂ (fun _ _ => A)
                    (Spec.Transcript.append s₁ s₂ tr₁ tr₂)
                    (Spec.Transcript.packAppend s₁ s₂ (fun _ _ => A) tr₁ tr₂ x) = x
                | .done, _, _, ⟨⟩, _, _ => rfl
                | .node _ rest, s₂, A, ⟨xm, tail₁⟩, tr₂, x => by
                    simpa [Spec.Transcript.unliftAppend, Spec.Transcript.packAppend,
                      Spec.Transcript.append] using
                      h (s₁ := rest xm) (s₂ := fun p => s₂ ⟨xm, p⟩) A tail₁ tr₂ x
            exact h (A := ιₛ tr₁ tr₂) tr₁ tr₂ iSplit
          exact congrArg (fun j => OStmt tr₁ tr₂ j) hConst

/-- Specialization of `answerSplitLiftAppendQuery` to a fused transcript
already known to be `append tr₁ tr₂`, phrased in terms of the corresponding
casted split query `qSplit`. -/
def answerSplitLiftAppendQueryAppend
    (spec₁ : Spec) :
    (spec₂ : Spec.Transcript spec₁ → Spec) →
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type) →
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type) →
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)] →
    (tr₁ : Spec.Transcript spec₁) →
    (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    (qOut : ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt
      (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)]ₒ).Domain) →
    let qSplit : ([OStmt tr₁ tr₂]ₒ).Domain :=
      cast
        (congrArg (fun p => ([OStmt p.1 p.2]ₒ).Domain)
          (Spec.Transcript.split_append spec₁ spec₂ tr₁ tr₂))
        (splitLiftAppendOracleQuery
          spec₁ spec₂ ιₛ OStmt
          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂) qOut)
    ([OStmt tr₁ tr₂]ₒ).Range qSplit →
      ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)]ₒ).Range qOut :=
  match spec₁ with
  | .done => fun spec₂ ιₛ OStmt _ tr₁ tr₂ qOut => by
      cases tr₁
      dsimp
      intro a
      simpa using a
  | .node X rest => fun spec₂ ιₛ OStmt _ tr₁ tr₂ qOut => by
      cases tr₁ with
      | mk x tail₁ =>
          dsimp
          simpa using
            (answerSplitLiftAppendQueryAppend
              (rest x)
              (fun p => spec₂ ⟨x, p⟩)
              (fun tr₁ tr₂ => ιₛ ⟨x, tr₁⟩ tr₂)
              (fun tr₁ tr₂ i => OStmt ⟨x, tr₁⟩ tr₂ i)
              tail₁ tr₂ qOut)

/-- At a fused append transcript already known to be `append tr₁ tr₂`, the raw
split-query response type used by `answerSplitLiftAppendQuery` agrees with the
casted split-query response type used by `answerSplitLiftAppendQueryAppend`. -/
theorem splitLiftAppendOracleRange_eq
    (spec₁ : Spec) :
    (spec₂ : Spec.Transcript spec₁ → Spec) →
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type) →
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type) →
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)] →
    (tr₁ : Spec.Transcript spec₁) →
    (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    (qOut : ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt
      (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)]ₒ).Domain) →
    let qSplit : ([OStmt tr₁ tr₂]ₒ).Domain :=
      cast
        (congrArg (fun p => ([OStmt p.1 p.2]ₒ).Domain)
          (Spec.Transcript.split_append spec₁ spec₂ tr₁ tr₂))
        (splitLiftAppendOracleQuery
          spec₁ spec₂ ιₛ OStmt
          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂) qOut)
    ([OStmt (Spec.Transcript.split spec₁ spec₂
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).1
      (Spec.Transcript.split spec₁ spec₂
        (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)).2]ₒ).Range
        (splitLiftAppendOracleQuery
          spec₁ spec₂ ιₛ OStmt
          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂) qOut) =
      ([OStmt tr₁ tr₂]ₒ).Range qSplit
    := by
  intro spec₂ ιₛ OStmt _ tr₁ tr₂ qOut
  induction spec₁ with
  | done =>
      cases tr₁
      rfl
  | node X rest ih =>
      cases tr₁ with
      | mk x tail₁ =>
          dsimp [splitLiftAppendOracleQuery]
          simpa using
            (ih
              (spec₂ := fun p => spec₂ ⟨x, p⟩)
              (ιₛ := fun tr₁ tr₂ => ιₛ ⟨x, tr₁⟩ tr₂)
              (OStmt := fun tr₁ tr₂ i => OStmt ⟨x, tr₁⟩ tr₂ i)
              (tr₁ := tail₁) (tr₂ := tr₂) (qOut := qOut))

/-- Repackaging a casted split-query answer through `answerSplitLiftAppendQuery`
agrees with the append-specialized helper `answerSplitLiftAppendQueryAppend`. -/
theorem answerSplitLiftAppendQueryAppend_eq
    (spec₁ : Spec) :
    (spec₂ : Spec.Transcript spec₁ → Spec) →
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type) →
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type) →
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)] →
    (tr₁ : Spec.Transcript spec₁) →
    (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    (qOut : ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt
      (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)]ₒ).Domain) →
    let qSplit : ([OStmt tr₁ tr₂]ₒ).Domain :=
      cast
        (congrArg (fun p => ([OStmt p.1 p.2]ₒ).Domain)
          (Spec.Transcript.split_append spec₁ spec₂ tr₁ tr₂))
        (splitLiftAppendOracleQuery
          spec₁ spec₂ ιₛ OStmt
          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂) qOut)
    (ans : ([OStmt tr₁ tr₂]ₒ).Range qSplit) →
    answerSplitLiftAppendQuery spec₁ spec₂ ιₛ OStmt
      (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂) qOut
      (cast
        (splitLiftAppendOracleRange_eq spec₁ spec₂ ιₛ OStmt tr₁ tr₂ qOut).symm
        ans) =
      answerSplitLiftAppendQueryAppend spec₁ spec₂ ιₛ OStmt tr₁ tr₂ qOut ans
    := by
  intro spec₂ ιₛ OStmt _ tr₁ tr₂ qOut ans
  induction spec₁ with
  | done =>
      cases tr₁
      dsimp [splitLiftAppendOracleRange_eq]
      intro a
      rfl
  | node X rest ih =>
      cases tr₁ with
      | mk x tail₁ =>
          dsimp [answerSplitLiftAppendQuery, answerSplitLiftAppendQueryAppend,
            splitLiftAppendOracleRange_eq]
          intro a
          simpa using
            (ih
              (spec₂ := fun p => spec₂ ⟨x, p⟩)
              (ιₛ := fun tr₁ tr₂ => ιₛ ⟨x, tr₁⟩ tr₂)
              (OStmt := fun tr₁ tr₂ i => OStmt ⟨x, tr₁⟩ tr₂ i)
              (tr₁ := tail₁) (tr₂ := tr₂) (qOut := qOut) (ans := a))

/-- At a fused append transcript already known to be `append tr₁ tr₂`, feeding
the casted split query to a concrete split oracle statement and then
repackaging the answer through `answerSplitLiftAppendQueryAppend` agrees with
directly answering the fused query against the corresponding fused oracle
statement. -/
theorem answerSplitLiftAppendQueryAppend_simOracle0
    (spec₁ : Spec) :
    (spec₂ : Spec.Transcript spec₁ → Spec) →
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type) →
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type) →
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)] →
    (tr₁ : Spec.Transcript spec₁) →
    (tr₂ : Spec.Transcript (spec₂ tr₁)) →
    (oStatement : OracleStatement (OStmt tr₁ tr₂)) →
    (qOut : ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt
      (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)]ₒ).Domain) →
    let qSplit : ([OStmt tr₁ tr₂]ₒ).Domain :=
      cast
        (congrArg (fun p => ([OStmt p.1 p.2]ₒ).Domain)
          (Spec.Transcript.split_append spec₁ spec₂ tr₁ tr₂))
        (splitLiftAppendOracleQuery
          spec₁ spec₂ ιₛ OStmt
          (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂) qOut)
    answerSplitLiftAppendQueryAppend spec₁ spec₂ ιₛ OStmt tr₁ tr₂ qOut
      ((OracleInterface.simOracle0 (OStmt tr₁ tr₂) oStatement) qSplit) =
      let i := qOut.1
      let q := qOut.2
      let iSplit := Spec.Transcript.unpackAppend spec₁ spec₂ ιₛ tr₁ tr₂ i
      let hQueryTy :
          liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt
            (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂) i =
            OStmt tr₁ tr₂ iSplit :=
        liftAppendOracleFamily_append_eq spec₁ spec₂ ιₛ OStmt tr₁ tr₂ i
      OracleInterface.answer (cast hQueryTy.symm (oStatement iSplit)) q :=
  match spec₁ with
  | .done => fun spec₂ ιₛ OStmt _ tr₁ tr₂ oStatement qOut => by
      cases tr₁
      cases qOut with
      | mk i q =>
          rfl
  | .node X rest => fun spec₂ ιₛ OStmt _ tr₁ tr₂ oStatement qOut => by
      cases tr₁ with
      | mk x tail₁ =>
          simpa [Spec.Transcript.unpackAppend, liftAppendOracleFamily_append_eq]
            using
              (answerSplitLiftAppendQueryAppend_simOracle0
                (rest x)
                (fun p => spec₂ ⟨x, p⟩)
                (fun tr₁ tr₂ => ιₛ ⟨x, tr₁⟩ tr₂)
                (fun tr₁ tr₂ j => OStmt ⟨x, tr₁⟩ tr₂ j)
                tail₁ tr₂ oStatement qOut)

/-- Repackage a routed split-world append-oracle computation as the public
fused append-oracle computation. This centralizes the only propositional
transport needed at the append boundary: internally we work with the split
transcript recovered by `Transcript.split`, while the public API is indexed by
the fused transcript `tr`. -/
def collapseAppendOracleComp
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (Idx :
      Spec.Transcript (spec₁.append spec₂) → Type _)
    (baseSpec : (tr : Spec.Transcript (spec₁.append spec₂)) → OracleSpec (Idx tr))
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type)
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)]
    (tr : Spec.Transcript (spec₁.append spec₂))
    (qOut : ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt tr]ₒ).Domain)
    (oa :
      let split := Spec.Transcript.split spec₁ spec₂ tr
      OracleComp
        (baseSpec (Spec.Transcript.append spec₁ spec₂ split.1 split.2))
        (([OStmt split.1 split.2]ₒ).Range
          (splitLiftAppendOracleQuery spec₁ spec₂ ιₛ OStmt tr qOut))) :
    OracleComp
      (baseSpec tr)
      (([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt tr]ₒ).Range qOut) := by
  let split := Spec.Transcript.split spec₁ spec₂ tr
  let tr₁ := split.1
  let tr₂ := split.2
  let qSplit :=
    splitLiftAppendOracleQuery spec₁ spec₂ ιₛ OStmt tr qOut
  let fusedAnswer :=
    answerSplitLiftAppendQuery spec₁ spec₂ ιₛ OStmt tr qOut
  have htr : Spec.Transcript.append spec₁ spec₂ tr₁ tr₂ = tr := by
    simpa [tr₁, tr₂, split] using
      (Spec.Transcript.append_split spec₁ spec₂ tr)
  have hSpec :
      OracleComp
        (baseSpec (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂))
        (([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt tr]ₒ).Range qOut) =
      OracleComp (baseSpec tr)
        (([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt tr]ₒ).Range qOut) := by
    simpa using
      congrArg
        (fun tr' =>
          OracleComp (baseSpec tr')
            (([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt tr]ₒ).Range qOut))
        htr
  exact cast hSpec (fusedAnswer <$> oa)

/-- Simulating `collapseAppendOracleComp` evaluates the routed split-world
computation and then repackages its answer via `answerSplitLiftAppendQuery`. -/
theorem simulateQ_collapseAppendOracleComp
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (Idx :
      Spec.Transcript (spec₁.append spec₂) → Type _)
    (baseSpec : (tr : Spec.Transcript (spec₁.append spec₂)) → OracleSpec (Idx tr))
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type)
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)]
    (tr : Spec.Transcript (spec₁.append spec₂))
    (qOut : ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt tr]ₒ).Domain)
    (impl : QueryImpl (baseSpec tr) Id)
    (oa :
      let split := Spec.Transcript.split spec₁ spec₂ tr
      OracleComp
        (baseSpec (Spec.Transcript.append spec₁ spec₂ split.1 split.2))
        (([OStmt split.1 split.2]ₒ).Range
          (splitLiftAppendOracleQuery spec₁ spec₂ ιₛ OStmt tr qOut))) :
    simulateQ impl
      (collapseAppendOracleComp spec₁ spec₂ Idx baseSpec ιₛ OStmt tr qOut oa) =
      answerSplitLiftAppendQuery spec₁ spec₂ ιₛ OStmt tr qOut
        (simulateQ
          (cast
            (by
              let split := Spec.Transcript.split spec₁ spec₂ tr
              let tr₁ := split.1
              let tr₂ := split.2
              have htr : Spec.Transcript.append spec₁ spec₂ tr₁ tr₂ = tr := by
                simpa [tr₁, tr₂, split] using
                  (Spec.Transcript.append_split spec₁ spec₂ tr)
              simpa using (congrArg (fun tr' => QueryImpl (baseSpec tr') Id) htr).symm)
            impl)
          oa) := by
  unfold collapseAppendOracleComp
  let split := Spec.Transcript.split spec₁ spec₂ tr
  let tr₁ := split.1
  let tr₂ := split.2
  have htr : Spec.Transcript.append spec₁ spec₂ tr₁ tr₂ = tr := by
    simpa [tr₁, tr₂, split] using
      (Spec.Transcript.append_split spec₁ spec₂ tr)
  let impl' :
      QueryImpl (baseSpec (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)) Id :=
    cast
      (by
        simpa using (congrArg (fun tr' => QueryImpl (baseSpec tr') Id) htr).symm)
      impl
  calc
    simulateQ impl
        (cast
          (by
            simpa using
              congrArg
                (fun tr' =>
                  OracleComp (baseSpec tr')
                    (([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt tr]ₒ).Range qOut))
                htr)
          (answerSplitLiftAppendQuery spec₁ spec₂ ιₛ OStmt tr qOut <$> oa)) =
      simulateQ impl' (answerSplitLiftAppendQuery spec₁ spec₂ ιₛ OStmt tr qOut <$> oa) := by
        simpa [impl'] using
          (simulateQ_cast_dep
            (Idx := Idx) (SpecFam := baseSpec) htr
            impl
            (answerSplitLiftAppendQuery spec₁ spec₂ ιₛ OStmt tr qOut <$> oa))
    _ =
      answerSplitLiftAppendQuery spec₁ spec₂ ιₛ OStmt tr qOut
        <$> simulateQ impl' oa := by
        exact
          (simulateQ_map impl'
            (answerSplitLiftAppendQuery spec₁ spec₂ ιₛ OStmt tr qOut) oa)
    _ =
      answerSplitLiftAppendQuery spec₁ spec₂ ιₛ OStmt tr qOut
        (simulateQ impl' oa) := by
        rfl

/-- Accumulated oracle spec after traversing `spec` along transcript `tr`,
starting from `accSpec`. At sender nodes, adds the node's oracle interface spec.
At receiver nodes, the accumulated spec is unchanged. -/
def accSpecAfter :
    (spec : Spec) → (roles : RoleDecoration spec) → OracleDecoration spec roles →
    {ιₐ : Type} → OracleSpec ιₐ → Spec.Transcript spec →
    Σ (ιₐ' : Type), OracleSpec ιₐ'
  | .done, _, _, _, accSpec, _ => ⟨_, accSpec⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec, ⟨x, trRest⟩ =>
      accSpecAfter (rest x) (rRest x) (odRest x)
        (accSpec + @OracleInterface.spec _ oi) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec, ⟨x, trRest⟩ =>
      accSpecAfter (rest x) (rRest x) (odFn x) accSpec trRest

/-- Concrete implementation of the accumulated sender-message oracle spec after
traversing a transcript. -/
def accImplAfter :
    (spec : Spec) → (roles : RoleDecoration spec) → (od : OracleDecoration spec roles) →
    {ιₐ : Type} → (accSpec : OracleSpec ιₐ) → QueryImpl accSpec Id →
    (tr : Spec.Transcript spec) →
    QueryImpl ((accSpecAfter spec roles od accSpec tr).2) Id
  | .done, _, _, _, _, accImpl, _ => accImpl
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec, accImpl, ⟨x, trRest⟩ =>
      let implX : QueryImpl (@OracleInterface.spec _ oi) Id := fun q => (oi.toOC.impl q).run x
      accImplAfter (rest x) (rRest x) (odRest x) (accSpec + @OracleInterface.spec _ oi)
        (QueryImpl.add accImpl implX) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec, accImpl, ⟨x, trRest⟩ =>
      accImplAfter (rest x) (rRest x) (odFn x) accSpec accImpl trRest

/-- Execute a prover strategy against a monadic oracle verifier counterpart.

This is the core operational engine behind the impl-based oracle execution APIs
and their concrete-input specializations. It threads three oracle sources
through the verifier:

- ambient base oracles `oSpec`,
- concrete input oracles `OStmtIn`,
- accumulated sender-message oracles `accSpec`.

The result packages the realized transcript, prover output, and verifier output
for that transcript. -/
def runWithOracleCounterpart
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (inputImpl : QueryImpl [OStmtIn]ₒ Id) :
    (spec : Spec) → (roles : RoleDecoration spec) → (od : OracleDecoration spec roles) →
    {ιₐ : Type} → (accSpec : OracleSpec ιₐ) → QueryImpl accSpec Id →
    {OutputP OutputC : Spec.Transcript spec → Type} →
    Spec.Strategy.withRoles (OracleComp oSpec) spec roles OutputP →
    Spec.Counterpart.withMonads spec roles
      (toMonadDecoration oSpec OStmtIn spec roles od accSpec) OutputC →
    OracleComp oSpec ((tr : Spec.Transcript spec) × OutputP tr × OutputC tr)
  | .done, _, _, _, _, _, _, _, output, cOutput =>
      pure ⟨⟨⟩, output, cOutput⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec, accImpl, OutputP, OutputC,
      send, dualFn => do
      let ⟨x, next⟩ ← send
      let implX : QueryImpl (@OracleInterface.spec _ oi) Id := fun q => (oi.toOC.impl q).run x
      let z ← runWithOracleCounterpart inputImpl
        (rest x) (rRest x) (odRest x) (accSpec + @OracleInterface.spec _ oi)
        (QueryImpl.add accImpl implX) next (dualFn x)
      let tail := z.1
      let outP := z.2.1
      let outC := z.2.2
      return ⟨⟨x, tail⟩, outP, outC⟩
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec, accImpl, OutputP, OutputC,
      respond, dualSample => do
      let routeImpl :
          QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
        fun
        | .inl (.inl q) => liftM (oSpec.query q)
        | .inl (.inr q) => liftM (inputImpl q)
        | .inr q => liftM (accImpl q)
      have dualSample' : OracleComp ((oSpec + [OStmtIn]ₒ) + accSpec) _ := by
        simpa using dualSample
      let z' : Sigma (fun x =>
          Spec.Counterpart.withMonads (rest x) (rRest x)
            (toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (odFn x) accSpec)
            (fun p => OutputC ⟨x, p⟩)) ←
        simulateQ routeImpl dualSample'
      let x := z'.1
      let dualRest := z'.2
      let next ← respond x
      let z ← runWithOracleCounterpart inputImpl
        (rest x) (rRest x) (odFn x) accSpec accImpl next dualRest
      let tail := z.1
      let outP := z.2.1
      let outC := z.2.2
      return ⟨⟨x, tail⟩, outP, outC⟩

namespace OracleReduction

/-- Run an arbitrary prover strategy against a concrete oracle input statement,
using the empty accumulated oracle context. This is the concrete-input
specialization of the more general impl-based execution API. -/
def runConcrete
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type} {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction :
      OracleReduction oSpec SharedIn Context Roles oracleDeco StatementIn OStatementIn WitnessIn
        StatementOut OStatementOut WitnessOut)
    (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    {OutputP : Spec.Transcript (Context shared) → Type}
    (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared) (Roles shared) OutputP) :
    OracleComp oSpec ((tr : Spec.Transcript (Context shared)) × OutputP tr ×
      (StatementOut shared tr × QueryImpl [OStatementOut shared tr]ₒ
        (OracleComp
          ([OStatementIn shared]ₒ + toOracleSpec (Context shared) (Roles shared)
            (oracleDeco shared) tr)))) := do
  let ⟨tr, outP, stmtOutV⟩ ←
    runWithOracleCounterpart (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt)
      (Context shared) (Roles shared) (oracleDeco shared) []ₒ (fun q => q.elim)
      prover (reduction.verifier shared []ₒ s.stmt)
  pure ⟨tr, outP, ⟨stmtOutV, reduction.simulate shared tr⟩⟩

end OracleReduction

end OracleDecoration

namespace OracleVerifier

/-- Run an arbitrary prover strategy against a verifier-only oracle protocol
surface against abstract deterministic input and accumulated oracle
implementations, and package the resulting plain verifier output with
transcript-indexed oracle access semantics. -/
def run
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type} {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (verifier :
      @Interaction.OracleVerifier ι oSpec SharedIn Context Roles oracleDeco StatementIn ιₛᵢ
        OStatementIn (by infer_instance) StatementOut ιₛₒ OStatementOut
        (by infer_instance))
    (shared : SharedIn)
    (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStatementIn shared]ₒ Id)
    {OutputP : Spec.Transcript (Context shared) → Type}
    (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared) (Roles shared) OutputP)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id) :
    OracleComp oSpec ((tr : Spec.Transcript (Context shared)) × OutputP tr ×
      (StatementOut shared tr × QueryImpl [OStatementOut shared tr]ₒ
        (OracleComp
          ([OStatementIn shared]ₒ +
            OracleDecoration.toOracleSpec
              (Context shared) (Roles shared) (oracleDeco shared) tr)))) := do
  let ⟨tr, outP, stmtOutV⟩ ←
    OracleDecoration.runWithOracleCounterpart inputImpl
      (Context shared) (Roles shared) (oracleDeco shared) accSpec accImpl
      prover (verifier shared accSpec stmt)
  pure ⟨tr, outP, ⟨stmtOutV, verifier.simulate shared tr⟩⟩
end OracleVerifier

namespace OracleDecoration

namespace OracleReduction

/-- Execute an oracle reduction honestly, but erase the prover's private witness
output and retain only the public outgoing statement-with-oracles together with
the verifier's plain output and transcript-indexed oracle simulation. -/
def executePublicConcrete
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type} {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction :
      OracleReduction oSpec SharedIn Context Roles oracleDeco StatementIn OStatementIn WitnessIn
        StatementOut OStatementOut WitnessOut)
    (shared : SharedIn) (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn shared) :
    OracleComp oSpec ((tr : Spec.Transcript (Context shared)) ×
      StatementWithOracles (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr)
        shared ×
      (StatementOut shared tr × QueryImpl [OStatementOut shared tr]ₒ
        (OracleComp
          ([OStatementIn shared]ₒ + toOracleSpec (Context shared) (Roles shared)
            (oracleDeco shared) tr)))) := do
  let strategy ← reduction.prover shared s w
  let ⟨tr, stmtOutP, stmtOutV⟩ ←
    runWithOracleCounterpart (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt)
      (Context shared) (Roles shared) (oracleDeco shared) []ₒ (fun q => q.elim)
      (Spec.Strategy.mapOutputWithRoles (fun _ out => out.stmt) strategy)
      (reduction.verifier shared []ₒ s.stmt)
  pure ⟨tr, stmtOutP, ⟨stmtOutV, reduction.simulate shared tr⟩⟩

/-- Two oracle reductions with the same public interface are *honestly publicly
equivalent* when, after relating their input witness types by `liftWitness`,
their honest executions produce exactly the same public transcript/output view.

This intentionally ignores private witness bookkeeping while keeping the full
verifier-facing behavior fixed. -/
def HonestPubliclyEquivalent
    {ι : Type} {oSpec : OracleSpec ι}
    {Input : Type} {ιₛᵢ : Input → Type}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {oracleDeco : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt WitnessIn₁ WitnessIn₂ : Input → Type}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    {WitnessOut₁ WitnessOut₂ : (i : Input) → Spec.Transcript (Context i) → Type}
    (liftWitness :
      (i : Input) → StatementWithOracles LocalStmt OStmtIn i → WitnessIn₁ i → WitnessIn₂ i)
    (reduction₁ : OracleReduction oSpec Input Context Roles oracleDeco LocalStmt OStmtIn WitnessIn₁
      StatementOut OStmtOut WitnessOut₁)
    (reduction₂ : OracleReduction oSpec Input Context Roles oracleDeco LocalStmt OStmtIn WitnessIn₂
      StatementOut OStmtOut WitnessOut₂) : Prop :=
  ∀ (i : Input) (s : StatementWithOracles LocalStmt OStmtIn i) (w : WitnessIn₁ i),
    reduction₁.executePublicConcrete i s w =
      reduction₂.executePublicConcrete i s (liftWitness i s w)

/-- Execute an oracle reduction honestly and package the verifier's plain output
with transcript-dependent oracle access semantics. -/
def executeConcrete
    {ι : Type} {oSpec : OracleSpec ι}
    {Input : Type} {ιₛᵢ : Input → Type}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {oracleDeco : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt WitnessIn : Input → Type}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    {WitnessOut : (i : Input) → Spec.Transcript (Context i) → Type}
    (reduction : OracleReduction oSpec Input Context Roles oracleDeco LocalStmt OStmtIn WitnessIn
      StatementOut OStmtOut WitnessOut)
    (i : Input) (s : StatementWithOracles LocalStmt OStmtIn i) (w : WitnessIn i) :
    OracleComp oSpec ((tr : Spec.Transcript (Context i)) ×
      HonestProverOutput
        (StatementWithOracles (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i)
        (WitnessOut i tr) ×
      (StatementOut i tr × QueryImpl [OStmtOut i tr]ₒ
        (OracleComp
          ([OStmtIn i]ₒ + toOracleSpec (Context i) (Roles i)
            (oracleDeco i) tr)))) := do
  let strategy ← reduction.prover i s w
  let ⟨tr, proverOut, stmtOutV⟩ ←
    runWithOracleCounterpart (OracleInterface.simOracle0 (OStmtIn i) s.oracleStmt)
      (Context i) (Roles i) (oracleDeco i) []ₒ (fun q => q.elim)
      strategy (reduction.verifier i []ₒ s.stmt)
  pure ⟨tr, proverOut, ⟨stmtOutV, reduction.simulate i tr⟩⟩

/-- Map the private honest-prover witness component of an executed oracle
reduction while leaving its public transcript/output view unchanged. -/
def mapExecuteWitness
    {ι : Type} {oSpec : OracleSpec ι}
    {Input : Type} {ιₛᵢ : Input → Type}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {oracleDeco : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt : Input → Type}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    {WitnessOut₁ WitnessOut₂ : (i : Input) → Spec.Transcript (Context i) → Type}
    (i : Input)
    (s : StatementWithOracles LocalStmt OStmtIn i)
    (liftWitness : (tr : Spec.Transcript (Context i)) →
      WitnessOut₁ i tr → WitnessOut₂ i tr) :
    ((tr : Spec.Transcript (Context i)) ×
      HonestProverOutput
        (StatementWithOracles (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i)
        (WitnessOut₁ i tr) ×
      (StatementOut i tr × QueryImpl [OStmtOut i tr]ₒ
        (OracleComp
          ([OStmtIn i]ₒ + toOracleSpec (Context i) (Roles i)
            (oracleDeco i) tr)))) →
    ((tr : Spec.Transcript (Context i)) ×
      HonestProverOutput
        (StatementWithOracles (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i)
        (WitnessOut₂ i tr) ×
      (StatementOut i tr × QueryImpl [OStmtOut i tr]ₒ
        (OracleComp
          ([OStmtIn i]ₒ + toOracleSpec (Context i) (Roles i)
            (oracleDeco i) tr)))) :=
  let _ := oSpec
  let _ := s
  fun ⟨tr, out, view⟩ => ⟨tr, ⟨out.stmt, liftWitness tr out.wit⟩, view⟩

/-- Forget the private honest-prover witness component of an executed oracle
reduction, keeping only its public transcript/output view. -/
def forgetExecuteWitness
    {ι : Type} {oSpec : OracleSpec ι}
    {Input : Type} {ιₛᵢ : Input → Type}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {oracleDeco : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt : Input → Type}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    {WitnessOut : (i : Input) → Spec.Transcript (Context i) → Type}
    (i : Input)
    (s : StatementWithOracles LocalStmt OStmtIn i) :
    ((tr : Spec.Transcript (Context i)) ×
      HonestProverOutput
        (StatementWithOracles (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i)
        (WitnessOut i tr) ×
      (StatementOut i tr × QueryImpl [OStmtOut i tr]ₒ
        (OracleComp
          ([OStmtIn i]ₒ + toOracleSpec (Context i) (Roles i)
            (oracleDeco i) tr)))) →
    ((tr : Spec.Transcript (Context i)) ×
      StatementWithOracles (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i ×
      (StatementOut i tr × QueryImpl [OStmtOut i tr]ₒ
        (OracleComp
          ([OStmtIn i]ₒ + toOracleSpec (Context i) (Roles i)
            (oracleDeco i) tr)))) :=
  let _ := oSpec
  let _ := s
  fun ⟨tr, out, view⟩ => ⟨tr, out.stmt, view⟩

/-- Two oracle reductions with the same public interface are *honestly
execution-equivalent* when, after relating their input witnesses by
`liftWitnessIn`, their full honest executions agree once the first reduction's
private output witness is transported along `liftWitnessOut`.

This is stronger than `HonestPubliclyEquivalent` and is the right notion for
sequential composition, since suffix reductions consume the honest prover's
private output witness. -/
def HonestExecutionEquivalent
    {ι : Type} {oSpec : OracleSpec ι}
    {Input : Type} {ιₛᵢ : Input → Type}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {oracleDeco : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt WitnessIn₁ WitnessIn₂ : Input → Type}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    {WitnessOut₁ WitnessOut₂ : (i : Input) → Spec.Transcript (Context i) → Type}
    (liftWitnessIn :
      (i : Input) → StatementWithOracles LocalStmt OStmtIn i → WitnessIn₁ i → WitnessIn₂ i)
    (liftWitnessOut :
      (i : Input) → (s : StatementWithOracles LocalStmt OStmtIn i) →
      (tr : Spec.Transcript (Context i)) →
      WitnessOut₁ i tr → WitnessOut₂ i tr)
    (reduction₁ : OracleReduction oSpec Input Context Roles oracleDeco LocalStmt OStmtIn WitnessIn₁
      StatementOut OStmtOut WitnessOut₁)
    (reduction₂ : OracleReduction oSpec Input Context Roles oracleDeco LocalStmt OStmtIn WitnessIn₂
      StatementOut OStmtOut WitnessOut₂) : Prop :=
  ∀ (i : Input) (s : StatementWithOracles LocalStmt OStmtIn i) (w : WitnessIn₁ i),
    (OracleReduction.mapExecuteWitness
      (oSpec := oSpec)
      (Context := Context)
      (Roles := Roles)
      (oracleDeco := oracleDeco)
      (LocalStmt := LocalStmt)
      (StatementOut := StatementOut)
      (OStmtOut := OStmtOut)
      (WitnessOut₁ := WitnessOut₁)
      (WitnessOut₂ := WitnessOut₂)
      (i := i)
      (s := s)
      (liftWitness := liftWitnessOut i s)) <$> reduction₁.executeConcrete i s w =
      reduction₂.executeConcrete i s (liftWitnessIn i s w)

end OracleReduction

/-- `toMonadDecoration` distributes over `Spec.append`: the monad decoration for
the appended spec equals `Decoration.append` of the individual monad decorations,
where the second phase starts from the accumulated oracle spec of the first. -/
theorem toMonadDecoration_append
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)] :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
    toMonadDecoration oSpec OStmtIn (spec₁.append spec₂)
      (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂) accSpec =
    Spec.Decoration.append (toMonadDecoration oSpec OStmtIn spec₁ roles₁ od₁ accSpec)
      (fun tr₁ => toMonadDecoration oSpec OStmtIn (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁)
        (accSpecAfter spec₁ roles₁ od₁ accSpec tr₁).2)
  | .done, _, _, _, _, _, _, _ => rfl
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨oi, odRest⟩, od₂, _, accSpec => by
      simp only [Spec.append, PFunctor.FreeM.append, toMonadDecoration,
        Spec.Decoration.append, PFunctor.FreeM.Displayed.Decoration.append,
        Role.Refine.append, accSpecAfter]
      congr 1; funext x
      exact toMonadDecoration_append (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩) _
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, _, accSpec => by
      simp only [Spec.append, PFunctor.FreeM.append, toMonadDecoration,
        Spec.Decoration.append, PFunctor.FreeM.Displayed.Decoration.append,
        Role.Refine.append, accSpecAfter]
      congr 1; funext x
      exact toMonadDecoration_append (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩) _

/-- Mapping the prover-side output of a strategy before execution is equivalent
to executing first and then mapping the prover component of the result. -/
theorem runWithOracleCounterpart_mapOutputWithRoles
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (inputImpl : QueryImpl [OStmtIn]ₒ Id)
    (spec : Spec) (roles : RoleDecoration spec) (od : OracleDecoration spec roles)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id)
    {OutputP OutputP' OutputC : Spec.Transcript spec → Type}
    (fP : ∀ tr, OutputP tr → OutputP' tr)
    (strat : Spec.Strategy.withRoles (OracleComp oSpec) spec roles OutputP)
    (cpt : Spec.Counterpart.withMonads spec roles
      (toMonadDecoration oSpec OStmtIn spec roles od accSpec) OutputC) :
    runWithOracleCounterpart inputImpl spec roles od accSpec accImpl
      (Spec.Strategy.mapOutputWithRoles fP strat) cpt =
      (fun z => ⟨z.1, fP z.1 z.2.1, z.2.2⟩) <$>
        runWithOracleCounterpart inputImpl spec roles od accSpec accImpl strat cpt := by
  let rec go
      (spec : Spec) (roles : RoleDecoration spec) (od : OracleDecoration spec roles)
      {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id)
      {OutputP OutputP' OutputC : Spec.Transcript spec → Type}
      (fP : ∀ tr, OutputP tr → OutputP' tr)
      (strat : Spec.Strategy.withRoles (OracleComp oSpec) spec roles OutputP)
      (cpt : Spec.Counterpart.withMonads spec roles
        (toMonadDecoration oSpec OStmtIn spec roles od accSpec) OutputC) :
      runWithOracleCounterpart inputImpl spec roles od accSpec accImpl
        (Spec.Strategy.mapOutputWithRoles fP strat) cpt =
        (fun z => ⟨z.1, fP z.1 z.2.1, z.2.2⟩) <$>
          runWithOracleCounterpart inputImpl spec roles od accSpec accImpl strat cpt := by
    match spec, roles, od with
    | .done, roles, od =>
        cases roles
        cases od
        simp [runWithOracleCounterpart, Spec.Strategy.mapOutputWithRoles,
          StrategyOver.TwoParty.Focal.mapOutput, ShapeOver.mapOutput,
          ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired,
          SyntaxOver.TwoParty.paired, PFunctor.Lens.id]
    | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩ =>
        simp only [Spec.Strategy.mapOutputWithRoles, Spec.Counterpart.mapReceiver,
          StrategyOver.TwoParty.Focal.mapOutput, ShapeOver.mapOutput,
          ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired,
          SyntaxOver.TwoParty.paired, PFunctor.Lens.id,
          runWithOracleCounterpart, bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
        refine congrArg (fun k => strat >>= k) ?_
        funext xc
        let addPrefix :
            ((tr : Spec.Transcript (rest xc.1)) ×
              (fun tr => OutputP' ⟨xc.1, tr⟩) tr ×
              (fun tr => OutputC ⟨xc.1, tr⟩) tr) →
            ((tr : Spec.Transcript (Spec.node _ rest)) × OutputP' tr × OutputC tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        calc
          addPrefix <$>
              runWithOracleCounterpart inputImpl (rest xc.1) (rRest xc.1) (odRest xc.1)
                (accSpec + @OracleInterface.spec _ oi)
                (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run xc.1))
                (Spec.Strategy.mapOutputWithRoles (fun tr => fP ⟨xc.1, tr⟩) xc.2)
                (cpt xc.1)
              = addPrefix <$> ((fun z => ⟨z.1, fP ⟨xc.1, z.1⟩ z.2.1, z.2.2⟩) <$>
                  runWithOracleCounterpart inputImpl (rest xc.1) (rRest xc.1)
                    (odRest xc.1) (accSpec + @OracleInterface.spec _ oi)
                    (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run xc.1))
                    xc.2 (cpt xc.1)) := by
                exact congrArg (fun z => addPrefix <$> z)
                  (go (rest xc.1) (rRest xc.1) (odRest xc.1)
                    (accSpec + @OracleInterface.spec _ oi)
                    (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run xc.1))
                    (fun tr => fP ⟨xc.1, tr⟩)
                    xc.2
                    (cpt xc.1))
          _ = (fun z => ⟨⟨xc.1, z.1⟩, fP ⟨xc.1, z.1⟩ z.2.1, z.2.2⟩) <$>
              runWithOracleCounterpart inputImpl (rest xc.1) (rRest xc.1) (odRest xc.1)
                (accSpec + @OracleInterface.spec _ oi)
                (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run xc.1))
                xc.2 (cpt xc.1) := by
                simp [addPrefix, Functor.map_map]
    | .node _ rest, ⟨.receiver, rRest⟩, odFn =>
        simp only [runWithOracleCounterpart, Spec.Strategy.mapOutputWithRoles,
          StrategyOver.TwoParty.Focal.mapOutput, ShapeOver.mapOutput,
          ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired,
          SyntaxOver.TwoParty.paired, PFunctor.Lens.id,
          bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
        let routeImpl :
            QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
          fun
          | .inl (.inl q) => liftM (oSpec.query q)
          | .inl (.inr q) => liftM (inputImpl q)
          | .inr q => liftM (accImpl q)
        refine congrArg (fun k => simulateQ routeImpl cpt >>= k) ?_
        funext xc
        refine congrArg (fun k => strat xc.1 >>= k) ?_
        funext next
        let addPrefix :
            ((tr : Spec.Transcript (rest xc.1)) ×
              (fun tr => OutputP' ⟨xc.1, tr⟩) tr ×
              (fun tr => OutputC ⟨xc.1, tr⟩) tr) →
            ((tr : Spec.Transcript (Spec.node _ rest)) × OutputP' tr × OutputC tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        calc
          addPrefix <$>
              runWithOracleCounterpart inputImpl (rest xc.1) (rRest xc.1) (odFn xc.1)
                accSpec accImpl
                (Spec.Strategy.mapOutputWithRoles (fun tr => fP ⟨xc.1, tr⟩) next)
                xc.2
              = addPrefix <$> ((fun z => ⟨z.1, fP ⟨xc.1, z.1⟩ z.2.1, z.2.2⟩) <$>
                  runWithOracleCounterpart inputImpl (rest xc.1) (rRest xc.1)
                    (odFn xc.1) accSpec accImpl next xc.2) := by
                exact congrArg (fun z => addPrefix <$> z)
                  (go (rest xc.1) (rRest xc.1) (odFn xc.1)
                    accSpec accImpl
                    (fun tr => fP ⟨xc.1, tr⟩)
                    next
                    xc.2)
          _ = (fun z => ⟨⟨xc.1, z.1⟩, fP ⟨xc.1, z.1⟩ z.2.1, z.2.2⟩) <$>
              runWithOracleCounterpart inputImpl (rest xc.1) (rRest xc.1) (odFn xc.1)
                accSpec accImpl next xc.2 := by
                simp [addPrefix, Functor.map_map]
  exact go spec roles od accSpec accImpl fP strat cpt

/-- Mapping the honest prover's private witness output after executing an oracle
reduction is equivalent to first mapping the honest prover output of its
strategy and then executing. -/
theorem OracleReduction.mapExecuteWitness_eq_execute_mappedOutput
    {ι : Type} {oSpec : OracleSpec ι}
    {Input : Type} {ιₛᵢ : Input → Type}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {oracleDeco : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt : Input → Type}
    {WitnessIn : Input → Type}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    {WitnessOut₁ WitnessOut₂ : (i : Input) → Spec.Transcript (Context i) → Type}
    (reduction : OracleReduction oSpec Input Context Roles oracleDeco LocalStmt OStmtIn WitnessIn
      StatementOut OStmtOut WitnessOut₁)
    (i : Input)
    (s : StatementWithOracles LocalStmt OStmtIn i)
    (w : WitnessIn i)
    (liftWitness : (tr : Spec.Transcript (Context i)) →
      WitnessOut₁ i tr → WitnessOut₂ i tr) :
    (OracleReduction.mapExecuteWitness
      (oSpec := oSpec)
      (Context := Context)
      (Roles := Roles)
      (oracleDeco := oracleDeco)
      (LocalStmt := LocalStmt)
      (StatementOut := StatementOut)
      (OStmtOut := OStmtOut)
      (WitnessOut₁ := WitnessOut₁)
      (WitnessOut₂ := WitnessOut₂)
      (i := i)
      (s := s)
      liftWitness) <$>
      reduction.executeConcrete i s w =
    (do
      let strategy ← reduction.prover i s w
      let a ←
        runWithOracleCounterpart
          (OracleInterface.simOracle0 (OStmtIn i) s.oracleStmt)
          (Context i) (Roles i) (oracleDeco i) []ₒ (fun q => q.elim)
          (Spec.Strategy.mapOutputWithRoles
            (fun tr out =>
              (⟨out.stmt, liftWitness tr out.wit⟩ :
                HonestProverOutput
                  (StatementWithOracles
                    (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i)
                  (WitnessOut₂ i tr)))
            strategy)
          (reduction.verifier i []ₒ s.stmt)
      pure
        ((⟨a.1, a.2.1, ⟨a.2.2, reduction.simulate i a.1⟩⟩ :
          (tr : Spec.Transcript (Context i)) ×
            HonestProverOutput
              (StatementWithOracles
                (fun _ => StatementOut i tr) (fun _ => OStmtOut i tr) i)
              (WitnessOut₂ i tr) ×
            (StatementOut i tr × QueryImpl [OStmtOut i tr]ₒ
              (OracleComp
                ([OStmtIn i]ₒ + toOracleSpec (Context i) (Roles i)
                  (oracleDeco i) tr)))))) := by
        simp [OracleReduction.executeConcrete, OracleReduction.mapExecuteWitness,
          runWithOracleCounterpart_mapOutputWithRoles, Functor.map_map]

/-- Mapping the verifier-side output of a monadic counterpart before execution
is equivalent to executing first and then mapping the verifier component of the
result. -/
theorem runWithOracleCounterpart_mapCounterpartOutput
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (inputImpl : QueryImpl [OStmtIn]ₒ Id)
    (spec : Spec) (roles : RoleDecoration spec) (od : OracleDecoration spec roles)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id)
    {OutputP OutputC OutputC' : Spec.Transcript spec → Type}
    (fC : ∀ tr, OutputC tr → OutputC' tr)
    (strat : Spec.Strategy.withRoles (OracleComp oSpec) spec roles OutputP)
    (cpt : Spec.Counterpart.withMonads spec roles
      (toMonadDecoration oSpec OStmtIn spec roles od accSpec) OutputC) :
    runWithOracleCounterpart inputImpl spec roles od accSpec accImpl
      strat
      (Spec.Counterpart.withMonads.mapOutput spec roles
        (toMonadDecoration oSpec OStmtIn spec roles od accSpec) fC cpt) =
      (fun z => ⟨z.1, z.2.1, fC z.1 z.2.2⟩) <$>
        runWithOracleCounterpart inputImpl spec roles od accSpec accImpl strat cpt := by
  let rec go
      (spec : Spec) (roles : RoleDecoration spec) (od : OracleDecoration spec roles)
      {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id)
      {OutputP OutputC OutputC' : Spec.Transcript spec → Type}
      (fC : ∀ tr, OutputC tr → OutputC' tr)
      (strat : Spec.Strategy.withRoles (OracleComp oSpec) spec roles OutputP)
      (cpt : Spec.Counterpart.withMonads spec roles
        (toMonadDecoration oSpec OStmtIn spec roles od accSpec) OutputC) :
      runWithOracleCounterpart inputImpl spec roles od accSpec accImpl
        strat
        (Spec.Counterpart.withMonads.mapOutput spec roles
          (toMonadDecoration oSpec OStmtIn spec roles od accSpec) fC cpt) =
        (fun z => ⟨z.1, z.2.1, fC z.1 z.2.2⟩) <$>
          runWithOracleCounterpart inputImpl spec roles od accSpec accImpl strat cpt := by
    match spec, roles, od with
    | .done, roles, od =>
        cases roles
        cases od
        rw [Spec.Counterpart.withMonads.mapOutput_done]
        simp [runWithOracleCounterpart]
    | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩ =>
        have hMap :
            Spec.Counterpart.withMonads.mapOutput
              (Spec.node _ rest) ⟨.sender, rRest⟩
              (toMonadDecoration oSpec OStmtIn (Spec.node _ rest) ⟨.sender, rRest⟩
                ⟨oi, odRest⟩ accSpec)
              fC cpt =
              fun x =>
                Spec.Counterpart.withMonads.mapOutput
                  (rest x) (rRest x)
                  (toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (odRest x)
                    (accSpec + @OracleInterface.spec _ oi))
                  (fun tr => fC ⟨x, tr⟩) (cpt x) := by
          rfl
        rw [hMap]
        simp only [runWithOracleCounterpart,
          bind_pure_comp, map_bind, Functor.map_map]
        refine congrArg (fun k => strat >>= k) ?_
        funext xc
        let addPrefix :
            ((tr : Spec.Transcript (rest xc.1)) ×
              (fun tr => OutputP ⟨xc.1, tr⟩) tr ×
              (fun tr => OutputC' ⟨xc.1, tr⟩) tr) →
            ((tr : Spec.Transcript (Spec.node _ rest)) × OutputP tr × OutputC' tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        calc
          addPrefix <$>
              runWithOracleCounterpart inputImpl (rest xc.1) (rRest xc.1) (odRest xc.1)
                (accSpec + @OracleInterface.spec _ oi)
                (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run xc.1)) xc.2
                (Spec.Counterpart.withMonads.mapOutput (rest xc.1) (rRest xc.1)
                  (toMonadDecoration oSpec OStmtIn (rest xc.1) (rRest xc.1)
                    (odRest xc.1) (accSpec + @OracleInterface.spec _ oi))
                  (fun tr => fC ⟨xc.1, tr⟩) (cpt xc.1))
              = addPrefix <$> ((fun z => ⟨z.1, z.2.1, fC ⟨xc.1, z.1⟩ z.2.2⟩) <$>
                  runWithOracleCounterpart inputImpl (rest xc.1) (rRest xc.1)
                    (odRest xc.1) (accSpec + @OracleInterface.spec _ oi)
                    (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run xc.1))
                    xc.2 (cpt xc.1)) := by
                exact congrArg (fun z => addPrefix <$> z)
                  (go (rest xc.1) (rRest xc.1) (odRest xc.1)
                    (accSpec + @OracleInterface.spec _ oi)
                    (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run xc.1))
                    (fun tr => fC ⟨xc.1, tr⟩)
                    xc.2
                    (cpt xc.1))
          _ = (fun z => ⟨⟨xc.1, z.1⟩, z.2.1, fC ⟨xc.1, z.1⟩ z.2.2⟩) <$>
              runWithOracleCounterpart inputImpl (rest xc.1) (rRest xc.1) (odRest xc.1)
                (accSpec + @OracleInterface.spec _ oi)
                (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run xc.1))
                xc.2 (cpt xc.1) := by
                simp [addPrefix, Functor.map_map]
    | .node _ rest, ⟨.receiver, rRest⟩, odFn =>
        let routeImpl :
            QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
          fun
          | .inl (.inl q) => liftM (oSpec.query q)
          | .inl (.inr q) => liftM (inputImpl q)
          | .inr q => liftM (accImpl q)
        let mapCpt :
            ((x : _) ×
              Spec.Counterpart.withMonads (rest x) (rRest x)
                (toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (odFn x) accSpec)
                (fun tr => OutputC ⟨x, tr⟩)) →
              ((x : _) ×
                Spec.Counterpart.withMonads (rest x) (rRest x)
                  (toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (odFn x) accSpec)
                  (fun tr => OutputC' ⟨x, tr⟩)) :=
          fun xc =>
            ⟨xc.1,
              Spec.Counterpart.withMonads.mapOutput
                (rest xc.1) (rRest xc.1)
                (toMonadDecoration oSpec OStmtIn (rest xc.1) (rRest xc.1)
                  (odFn xc.1) accSpec)
                (fun tr => fC ⟨xc.1, tr⟩) xc.2⟩
        have hSim : simulateQ routeImpl (mapCpt <$> cpt) =
            mapCpt <$> simulateQ routeImpl cpt :=
          simulateQ_map routeImpl mapCpt cpt
        have hMap :
            Spec.Counterpart.withMonads.mapOutput
              (Spec.node _ rest) ⟨.receiver, rRest⟩
              (toMonadDecoration oSpec OStmtIn (Spec.node _ rest) ⟨.receiver, rRest⟩
                odFn accSpec)
              fC cpt =
              mapCpt <$> cpt := by
          rfl
        rw [hMap]
        simp only [runWithOracleCounterpart]
        dsimp [routeImpl] at hSim
        change
          (simulateQ
            (fun x =>
              match x with
              | .inl (.inl q) => liftM (oSpec.query q)
              | .inl (.inr q) => liftM (inputImpl q)
              | .inr q => liftM (accImpl q))
            (mapCpt <$> cpt) >>= fun z' =>
              strat z'.1 >>= fun next =>
                runWithOracleCounterpart inputImpl (rest z'.1) (rRest z'.1)
                  (odFn z'.1) accSpec accImpl next z'.2 >>= fun z =>
                    pure
                      ((⟨⟨z'.1, z.1⟩, (z.2.1, z.2.2)⟩ :
                        (tr : Spec.Transcript (Spec.node _ rest)) ×
                          OutputP tr × OutputC' tr))) = _
        trans
          ((mapCpt <$>
            simulateQ
              (fun x =>
                match x with
                | .inl (.inl q) => liftM (oSpec.query q)
                | .inl (.inr q) => liftM (inputImpl q)
                | .inr q => liftM (accImpl q))
              cpt) >>= fun z' =>
                strat z'.1 >>= fun next =>
                  runWithOracleCounterpart inputImpl (rest z'.1) (rRest z'.1)
                    (odFn z'.1) accSpec accImpl next z'.2 >>= fun z =>
                      pure
                        ((⟨⟨z'.1, z.1⟩, (z.2.1, z.2.2)⟩ :
                          (tr : Spec.Transcript (Spec.node _ rest)) ×
                            OutputP tr × OutputC' tr)))
        · exact congrArg
            (fun m =>
              m >>= fun z' =>
                strat z'.1 >>= fun next =>
                  runWithOracleCounterpart inputImpl (rest z'.1) (rRest z'.1)
                    (odFn z'.1) accSpec accImpl next z'.2 >>= fun z =>
                      pure
                        ((⟨⟨z'.1, z.1⟩, (z.2.1, z.2.2)⟩ :
                          (tr : Spec.Transcript (Spec.node _ rest)) ×
                            OutputP tr × OutputC' tr)))
            hSim
        simp only [bind_map_left, bind_pure_comp, map_bind, Functor.map_map]
        refine congrArg (fun k => simulateQ routeImpl cpt >>= k) ?_
        funext xc
        refine congrArg (fun k => strat xc.1 >>= k) ?_
        funext next
        let addPrefix :
            ((tr : Spec.Transcript (rest xc.1)) ×
              (fun tr => OutputP ⟨xc.1, tr⟩) tr ×
              (fun tr => OutputC' ⟨xc.1, tr⟩) tr) →
            ((tr : Spec.Transcript (Spec.node _ rest)) × OutputP tr × OutputC' tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        calc
          addPrefix <$>
              runWithOracleCounterpart inputImpl (rest xc.1) (rRest xc.1) (odFn xc.1)
                accSpec accImpl next
                (Spec.Counterpart.withMonads.mapOutput (rest xc.1) (rRest xc.1)
                  (toMonadDecoration oSpec OStmtIn (rest xc.1) (rRest xc.1)
                    (odFn xc.1) accSpec)
                  (fun tr => fC ⟨xc.1, tr⟩) xc.2)
              = addPrefix <$> ((fun z => ⟨z.1, z.2.1, fC ⟨xc.1, z.1⟩ z.2.2⟩) <$>
                  runWithOracleCounterpart inputImpl (rest xc.1) (rRest xc.1)
                    (odFn xc.1) accSpec accImpl next xc.2) := by
                exact congrArg (fun z => addPrefix <$> z)
                  (go (rest xc.1) (rRest xc.1) (odFn xc.1)
                    accSpec accImpl
                    (fun tr => fC ⟨xc.1, tr⟩)
                    next
                    xc.2)
          _ = (fun z => ⟨⟨xc.1, z.1⟩, z.2.1, fC ⟨xc.1, z.1⟩ z.2.2⟩) <$>
              runWithOracleCounterpart inputImpl (rest xc.1) (rRest xc.1) (odFn xc.1)
                accSpec accImpl next xc.2 := by
                simp [addPrefix, Functor.map_map]
  exact go spec roles od accSpec accImpl fC strat cpt

/-- Public execution is just full honest execution with the prover's private
witness component erased afterwards. -/
theorem OracleReduction.executePublic_eq_map_execute
    {ι : Type} {oSpec : OracleSpec ι}
    {Input : Type} {ιₛᵢ : Input → Type}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {oracleDeco : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt WitnessIn : Input → Type}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    {WitnessOut : (i : Input) → Spec.Transcript (Context i) → Type}
    (reduction : OracleReduction oSpec Input Context Roles oracleDeco LocalStmt OStmtIn WitnessIn
      StatementOut OStmtOut WitnessOut)
    (i : Input) (s : StatementWithOracles LocalStmt OStmtIn i) (w : WitnessIn i) :
    reduction.executePublicConcrete i s w =
      (OracleReduction.forgetExecuteWitness
        (oSpec := oSpec)
        (Context := Context)
        (Roles := Roles)
        (oracleDeco := oracleDeco)
        (LocalStmt := LocalStmt)
        (StatementOut := StatementOut)
        (OStmtOut := OStmtOut)
        (WitnessOut := WitnessOut)
        (i := i)
        (s := s)) <$> reduction.executeConcrete i s w := by
  unfold OracleReduction.executePublicConcrete OracleReduction.executeConcrete
    OracleReduction.forgetExecuteWitness
  simp [runWithOracleCounterpart_mapOutputWithRoles]

/-- Honest execution equivalence implies honest public equivalence by erasing
the private prover witnesses. -/
theorem OracleReduction.HonestExecutionEquivalent.toPublic
    {ι : Type} {oSpec : OracleSpec ι}
    {Input : Type} {ιₛᵢ : Input → Type}
    {OStmtIn : (i : Input) → ιₛᵢ i → Type}
    [∀ i j, OracleInterface (OStmtIn i j)]
    {Context : Input → Spec}
    {Roles : (i : Input) → RoleDecoration (Context i)}
    {oracleDeco : (i : Input) → OracleDecoration (Context i) (Roles i)}
    {LocalStmt WitnessIn₁ WitnessIn₂ : Input → Type}
    {StatementOut : (i : Input) → Spec.Transcript (Context i) → Type}
    {ιₛₒ : (i : Input) → (tr : Spec.Transcript (Context i)) → Type}
    {OStmtOut : (i : Input) → (tr : Spec.Transcript (Context i)) → ιₛₒ i tr → Type}
    [∀ i tr j, OracleInterface (OStmtOut i tr j)]
    {WitnessOut₁ WitnessOut₂ : (i : Input) → Spec.Transcript (Context i) → Type}
    {liftWitnessIn :
      (i : Input) → StatementWithOracles LocalStmt OStmtIn i → WitnessIn₁ i → WitnessIn₂ i}
    {liftWitnessOut :
      (i : Input) → (s : StatementWithOracles LocalStmt OStmtIn i) →
      (tr : Spec.Transcript (Context i)) →
      WitnessOut₁ i tr → WitnessOut₂ i tr}
    {reduction₁ : OracleReduction oSpec Input Context Roles oracleDeco LocalStmt OStmtIn WitnessIn₁
      StatementOut OStmtOut WitnessOut₁}
    {reduction₂ : OracleReduction oSpec Input Context Roles oracleDeco LocalStmt OStmtIn WitnessIn₂
      StatementOut OStmtOut WitnessOut₂}
    (hEq : OracleReduction.HonestExecutionEquivalent
      liftWitnessIn liftWitnessOut reduction₁ reduction₂) :
    OracleReduction.HonestPubliclyEquivalent liftWitnessIn reduction₁ reduction₂ := by
  intro i s w
  have hForget :
      (OracleReduction.forgetExecuteWitness
        (oSpec := oSpec)
        (Context := Context)
        (Roles := Roles)
        (oracleDeco := oracleDeco)
        (LocalStmt := LocalStmt)
        (StatementOut := StatementOut)
        (OStmtOut := OStmtOut)
        (WitnessOut := WitnessOut₂)
        (i := i)
        (s := s)) ∘
        (OracleReduction.mapExecuteWitness
          (oSpec := oSpec)
          (Context := Context)
          (Roles := Roles)
          (oracleDeco := oracleDeco)
          (LocalStmt := LocalStmt)
          (StatementOut := StatementOut)
          (OStmtOut := OStmtOut)
          (WitnessOut₁ := WitnessOut₁)
          (WitnessOut₂ := WitnessOut₂)
          (i := i)
          (s := s)
          (liftWitness := liftWitnessOut i s)) =
      (OracleReduction.forgetExecuteWitness
        (oSpec := oSpec)
        (Context := Context)
        (Roles := Roles)
        (oracleDeco := oracleDeco)
        (LocalStmt := LocalStmt)
        (StatementOut := StatementOut)
        (OStmtOut := OStmtOut)
        (WitnessOut := WitnessOut₁)
        (i := i)
        (s := s)) := by
    funext z
    cases z
    rfl
  rw [OracleReduction.executePublic_eq_map_execute,
    OracleReduction.executePublic_eq_map_execute]
  simpa [Functor.map_map, Function.comp, hForget] using
    congrArg
      (Functor.map <|
        OracleReduction.forgetExecuteWitness
          (oSpec := oSpec)
        (Context := Context)
        (Roles := Roles)
        (oracleDeco := oracleDeco)
        (LocalStmt := LocalStmt)
        (StatementOut := StatementOut)
        (OStmtOut := OStmtOut)
        (WitnessOut := WitnessOut₂)
        (i := i)
        (s := s))
      (hEq i s w)

end OracleDecoration

/-! ## Execution for Oracle.Spec-based reductions -/

namespace Oracle

/-- Run a prover strategy against a verifier counterpart on `Oracle.Spec`,
threading accumulated oracle access. This is the `Oracle.Spec` analog of
`OracleDecoration.runWithOracleCounterpart`. -/
def Spec.runWithOracleCounterpart
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (inputImpl : QueryImpl [OStmtIn]ₒ Id) :
    (s : Spec) → (roles : Spec.RoleDeco s) → (od : Spec.OracleDeco s) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) → QueryImpl accSpec Id →
    {OutputP OutputC : Interaction.Spec.Transcript s.toInteractionSpec → Type} →
    Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
      s.toInteractionSpec (s.toSpecRoles roles) OutputP →
    Interaction.Spec.Counterpart.withMonads s.toInteractionSpec (s.toSpecRoles roles)
      (s.toMonadDecoration oSpec OStmtIn roles od accSpec) OutputC →
    OracleComp oSpec ((tr : Interaction.Spec.Transcript s.toInteractionSpec) ×
      OutputP tr × OutputC tr)
  | .done, _, _, _, _, _, _, _, output, cOutput =>
      pure ⟨⟨⟩, output, cOutput⟩
  | .«public» _ rest, ⟨.sender, rRest⟩, odRest, _, accSpec, accImpl, _, _,
      send, dualFn => do
      let ⟨x, next⟩ ← send
      let z ← runWithOracleCounterpart inputImpl
        (rest x) (rRest x) (odRest x) accSpec accImpl next (dualFn x)
      return ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
  | .«public» X rest, ⟨.receiver, rRest⟩, odRest, _, accSpec, accImpl, OutputP, OutputC,
      respond, dualSample => do
      let routeImpl : QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
        fun
        | .inl (.inl q) => liftM (oSpec.query q)
        | .inl (.inr q) => liftM (inputImpl q)
        | .inr q => liftM (accImpl q)
      have dualSample' : OracleComp ((oSpec + [OStmtIn]ₒ) + accSpec) _ := by
        simpa using dualSample
      let z' : Sigma (fun x =>
          Interaction.Spec.Counterpart.withMonads (rest x).toInteractionSpec
            ((rest x).toSpecRoles (rRest x))
            ((rest x).toMonadDecoration oSpec OStmtIn (rRest x) (odRest x) accSpec)
            (fun p => OutputC ⟨x, p⟩)) ←
        simulateQ routeImpl dualSample'
      let x := z'.1
      let dualRest := z'.2
      let next ← respond x
      let z ← runWithOracleCounterpart inputImpl
        (rest x) (rRest x) (odRest x) accSpec accImpl next dualRest
      return ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
  | .oracle _ rest, roles, ⟨oi, odRest⟩, _, accSpec, accImpl, _, _,
      send, dualFn => do
      let ⟨x, next⟩ ← send
      let implX : QueryImpl (@OracleInterface.spec _ oi) Id :=
        fun q => (oi.toOC.impl q).run x
      let z ← runWithOracleCounterpart inputImpl
        rest roles odRest (accSpec + @OracleInterface.spec _ oi)
        (QueryImpl.add accImpl implX) next (dualFn x)
      return ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩

/-- Execute an `Oracle.Reduction` against concrete oracle input statements.
Produces the realized transcript, prover output (statement + oracle statements +
witness), and verifier output (statement + output oracle simulation). -/
def Reduction.executeConcrete
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn shared) :
    OracleComp oSpec
      ((tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) ×
       HonestProverOutput
         (StatementWithOracles
           (fun _ => StatementOut shared ((Context shared).projectPublic tr))
           (fun _ => OStatementOut shared ((Context shared).projectPublic tr))
           shared)
         (WitnessOut shared ((Context shared).projectPublic tr)) ×
       (StatementOut shared ((Context shared).projectPublic tr) ×
        QueryImpl [OStatementOut shared ((Context shared).projectPublic tr)]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Context shared).toOracleSpec (OracleDeco shared)
                ((Context shared).projectPublic tr))))) := do
  let strategy ← reduction.prover shared s w
  let ⟨tr, proverOut, stmtOutV⟩ ←
    Spec.runWithOracleCounterpart
      (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt)
      (Context shared) (Roles shared) (OracleDeco shared) []ₒ (fun q => q.elim)
      strategy (reduction.verifier.toFun shared s.stmt)
  pure ⟨tr, proverOut,
    ⟨stmtOutV,
     reduction.verifier.simulate shared ((Context shared).projectPublic tr)⟩⟩

/-- Run an arbitrary prover strategy against an `Oracle.Verifier`, producing the
full transcript, prover output, and the verifier's statement output paired with
its output oracle simulation. This is the `Oracle.Spec` analog of
`OracleVerifier.run`. -/
def Verifier.run
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut)
    (shared : SharedIn)
    (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStatementIn shared]ₒ Id)
    {OutputP : Interaction.Spec.Transcript (Context shared).toInteractionSpec → Type}
    (prover : Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
      (Context shared).toInteractionSpec
      ((Context shared).toSpecRoles (Roles shared)) OutputP) :
    OracleComp oSpec
      ((tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) ×
       OutputP tr ×
       (StatementOut shared ((Context shared).projectPublic tr) ×
        QueryImpl [OStatementOut shared ((Context shared).projectPublic tr)]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Context shared).toOracleSpec (OracleDeco shared)
                ((Context shared).projectPublic tr))))) := do
  let ⟨tr, outP, stmtOutV⟩ ←
    Spec.runWithOracleCounterpart inputImpl
      (Context shared) (Roles shared) (OracleDeco shared) []ₒ (fun q => q.elim)
      prover (verifier.toFun shared stmt)
  pure ⟨tr, outP,
    ⟨stmtOutV,
     verifier.simulate shared ((Context shared).projectPublic tr)⟩⟩

/-- Mapping the prover-side output of a strategy before execution is equivalent
to executing first and then mapping the prover component of the result.
This is the `Oracle.Spec` analog of
`OracleDecoration.runWithOracleCounterpart_mapOutputWithRoles`. -/
theorem Spec.runWithOracleCounterpart_mapOutputWithRoles
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (inputImpl : QueryImpl [OStmtIn]ₒ Id) :
    (s : Spec) → (roles : Spec.RoleDeco s) → (od : Spec.OracleDeco s) →
    {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) → (accImpl : QueryImpl accSpec Id) →
    {OutputP OutputP' OutputC : Interaction.Spec.Transcript s.toInteractionSpec → Type} →
    (fP : ∀ tr, OutputP tr → OutputP' tr) →
    (strat : Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
      s.toInteractionSpec (s.toSpecRoles roles) OutputP) →
    (cpt : Interaction.Spec.Counterpart.withMonads s.toInteractionSpec (s.toSpecRoles roles)
      (s.toMonadDecoration oSpec OStmtIn roles od accSpec) OutputC) →
    Spec.runWithOracleCounterpart inputImpl s roles od accSpec accImpl
      (Interaction.Spec.Strategy.mapOutputWithRoles fP strat) cpt =
      (fun z => ⟨z.1, fP z.1 z.2.1, z.2.2⟩) <$>
        Spec.runWithOracleCounterpart inputImpl s roles od accSpec accImpl strat cpt := by
  intro s roles od ιₐ accSpec accImpl OutputP OutputP' OutputC fP strat cpt
  let rec go
      (s : Spec) (roles : Spec.RoleDeco s) (od : Spec.OracleDeco s)
      {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) (accImpl : QueryImpl accSpec Id)
      {OutputP OutputP' OutputC : Interaction.Spec.Transcript s.toInteractionSpec → Type}
      (fP : ∀ tr, OutputP tr → OutputP' tr)
      (strat : Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
        s.toInteractionSpec (s.toSpecRoles roles) OutputP)
      (cpt : Interaction.Spec.Counterpart.withMonads s.toInteractionSpec (s.toSpecRoles roles)
        (s.toMonadDecoration oSpec OStmtIn roles od accSpec) OutputC) :
      Spec.runWithOracleCounterpart inputImpl s roles od accSpec accImpl
        (Interaction.Spec.Strategy.mapOutputWithRoles fP strat) cpt =
        (fun z => ⟨z.1, fP z.1 z.2.1, z.2.2⟩) <$>
          Spec.runWithOracleCounterpart inputImpl s roles od accSpec accImpl strat cpt := by
    match s, roles, od with
    | .done, _, _ =>
        rfl
    | .«public» _X rest, ⟨.sender, rRest⟩, odRest =>
        simp only [Spec.toInteractionSpec, Spec.toSpecRoles,
          Interaction.Spec.Strategy.mapOutputWithRoles,
          Interaction.Spec.Counterpart.mapReceiver, Spec.runWithOracleCounterpart,
          StrategyOver.TwoParty.Focal.mapOutput, ShapeOver.mapOutput,
          ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired,
          SyntaxOver.TwoParty.paired, PFunctor.Lens.id,
          bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
        refine congrArg (fun k => strat >>= k) ?_
        funext ⟨x, next⟩
        let addPrefix :
            ((tr : Interaction.Spec.Transcript (rest x).toInteractionSpec) ×
              OutputP' ⟨x, tr⟩ × OutputC ⟨x, tr⟩) →
            ((tr : Interaction.Spec.Transcript
              (Oracle.Spec.public _X rest).toInteractionSpec) ×
              OutputP' tr × OutputC tr) :=
          fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
        calc
          addPrefix <$>
              runWithOracleCounterpart inputImpl (rest x) (rRest x) (odRest x)
                accSpec accImpl
                (Spec.Strategy.mapOutputWithRoles (fun tr => fP ⟨x, tr⟩) next)
                (cpt x)
              = addPrefix <$> ((fun z => ⟨z.1, fP ⟨x, z.1⟩ z.2.1, z.2.2⟩) <$>
                  runWithOracleCounterpart inputImpl (rest x) (rRest x) (odRest x)
                    accSpec accImpl next (cpt x)) := by
                exact congrArg (fun z => addPrefix <$> z)
                  (go (rest x) (rRest x) (odRest x) accSpec accImpl
                    (fun tr => fP ⟨x, tr⟩) next (cpt x))
          _ = (fun z => ⟨⟨x, z.1⟩, fP ⟨x, z.1⟩ z.2.1, z.2.2⟩) <$>
              runWithOracleCounterpart inputImpl (rest x) (rRest x) (odRest x)
                accSpec accImpl next (cpt x) := by
                simp [addPrefix, Functor.map_map]
    | .«public» _X rest, ⟨.receiver, rRest⟩, odRest =>
        simp only [Spec.toInteractionSpec, Spec.toSpecRoles, Spec.runWithOracleCounterpart,
          Interaction.Spec.Strategy.mapOutputWithRoles,
          StrategyOver.TwoParty.Focal.mapOutput, ShapeOver.mapOutput,
          ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired,
          SyntaxOver.TwoParty.paired, PFunctor.Lens.id,
          bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
        let routeImpl : QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
          fun
          | .inl (.inl q) => liftM (oSpec.query q)
          | .inl (.inr q) => liftM (inputImpl q)
          | .inr q => liftM (accImpl q)
        refine congrArg (fun k => simulateQ routeImpl cpt >>= k) ?_
        funext ⟨x, cptRest⟩
        refine congrArg (fun k => strat x >>= k) ?_
        funext next
        let addPrefix :
            ((tr : Interaction.Spec.Transcript (rest x).toInteractionSpec) ×
              OutputP' ⟨x, tr⟩ × OutputC ⟨x, tr⟩) →
            ((tr : Interaction.Spec.Transcript
              (Oracle.Spec.public _X rest).toInteractionSpec) ×
              OutputP' tr × OutputC tr) :=
          fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
        calc
          addPrefix <$>
              runWithOracleCounterpart inputImpl (rest x) (rRest x) (odRest x)
                accSpec accImpl
                (Spec.Strategy.mapOutputWithRoles (fun tr => fP ⟨x, tr⟩) next)
                cptRest
              = addPrefix <$> ((fun z => ⟨z.1, fP ⟨x, z.1⟩ z.2.1, z.2.2⟩) <$>
                  runWithOracleCounterpart inputImpl (rest x) (rRest x) (odRest x)
                    accSpec accImpl next cptRest) := by
                exact congrArg (fun z => addPrefix <$> z)
                  (go (rest x) (rRest x) (odRest x) accSpec accImpl
                    (fun tr => fP ⟨x, tr⟩) next cptRest)
          _ = (fun z => ⟨⟨x, z.1⟩, fP ⟨x, z.1⟩ z.2.1, z.2.2⟩) <$>
              runWithOracleCounterpart inputImpl (rest x) (rRest x) (odRest x)
                accSpec accImpl next cptRest := by
                simp [addPrefix, Functor.map_map]
    | .oracle _X rest, roles, ⟨oi, odRest⟩ =>
        simp only [Spec.toInteractionSpec, Spec.toSpecRoles,
          Interaction.Spec.Strategy.mapOutputWithRoles,
          Interaction.Spec.Counterpart.mapReceiver, Spec.runWithOracleCounterpart,
          StrategyOver.TwoParty.Focal.mapOutput, ShapeOver.mapOutput,
          ShapeOver.TwoParty.pairedSpec, ShapeOver.TwoParty.paired,
          SyntaxOver.TwoParty.paired, PFunctor.Lens.id,
          bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
        refine congrArg (fun k => strat >>= k) ?_
        funext ⟨x, next⟩
        let addPrefix :
            ((tr : Interaction.Spec.Transcript rest.toInteractionSpec) ×
              OutputP' ⟨x, tr⟩ × OutputC ⟨x, tr⟩) →
            ((tr : Interaction.Spec.Transcript
              (Oracle.Spec.oracle _X rest).toInteractionSpec) ×
              OutputP' tr × OutputC tr) :=
          fun a => ⟨⟨x, a.1⟩, a.2.1, a.2.2⟩
        calc
          addPrefix <$>
              runWithOracleCounterpart inputImpl rest roles odRest
                (accSpec + @OracleInterface.spec _ oi)
                (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run x))
                (Spec.Strategy.mapOutputWithRoles (fun tr => fP ⟨x, tr⟩) next)
                (cpt x)
              = addPrefix <$> ((fun z => ⟨z.1, fP ⟨x, z.1⟩ z.2.1, z.2.2⟩) <$>
                  runWithOracleCounterpart inputImpl rest roles odRest
                    (accSpec + @OracleInterface.spec _ oi)
                    (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run x))
                    next (cpt x)) := by
                exact congrArg (fun z => addPrefix <$> z)
                  (go rest roles odRest
                    (accSpec + @OracleInterface.spec _ oi)
                    (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run x))
                    (fun tr => fP ⟨x, tr⟩) next (cpt x))
          _ = (fun z => ⟨⟨x, z.1⟩, fP ⟨x, z.1⟩ z.2.1, z.2.2⟩) <$>
              runWithOracleCounterpart inputImpl rest roles odRest
                (accSpec + @OracleInterface.spec _ oi)
                (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run x))
                next (cpt x) := by
                simp [addPrefix, Functor.map_map]
  exact go s roles od accSpec accImpl fP strat cpt

end Oracle

end Interaction
