/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.KnowledgeState
public import ArkLib.OracleReduction.Composition.Sequential.Append.ProverSuffix
public import ArkLib.OracleReduction.Security.EmptyAmbient
public import ArkLib.OracleReduction.Composition.Sequential.Append.AveragedStateless

/-! # Averaged suffix security with an empty ambient oracle

An actual boundary state determines a suffix prover. Its prefix distribution, rather than
an arbitrary fixed transcript, is the distribution covered by averaged security.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ σ : Type} {m k : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec k}
  [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
  {V₂ : Verifier []ₒ Stmt₂ Stmt₃ pSpec₂}
  {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
  {W₂ : Fin (k + 1) → Type}
  {E₂ : Extractor.RoundByRound []ₒ Stmt₂ Wit₂ Wit₃ pSpec₂ W₂}

/-- Averaged tail security applies to the continuation from every fixed boundary state.
This bound still averages over the suffix prefix; it is not a fixed-prefix guarantee. -/
theorem averaged_suffix_bound_empty
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (ε₂ : pSpec₂.ChallengeIdx → ℝ≥0)
    (h₂ : V₂.rbrKnowledgeSoundnessAveragedWith init impl rel₂ rel₃ W₂ E₂ K₂ ε₂)
    (P : Prover []ₒ Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m))
    (state : P.PrvState ((0 : Fin (k + 1)).natAdd m))
    (stmt : Stmt₂) (wit : Wit₂) (i : pSpec₂.ChallengeIdx) :
    Pr{let x ← simulateQ emptyAmbientChallengeImpl
         (P.runFromBoundary tr state i.1.castSucc)
       let c ← $ᵗ (pSpec₂.Challenge i)}[
      ∃ w, ¬ K₂ i.1.castSucc stmt (Prover.suffixTranscript x.1)
        (E₂.extractMid i.1 stmt ((Prover.suffixTranscript x.1).concat c) w) ∧
        K₂ i.1.succ stmt ((Prover.suffixTranscript x.1).concat c) w] ≤ ε₂ i := by
  let base : QueryImpl []ₒ ProbComp := fun q => isEmptyElim q
  have himpl : impl = base.liftTarget (StateT σ ProbComp) := by
    funext q
    exact isEmptyElim q
  subst impl
  simpa only [emptyAmbientChallengeImpl] using
    averaged_suffix_bound_stateless init base K₂ ε₂ h₂ P tr state stmt wit i

/-- A distribution of boundary states preserves the same averaged tail error.
The intermediate statement may depend on the boundary transcript and private state. -/
theorem averaged_suffix_mixture_bound_empty
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (ε₂ : pSpec₂.ChallengeIdx → ℝ≥0)
    (h₂ : V₂.rbrKnowledgeSoundnessAveragedWith init impl rel₂ rel₃ W₂ E₂ K₂ ε₂)
    (P : Prover []ₒ Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (boundary : ProbComp ((pSpec₁ ++ₚ pSpec₂).Transcript
      ((0 : Fin (k + 1)).natAdd m) × P.PrvState ((0 : Fin (k + 1)).natAdd m)))
    (middle : ((pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m) ×
      P.PrvState ((0 : Fin (k + 1)).natAdd m)) → Stmt₂)
    (wit : Wit₂) (i : pSpec₂.ChallengeIdx) :
    Pr{let result ← (do
      let b ← boundary
      let x ← simulateQ emptyAmbientChallengeImpl
        (P.runFromBoundary b.1 b.2 i.1.castSucc)
      let c ← $ᵗ (pSpec₂.Challenge i)
      return (b, x, c))}[
      ∃ w, ¬ K₂ i.1.castSucc (middle result.1) (Prover.suffixTranscript result.2.1.1)
        (E₂.extractMid i.1 (middle result.1)
          ((Prover.suffixTranscript result.2.1.1).concat result.2.2) w) ∧
        K₂ i.1.succ (middle result.1)
          ((Prover.suffixTranscript result.2.1.1).concat result.2.2) w] ≤ ε₂ i := by
  let base : QueryImpl []ₒ ProbComp := fun q => isEmptyElim q
  have himpl : impl = base.liftTarget (StateT σ ProbComp) := by
    funext q
    exact isEmptyElim q
  subst impl
  simpa only [emptyAmbientChallengeImpl] using
    averaged_suffix_mixture_bound_stateless init base K₂ ε₂ h₂ P boundary middle wit i

omit [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- Along a supported continuation, a composed suffix failure is a tail failure for
the intermediate statement determined at the original boundary. -/
theorem append_badEvent_continuation
    {V₁ : Verifier []ₒ Stmt₁ Stmt₂ pSpec₁}
    {rel₁ : Set (Stmt₁ × Wit₁)} {W₁ : Fin (m + 1) → Type}
    {E₁ : Extractor.RoundByRound []ₒ Stmt₁ Wit₁ Wit₂ pSpec₁ W₁}
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (P : Prover []ₒ Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m))
    (state : P.PrvState ((0 : Fin (k + 1)).natAdd m))
    (stmt : Stmt₁) (i : pSpec₂.ChallengeIdx)
    (x : (pSpec₁ ++ₚ pSpec₂).Transcript (i.1.castSucc.natAdd m) ×
      P.PrvState (i.1.castSucc.natAdd m))
    (hx : x ∈ support (P.runFromBoundary tr state i.1.castSucc))
    (c : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))
    (hbad : ∃ w, ¬ KnowledgeStateFunction.appendPredicate init impl G K₁ K₂
      (i.1.natAdd m).castSucc stmt x.1
      ((E₁.append E₂ G.out).extractMid (i.1.natAdd m) stmt (x.1.concat c) w) ∧
      KnowledgeStateFunction.appendPredicate init impl G K₁ K₂
        (i.1.natAdd m).succ stmt (x.1.concat c) w) :
    let mid := G.out stmt (Prover.boundaryTranscript tr)
    let T := Prover.suffixTranscript x.1
    let d := cast (challenge_append_inr i) c
    ∃ w, ¬ K₂ i.1.castSucc mid T (E₂.extractMid i.1 mid (T.concat d) w) ∧
      K₂ i.1.succ mid (T.concat d) w := by
  let base : QueryImpl []ₒ ProbComp := fun q => isEmptyElim q
  have himpl : impl = base.liftTarget (StateT σ ProbComp) := by
    funext q
    exact isEmptyElim q
  subst impl
  simpa only [emptyAmbientChallengeImpl] using
    append_badEvent_continuation_stateless init base G K₁ K₂ P tr state stmt i x hx c hbad

/-- The composed bad-event probability in a fixed boundary continuation has the tail bound. -/
theorem append_continuation_bound_empty
    {V₁ : Verifier []ₒ Stmt₁ Stmt₂ pSpec₁}
    {rel₁ : Set (Stmt₁ × Wit₁)} {W₁ : Fin (m + 1) → Type}
    {E₁ : Extractor.RoundByRound []ₒ Stmt₁ Wit₁ Wit₂ pSpec₁ W₁}
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (ε₂ : pSpec₂.ChallengeIdx → ℝ≥0)
    (h₂ : V₂.rbrKnowledgeSoundnessAveragedWith init impl rel₂ rel₃ W₂ E₂ K₂ ε₂)
    (P : Prover []ₒ Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m))
    (state : P.PrvState ((0 : Fin (k + 1)).natAdd m))
    (stmt : Stmt₁) (wit : Wit₂) (i : pSpec₂.ChallengeIdx) :
    Pr{let x ← simulateQ emptyAmbientChallengeImpl
         (P.runFromBoundary tr state i.1.castSucc)
       let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))}[
      ∃ w, ¬ KnowledgeStateFunction.appendPredicate init impl G K₁ K₂
        (i.1.natAdd m).castSucc stmt x.1
        ((E₁.append E₂ G.out).extractMid (i.1.natAdd m) stmt (x.1.concat c) w) ∧
        KnowledgeStateFunction.appendPredicate init impl G K₁ K₂
          (i.1.natAdd m).succ stmt (x.1.concat c) w] ≤ ε₂ i := by
  let base : QueryImpl []ₒ ProbComp := fun q => isEmptyElim q
  have himpl : impl = base.liftTarget (StateT σ ProbComp) := by
    funext q
    exact isEmptyElim q
  subst impl
  simpa only [emptyAmbientChallengeImpl] using
    append_continuation_bound_stateless init base G K₁ K₂ ε₂ h₂ P tr state stmt wit i

/-- An empty ambient oracle permits an averaged-only tail in guarded-first composition.
The first component retains its fixed-prefix certificate, and each component keeps its error. -/
theorem append_rbrKnowledgeSoundnessAveraged_empty
    [Inhabited Wit₂]
    {V₁ : Verifier []ₒ Stmt₁ Stmt₂ pSpec₁}
    {rel₁ : Set (Stmt₁ × Wit₁)}
    (G : V₁.GuardedForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ ε₁)
    (h₂ : V₂.rbrKnowledgeSoundnessAveraged init impl rel₂ rel₃ ε₂) :
    (V₁.append V₂).rbrKnowledgeSoundnessAveraged init impl rel₁ rel₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  let base : QueryImpl []ₒ ProbComp := fun q => isEmptyElim q
  have himpl : impl = base.liftTarget (StateT σ ProbComp) := by
    funext q
    exact isEmptyElim q
  subst impl
  exact append_rbrKnowledgeSoundnessAveraged_stateless init base G h₁ h₂

end Verifier
