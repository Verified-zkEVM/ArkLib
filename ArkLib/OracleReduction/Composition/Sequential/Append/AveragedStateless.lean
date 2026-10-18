/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.Append.KnowledgeState
public import ArkLib.OracleReduction.Composition.Sequential.Append.ProverSuffix
public import ArkLib.OracleReduction.Composition.Sequential.Append.ProverPrefix
public import ArkLib.OracleReduction.Security.EmptyAmbient

/-! # Averaged knowledge-soundness composition with a stateless ambient oracle

An actual boundary state determines a suffix prover. Its prefix distribution, rather than
an arbitrary fixed transcript, is the distribution covered by averaged security.

Both composition theorems require a guarded first verifier and retain the component errors.
`append_rbrKnowledgeSoundnessAveraged_stateless` uses a fixed-prefix first-component bound.
`append_rbrKnowledgeSoundnessAveraged_of_averaged_stateless` instead accepts averaged bounds
for both components, with inhabited intermediate types for the restricted prefix prover.
Stateless ambient answers may be randomized, but cannot depend on persistent shared state.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
  {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ σ : Type} {m k : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec k}
  [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)]
  (init : ProbComp σ) (impl : QueryImpl oSpec ProbComp)
  {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
  {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
  {W₂ : Fin (k + 1) → Type}
  {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ W₂}

local notation "stateImpl" => impl.liftTarget (StateT σ ProbComp)

/-- Averaged tail security applies to the continuation from every fixed boundary state.
This bound still averages over the suffix prefix; it is not a fixed-prefix guarantee. -/
theorem averaged_suffix_bound_stateless
    (K₂ : V₂.KnowledgeStateFunction init stateImpl rel₂ rel₃ E₂)
    (ε₂ : pSpec₂.ChallengeIdx → ℝ≥0)
    (h₂ : V₂.rbrKnowledgeSoundnessAveragedWith init stateImpl rel₂ rel₃
      W₂ E₂ K₂ ε₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m))
    (state : P.PrvState ((0 : Fin (k + 1)).natAdd m))
    (stmt : Stmt₂) (wit : Wit₂) (i : pSpec₂.ChallengeIdx) :
    Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
         (P.runFromBoundary tr state i.1.castSucc)
       let c ← $ᵗ (pSpec₂.Challenge i)}[
      ∃ w, ¬ K₂ i.1.castSucc stmt (Prover.suffixTranscript x.1)
        (E₂.extractMid i.1 stmt ((Prover.suffixTranscript x.1).concat c) w) ∧
        K₂ i.1.succ stmt ((Prover.suffixTranscript x.1).concat c) w] ≤ ε₂ i := by
  have h := h₂ stmt wit (P.suffixFromState state) i
  rw [prEvent_rbrGame_statelessAmbient init impl (P.suffixFromState state) stmt wit i
    (fun T c => ∃ w, ¬ K₂ i.1.castSucc stmt T
      (E₂.extractMid i.1 stmt (T.concat c) w) ∧ K₂ i.1.succ stmt (T.concat c) w)] at h
  rw [Prover.prEvent_runFromBoundary_suffix_challenge
    impl P tr state i stmt wit
    (fun T c => ∃ w, ¬ K₂ i.1.castSucc stmt T
      (E₂.extractMid i.1 stmt (T.concat c) w) ∧ K₂ i.1.succ stmt (T.concat c) w)]
  exact h

/-- A distribution of boundary states preserves the same averaged tail error.
The intermediate statement may depend on the boundary transcript and private state. -/
theorem averaged_suffix_mixture_bound_stateless
    (K₂ : V₂.KnowledgeStateFunction init stateImpl rel₂ rel₃ E₂)
    (ε₂ : pSpec₂.ChallengeIdx → ℝ≥0)
    (h₂ : V₂.rbrKnowledgeSoundnessAveragedWith init stateImpl rel₂ rel₃
      W₂ E₂ K₂ ε₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (boundary : ProbComp ((pSpec₁ ++ₚ pSpec₂).Transcript
      ((0 : Fin (k + 1)).natAdd m) × P.PrvState ((0 : Fin (k + 1)).natAdd m)))
    (middle : ((pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m) ×
      P.PrvState ((0 : Fin (k + 1)).natAdd m)) → Stmt₂)
    (wit : Wit₂) (i : pSpec₂.ChallengeIdx) :
    Pr{let result ← (do
      let b ← boundary
      let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
        (P.runFromBoundary b.1 b.2 i.1.castSucc)
      let c ← $ᵗ (pSpec₂.Challenge i)
      return (b, x, c))}[
      ∃ w, ¬ K₂ i.1.castSucc (middle result.1) (Prover.suffixTranscript result.2.1.1)
        (E₂.extractMid i.1 (middle result.1)
          ((Prover.suffixTranscript result.2.1.1).concat result.2.2) w) ∧
        K₂ i.1.succ (middle result.1)
          ((Prover.suffixTranscript result.2.1.1).concat result.2.2) w] ≤ ε₂ i := by
  apply _root_.prEvent_bind_le_of_forall_le
  intro b
  simpa only [bind_assoc, pure_bind] using
    averaged_suffix_bound_stateless init impl K₂ ε₂ h₂ P b.1 b.2 (middle b) wit i

omit [∀ i, SampleableType (pSpec₁.Challenge i)]
  [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- Along a supported continuation, a composed suffix failure is a tail failure for
the intermediate statement determined at the original boundary. -/
theorem append_badEvent_continuation_stateless
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    {rel₁ : Set (Stmt₁ × Wit₁)} {W₁ : Fin (m + 1) → Type}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ W₁}
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init stateImpl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init stateImpl rel₂ rel₃ E₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m))
    (state : P.PrvState ((0 : Fin (k + 1)).natAdd m))
    (stmt : Stmt₁) (i : pSpec₂.ChallengeIdx)
    (x : (pSpec₁ ++ₚ pSpec₂).Transcript (i.1.castSucc.natAdd m) ×
      P.PrvState (i.1.castSucc.natAdd m))
    (hx : x ∈ support (P.runFromBoundary tr state i.1.castSucc))
    (c : (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))
    (hbad : ∃ w, ¬ KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
      (i.1.natAdd m).castSucc stmt x.1
      ((E₁.append E₂ G.out).extractMid (i.1.natAdd m) stmt (x.1.concat c) w) ∧
      KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
        (i.1.natAdd m).succ stmt (x.1.concat c) w) :
    let mid := G.out stmt (Prover.boundaryTranscript tr)
    let T := Prover.suffixTranscript x.1
    let d := cast (challenge_append_inr i) c
    ∃ w, ¬ K₂ i.1.castSucc mid T (E₂.extractMid i.1 mid (T.concat d) w) ∧
      K₂ i.1.succ mid (T.concat d) w := by
  have h := KnowledgeStateFunction.appendPredicate_badEvent_right
    init stateImpl G K₁ K₂ i.1 stmt x.1 c hbad
  have hb := P.runFromBoundary_preserves_boundary tr state i.1.castSucc x hx
  change (∃ w, ¬ K₂ i.1.castSucc (G.out stmt (Prover.boundaryTranscript x.1))
    (Prover.suffixTranscript x.1)
    (E₂.extractMid i.1 (G.out stmt (Prover.boundaryTranscript x.1))
      ((Prover.suffixTranscript x.1).concat (cast (challenge_append_inr i) c)) w) ∧
    K₂ i.1.succ (G.out stmt (Prover.boundaryTranscript x.1))
      ((Prover.suffixTranscript x.1).concat (cast (challenge_append_inr i) c)) w) at h
  rw [hb] at h
  exact h

/-- The composed bad-event probability in a fixed boundary continuation has the tail bound. -/
theorem append_continuation_bound_stateless
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    {rel₁ : Set (Stmt₁ × Wit₁)} {W₁ : Fin (m + 1) → Type}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ W₁}
    (G : V₁.GuardedForm)
    (K₁ : V₁.KnowledgeStateFunction init stateImpl rel₁ rel₂ E₁)
    (K₂ : V₂.KnowledgeStateFunction init stateImpl rel₂ rel₃ E₂)
    (ε₂ : pSpec₂.ChallengeIdx → ℝ≥0)
    (h₂ : V₂.rbrKnowledgeSoundnessAveragedWith init stateImpl rel₂ rel₃
      W₂ E₂ K₂ ε₂)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript ((0 : Fin (k + 1)).natAdd m))
    (state : P.PrvState ((0 : Fin (k + 1)).natAdd m))
    (stmt : Stmt₁) (wit : Wit₂) (i : pSpec₂.ChallengeIdx) :
    Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
         (P.runFromBoundary tr state i.1.castSucc)
       let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))}[
      ∃ w, ¬ KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
        (i.1.natAdd m).castSucc stmt x.1
        ((E₁.append E₂ G.out).extractMid (i.1.natAdd m) stmt (x.1.concat c) w) ∧
        KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
          (i.1.natAdd m).succ stmt (x.1.concat c) w] ≤ ε₂ i := by
  let mid := G.out stmt (Prover.boundaryTranscript tr)
  let bad := fun (T : pSpec₂.Transcript i.1.castSucc) (c : pSpec₂.Challenge i) =>
    ∃ w, ¬ K₂ i.1.castSucc mid T (E₂.extractMid i.1 mid (T.concat c) w) ∧
      K₂ i.1.succ mid (T.concat c) w
  have ht := averaged_suffix_bound_stateless init impl K₂ ε₂ h₂ P tr state mid wit i
  have hc : Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
                 (P.runFromBoundary tr state i.1.castSucc)
               let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))}[
        bad (Prover.suffixTranscript x.1) (cast (challenge_append_inr i) c)] ≤ ε₂ i := by
    rw [← uniformSample_challenge_append_inr (pSpec₁ := pSpec₁) i] at ht
    simpa only [bind_map_left] using ht
  apply le_trans ?_ hc
  let samples := do
    let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
      (P.runFromBoundary tr state i.1.castSucc)
    let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i))
    return (x, c)
  have hm := _root_.prEvent_mono_of_support samples
    (fun z => ∃ w, ¬ KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
      (i.1.natAdd m).castSucc stmt z.1.1
      ((E₁.append E₂ G.out).extractMid (i.1.natAdd m) stmt (z.1.1.concat z.2) w) ∧
      KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
        (i.1.natAdd m).succ stmt (z.1.1.concat z.2) w)
    (fun z => bad (Prover.suffixTranscript z.1.1) (cast (challenge_append_inr i) z.2)) ?_
  · simpa only [samples, bind_assoc, pure_bind] using hm
  · intro z hz hb
    simp only [samples, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at hz
    obtain ⟨x, hx, c, _, heq⟩ := hz
    subst z
    exact append_badEvent_continuation_stateless init impl G K₁ K₂ P tr state stmt i x
      (support_simulateQ_statelessAmbient_subset impl _ hx) c hb

/-- Averaged first-component security bounds the projected prefix of any composed prover.
The supplied terminal output only makes the restricted prover well typed; it is never run. -/
theorem averaged_prefix_bound_stateless
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {rel₁ : Set (Stmt₁ × Wit₁)}
    {W₁ : Fin (m + 1) → Type}
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ W₁}
    (K₁ : V₁.KnowledgeStateFunction init stateImpl rel₁ rel₂ E₁)
    (ε₁ : pSpec₁.ChallengeIdx → ℝ≥0)
    (h₁ : V₁.rbrKnowledgeSoundnessAveragedWith init stateImpl rel₁ rel₂ W₁ E₁ K₁ ε₁)
    (P : Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂))
    (finish : P.PrvState ((Fin.last m).castLE (by omega)) → Stmt₂ × Wit₂)
    (stmt : Stmt₁) (wit : Wit₁) (i : pSpec₁.ChallengeIdx) :
    Pr{let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
         (P.runToRound (i.1.castAdd k).castSucc stmt wit)
       let c ← $ᵗ (pSpec₁.Challenge i)}[
      ∃ w, ¬ K₁ i.1.castSucc stmt (Prover.prefixTranscript x.1)
        (E₁.extractMid i.1 stmt ((Prover.prefixTranscript x.1).concat c) w) ∧
        K₁ i.1.succ stmt ((Prover.prefixTranscript x.1).concat c) w] ≤ ε₁ i := by
  have h := h₁ stmt wit (P.prefixWithOutput finish) i
  rw [prEvent_rbrGame_statelessAmbient init impl (P.prefixWithOutput finish) stmt wit i
    (fun T c => ∃ w, ¬ K₁ i.1.castSucc stmt T
      (E₁.extractMid i.1 stmt (T.concat c) w) ∧ K₁ i.1.succ stmt (T.concat c) w)] at h
  rw [Prover.prEvent_runToRound_prefix_challenge impl P finish stmt wit i
    (fun T c => ∃ w, ¬ K₁ i.1.castSucc stmt T
      (E₁.extractMid i.1 stmt (T.concat c) w) ∧ K₁ i.1.succ stmt (T.concat c) w)]
  exact h

/-- A stateless ambient oracle permits an averaged-only tail in guarded-first composition.
The first component retains its fixed-prefix certificate, and each component keeps its error. -/
theorem append_rbrKnowledgeSoundnessAveraged_stateless
    [Inhabited Wit₂]
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    {rel₁ : Set (Stmt₁ × Wit₁)}
    (G : V₁.GuardedForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init stateImpl rel₁ rel₂ ε₁)
    (h₂ : V₂.rbrKnowledgeSoundnessAveraged init stateImpl rel₂ rel₃
      ε₂) :
    (V₁.append V₂).rbrKnowledgeSoundnessAveraged
      init stateImpl rel₁ rel₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨W₁, E₁, K₁, h₁⟩ := h₁
  obtain ⟨W₂, E₂, K₂, h₂⟩ := h₂
  refine ⟨_, E₁.append E₂ G.out,
    K₁.appendGuarded init stateImpl G K₂, ?_⟩
  intro stmt wit P i
  rw [prEvent_rbrGame_statelessAmbient init impl P stmt wit i
    (fun T c => ∃ w, ¬ (K₁.appendGuarded init stateImpl G K₂)
        i.1.castSucc stmt T
      ((E₁.append E₂ G.out).extractMid i.1 stmt (T.concat c) w) ∧
      (K₁.appendGuarded init stateImpl G K₂)
        i.1.succ stmt (T.concat c) w)]
  obtain ⟨i, rfl⟩ := ChallengeIdx.sumEquiv.surjective i
  rcases i with i | i
  · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    have hb := _root_.prEvent_bind_le_of_forall_le
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
        (P.runToRound (ChallengeIdx.inl i).1.castSucc stmt wit))
      (fun x => do
        let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i))
        return ∃ w, ¬ KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
          (ChallengeIdx.inl i).1.castSucc stmt x.1
          ((E₁.append E₂ G.out).extractMid (ChallengeIdx.inl i).1 stmt
            (x.1.concat c) w) ∧
          KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
            (ChallengeIdx.inl i).1.succ stmt (x.1.concat c) w)
      (fun p => p) (fun x => by
        simpa only [bind_assoc, pure_bind] using
          KnowledgeStateFunction.appendGuarded_bound_left
            init stateImpl G K₁ K₂ ε₁ h₁
            stmt i x.1)
    simp only [bind_assoc, pure_bind] at hb
    convert hb using 1
    rfl
  · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    have hb := Prover.prEvent_runToRound_le_of_boundary
      impl P stmt wit i.1.castSucc
      ($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i)))
      (fun T c => ∃ w, ¬ KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
        (i.1.natAdd m).castSucc stmt T
        ((E₁.append E₂ G.out).extractMid (i.1.natAdd m) stmt (T.concat c) w) ∧
        KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
          (i.1.natAdd m).succ stmt (T.concat c) w)
      (fun tr state => append_continuation_bound_stateless init impl G K₁ K₂ ε₂ h₂ P
        tr state stmt default i)
    convert hb using 1
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Two averaged component bounds compose under stateless ambient simulation.
Inhabited intermediate types provide an unused terminal output for the restricted prefix prover.
The first verifier is guarded, and the original per-round errors are retained. -/
theorem append_rbrKnowledgeSoundnessAveraged_of_averaged_stateless
    [Inhabited Stmt₂] [Inhabited Wit₂]
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    {rel₁ : Set (Stmt₁ × Wit₁)}
    (G : V₁.GuardedForm)
    {ε₁ : pSpec₁.ChallengeIdx → ℝ≥0} {ε₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundnessAveraged init stateImpl rel₁ rel₂ ε₁)
    (h₂ : V₂.rbrKnowledgeSoundnessAveraged init stateImpl rel₂ rel₃
      ε₂) :
    (V₁.append V₂).rbrKnowledgeSoundnessAveraged
      init stateImpl rel₁ rel₃
      (Sum.elim ε₁ ε₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  obtain ⟨W₁, E₁, K₁, h₁⟩ := h₁
  obtain ⟨W₂, E₂, K₂, h₂⟩ := h₂
  refine ⟨_, E₁.append E₂ G.out,
    K₁.appendGuarded init stateImpl G K₂, ?_⟩
  intro stmt wit P i
  rw [prEvent_rbrGame_statelessAmbient init impl P stmt wit i
    (fun T c => ∃ w, ¬ (K₁.appendGuarded init stateImpl G K₂)
        i.1.castSucc stmt T
      ((E₁.append E₂ G.out).extractMid i.1 stmt (T.concat c) w) ∧
      (K₁.appendGuarded init stateImpl G K₂)
        i.1.succ stmt (T.concat c) w)]
  obtain ⟨i, rfl⟩ := ChallengeIdx.sumEquiv.surjective i
  rcases i with i | i
  · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    let finish : P.PrvState ((Fin.last m).castLE (by omega)) → Stmt₂ × Wit₂ :=
      fun _ => (default, default)
    have hpre := averaged_prefix_bound_stateless init impl K₁ ε₁ h₁ P finish stmt wit i
    rw [← uniformSample_challenge_append_inl (pSpec₂ := pSpec₂) i] at hpre
    simp only [bind_map_left] at hpre
    apply le_trans ?_ hpre
    let samples : ProbComp
        (((pSpec₁ ++ₚ pSpec₂).Transcript (i.1.castAdd k).castSucc ×
          P.PrvState (i.1.castAdd k).castSucc) ×
          (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i)) := do
      let x ← simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ ProbComp)
        (P.runToRound (i.1.castAdd k).castSucc stmt wit)
      let c ← $ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i))
      return (x, c)
    have hm := _root_.prEvent_mono samples
      (fun z => ∃ w, ¬ KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
        (ChallengeIdx.inl i).1.castSucc stmt z.1.1
        ((E₁.append E₂ G.out).extractMid (ChallengeIdx.inl i).1 stmt (z.1.1.concat z.2) w) ∧
        KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
          (ChallengeIdx.inl i).1.succ stmt (z.1.1.concat z.2) w)
      (fun z => ∃ w, ¬ K₁ i.1.castSucc stmt (Prover.prefixTranscript (j := i.1.castSucc) z.1.1)
        (E₁.extractMid i.1 stmt
          ((Prover.prefixTranscript (j := i.1.castSucc) z.1.1).concat
            (cast (challenge_append_inl i) z.2)) w) ∧
        K₁ i.1.succ stmt
          ((Prover.prefixTranscript (j := i.1.castSucc) z.1.1).concat
            (cast (challenge_append_inl i) z.2)) w)
      (by
        intro z hz
        convert KnowledgeStateFunction.appendPredicate_badEvent_left init stateImpl
          G K₁ K₂ (ChallengeIdx.inl i).1 i.1.isLt stmt z.1.1 z.2 hz using 1
        rfl)
    simp only [samples, bind_assoc, pure_bind] at hm
    convert hm using 1
    rfl
  · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    have hb := Prover.prEvent_runToRound_le_of_boundary
      impl P stmt wit i.1.castSucc
      ($ᵗ ((pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i)))
      (fun T c => ∃ w, ¬ KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
        (i.1.natAdd m).castSucc stmt T
        ((E₁.append E₂ G.out).extractMid (i.1.natAdd m) stmt (T.concat c) w) ∧
        KnowledgeStateFunction.appendPredicate init stateImpl G K₁ K₂
          (i.1.natAdd m).succ stmt (T.concat c) w)
      (fun tr state => append_continuation_bound_stateless init impl G K₁ K₂ ε₂ h₂ P
        tr state stmt default i)
    convert hb using 1
    rfl

end Verifier
