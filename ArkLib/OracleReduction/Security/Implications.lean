/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.StateRestoration
import ArkLib.OracleReduction.Salt
import ArkLib.OracleReduction.Security.SpecialSoundness
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness

/-!
# Implications between security notions

This file collects the implications between the various security notions.

For now, we only state the theorems. It's likely that we will split this file into multiple files in
a single `Implication` folder in the future, each file for the proof of a single implication.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Verifier

section Implications

/- TODO: add the following results
- `knowledgeSoundness` implies `soundness`
- `rbrSoundness` implies `soundness`
- `rbrKnowledgeSoundness` implies `rbrSoundness`
- `rbrKnowledgeSoundness` implies `knowledgeSoundness`

In other words, we have a lattice of security notions, with `knowledge` and `roundByRound` being
two strengthenings of soundness.
-/

/-- Knowledge soundness with knowledge error `knowledgeError < 1` implies soundness with the same
soundness error `knowledgeError`, and for the corresponding input and output languages. -/
theorem knowledgeSoundness_implies_soundness
    (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (knowledgeError : ℝ≥0) (hLt : knowledgeError < 1) :
      knowledgeSoundness init impl relIn relOut verifier knowledgeError →
        soundness init impl relIn.language relOut.language verifier knowledgeError := by
  simp only [knowledgeSoundness, ChallengeIdx, Challenge, QueryImpl.addLift_def,
    PFunctor.Handler.liftTarget_self, bind_pure_comp, OptionT.run_bind,
    OptionT.run_map, simulateQ_option_elimM, simulateQ_pure, simulateQ_map,
    StateT.run'_eq, OptionT.mk_bind, Option.mem_def, Prod.mk.eta, soundness,
    Set.language, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
    not_exists, forall_exists_index]
  intro extractor hKS WitIn' WitOut' witIn' prover stmtIn hStmtIn
  sorry
  -- have hKS' := hKS stmtIn witIn' prover
  -- clear hKS
  -- contrapose! hKS'
  -- constructor
  -- · convert hKS'; rename_i result
  --   obtain ⟨transcript, queryLog, stmtOut, witOut⟩ := result
  --   simp
  --   sorry
  -- · simp only [Set.language, Set.mem_setOf_eq, not_exists] at hStmtIn
  --   simp only [Functor.map, Seq.seq, PMF.bind_bind, Function.comp_apply, PMF.pure_bind, hStmtIn,
  --     PMF.bind_const, PMF.pure_apply, eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte,
  --     zero_add, ℝ≥0.coe_lt_one_iff, hLt]

/-- Round-by-round soundness with error `rbrSoundnessError` implies soundness with error
`∑ i, rbrSoundnessError i`, where the sum is over all rounds `i`. -/
theorem rbrSoundness_implies_soundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) :
      rbrSoundness init impl langIn langOut verifier rbrSoundnessError →
        soundness init impl langIn langOut verifier (∑ i, rbrSoundnessError i) := by sorry

/-- Round-by-round knowledge soundness with error `rbrKnowledgeError` implies round-by-round
soundness with the same error `rbrKnowledgeError`. -/
theorem rbrKnowledgeSoundness_implies_rbrSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrKnowledgeSoundness init impl relIn relOut rbrKnowledgeError) :
    verifier.rbrSoundness init impl relIn.language relOut.language rbrKnowledgeError := by
  classical
  unfold rbrKnowledgeSoundness at h
  obtain ⟨WitMid, extractor, kSF, hkSF⟩ := h
  by_cases hWout : Nonempty WitOut
  · unfold rbrSoundness
    refine ⟨kSF.toStateFunction init impl, ?_⟩
    intro stmtIn hStmtIn WitIn' WitOut' witIn' prover i
    by_cases hWin : Nonempty WitIn
    · let prover' : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec :=
        { PrvState := prover.PrvState
          input := fun _ => prover.input (stmtIn, witIn')
          sendMessage := prover.sendMessage
          receiveChallenge := prover.receiveChallenge
          output := fun st => do
            let out ← prover.output st
            return (out.1, Classical.choice hWout) }
      have hrun : prover'.runToRound i.1.castSucc stmtIn (Classical.choice hWin) =
          prover.runToRound i.1.castSucc stmtIn witIn' := by rfl
      have hrunlog : prover'.runWithLogToRound i.1.castSucc stmtIn (Classical.choice hWin) =
          prover.runWithLogToRound i.1.castSucc stmtIn witIn' := by
        unfold Prover.runWithLogToRound
        rw [hrun]
      let logGame := do
        let s ← init
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover'.runWithLogToRound i.1.castSucc stmtIn (Classical.choice hWin)
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge, proveQueryLog))).run' s
      let plainGame := do
        let s ← init
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn'
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge))).run' s
      have hmap : (fun x => (x.1, x.2.1)) <$> logGame = plainGame := by
        simp [logGame, plainGame, ← Prover.runWithLogToRound_discard_log_eq_runToRound, hrunlog]
        rfl
      have hk := hkSF stmtIn (Classical.choice hWin) prover' i
      change probEvent plainGame (fun x =>
        ¬ (∃ w, kSF i.1.castSucc stmtIn x.1 w) ∧
          ∃ w, kSF i.1.succ stmtIn (x.1.concat x.2) w) ≤ _
      change probEvent logGame (fun x => ∃ w,
        ¬ kSF i.1.castSucc stmtIn x.1
            (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) w) ∧
          kSF i.1.succ stmtIn (x.1.concat x.2.1) w) ≤ _ at hk
      calc
        _ = probEvent logGame (fun x =>
            ¬ (∃ w, kSF i.1.castSucc stmtIn x.1 w) ∧
              ∃ w, kSF i.1.succ stmtIn (x.1.concat x.2.1) w) := by
              rw [← hmap, probEvent_map]
              rfl
        _ ≤ probEvent logGame (fun x => ∃ w,
            ¬ kSF i.1.castSucc stmtIn x.1
                (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) w) ∧
              kSF i.1.succ stmtIn (x.1.concat x.2.1) w) := by
              apply probEvent_mono
              intro x hx hbad
              obtain ⟨hprev, w, hnext⟩ := hbad
              exact ⟨w, fun hw => hprev ⟨_, hw⟩, hnext⟩
        _ ≤ _ := hk
    · let extractToInput : (m : Fin (n + 1)) → Transcript m pSpec → WitMid m → WitIn :=
        Fin.induction
          (fun tr w => cast extractor.eqIn w)
          (fun m ih tr w =>
            ih (Fin.init tr) (extractor.extractMid m stmtIn tr w))
      let plainGame := do
        let s ← init
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn'
            let challenge ← liftComp (pSpec.getChallenge i) _
            return (transcript, challenge))).run' s
      change probEvent plainGame (fun x =>
        ¬ (∃ w, kSF i.1.castSucc stmtIn x.1 w) ∧
          ∃ w, kSF i.1.succ stmtIn (x.1.concat x.2) w) ≤ _
      have hz : probEvent plainGame (fun x =>
          ¬ (∃ w, kSF i.1.castSucc stmtIn x.1 w) ∧
            ∃ w, kSF i.1.succ stmtIn (x.1.concat x.2) w) = 0 := by
        rw [probEvent_eq_zero_iff]
        intro x hx hbad
        obtain ⟨hprev, w, hnext⟩ := hbad
        exact hWin ⟨extractToInput i.1.succ (x.1.concat x.2) w⟩
      rw [hz]
      exact zero_le
  · have hLangOut : relOut.language = ∅ := by
      ext stmtOut
      simp only [Set.language, Set.mem_image, Prod.exists, exists_and_right,
        exists_eq_right, Set.mem_empty_iff_false, iff_false]
      intro hex
      exact hWout ⟨hex.choose⟩
    let sF : verifier.StateFunction init impl relIn.language relOut.language :=
      { toFun := fun m stmtIn _ => m = 0 ∧ stmtIn ∈ relIn.language
        toFun_empty := by
          intro stmtIn
          simp only [true_and]
        toFun_next := by
          intro m hdir stmtIn tr hfalse msg htrue
          exact Fin.succ_ne_zero m htrue.1
        toFun_full := by
          intro stmtIn tr hfalse
          rw [hLangOut]
          rw [probEvent_eq_zero_iff]
          simp only [Set.mem_empty_iff_false, not_false_eq_true, implies_true] }
    unfold rbrSoundness
    refine ⟨sF, ?_⟩
    intro stmtIn hStmtIn WitIn' WitOut' witIn' prover i
    let plainGame := do
      let s ← init
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn'
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge))).run' s
    change probEvent plainGame (fun x =>
      ¬ ((i.1.castSucc = 0) ∧ stmtIn ∈ relIn.language) ∧
        ((i.1.succ = 0) ∧ stmtIn ∈ relIn.language)) ≤ _
    have hz : probEvent plainGame (fun x =>
        ¬ ((i.1.castSucc = 0) ∧ stmtIn ∈ relIn.language) ∧
          ((i.1.succ = 0) ∧ stmtIn ∈ relIn.language)) = 0 := by
      rw [probEvent_eq_zero_iff]
      intro x hx hbad
      exact Fin.succ_ne_zero i.1 hbad.2.1
    rw [hz]
    exact zero_le

/-- Round-by-round knowledge soundness with error `rbrKnowledgeError` implies knowledge soundness
with error `∑ i, rbrKnowledgeError i`, where the sum is over all rounds `i`. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) :
      rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError →
        knowledgeSoundness init impl relIn relOut verifier (∑ i, rbrKnowledgeError i) := by sorry

-- /-- Round-by-round soundness for a protocol implies state-restoration soundness for the same
-- protocol with arbitrary added non-empty salts. -/
-- theorem rbrSoundness_implies_srSoundness_addSalt
--     {init : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id)}
--     {impl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)}
--     (langIn : Set StmtIn) (langOut : Set StmtOut)
--     (verifier : Verifier oSpec StmtIn StmtOut pSpec)
--     (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0)
--     (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)] :
--       rbrSoundness init impl langIn langOut verifier rbrSoundnessError →
--         Verifier.StateRestoration.soundness init impl langIn langOut (verifier.addSalt Salt)
--           (∑ i, (rbrSoundnessError i)) := by sorry

-- /-- Round-by-round knowledge soundness for a protocol implies state-restoration
-- knowledge soundness for the same protocol with arbitrary added non-empty salts. -/
-- theorem rbrKnowledgeSoundness_implies_srKnowledgeSoundness_addSalt
--     {init : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id)}
--     {impl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp)}
--     (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
--     (verifier : Verifier oSpec StmtIn StmtOut pSpec)
--     (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0)
--     (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)] :
--       rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError →
--         Verifier.StateRestoration.knowledgeSoundness init impl relIn relOut
--           (verifier.addSalt Salt) (∑ i, rbrKnowledgeError i) := by sorry

/-- State-restoration soundness for a protocol with added salts implies state-restoration
soundness for the original protocol (with improved parameters?)
-/
theorem srSoundness_addSalt_implies_srSoundness_original
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)]
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn (pSpec.addSalt Salt)) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle StmtIn (pSpec.addSalt Salt)) Id) ProbComp))
    (srSoundnessError : ℝ≥0) :
      Verifier.StateRestoration.soundness srInit srImpl langIn langOut
        (verifier.addSalt Salt) srSoundnessError →
        Verifier.StateRestoration.soundness sorry sorry langIn langOut
          verifier srSoundnessError := by sorry

/-- State-restoration knowledge soundness for a protocol with added salts implies state-restoration
knowledge soundness for the original protocol with improved parameters. -/
theorem srKnowledgeSoundness_addSalt_implies_srKnowledgeSoundness_original
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (Salt : pSpec.MessageIdx → Type) [∀ i, Nonempty (Salt i)] [∀ i, Fintype (Salt i)]
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn (pSpec.addSalt Salt)) Id))
    (srImpl : QueryImpl oSpec
      (StateT (QueryImpl (srChallengeOracle StmtIn (pSpec.addSalt Salt)) Id) ProbComp))
    (srKnowledgeError : ℝ≥0) :
      Verifier.StateRestoration.knowledgeSoundness srInit srImpl relIn relOut
        (verifier.addSalt Salt) srKnowledgeError →
        Verifier.StateRestoration.knowledgeSoundness sorry sorry relIn relOut
          verifier srKnowledgeError := by sorry

/-- State-restoration soundness implies basic (straightline) soundness.

This theorem shows that state-restoration security is a strengthening of basic soundness.
The error is preserved in the implication. -/
theorem srSoundness_implies_soundness
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
    (srSoundnessError : ℝ≥0) :
      Verifier.StateRestoration.soundness srInit srImpl langIn langOut verifier srSoundnessError →
        soundness init impl langIn langOut verifier srSoundnessError := by
  sorry

/-- State-restoration knowledge soundness implies basic (straightline) knowledge soundness.

This theorem shows that state-restoration knowledge soundness is a strengthening of basic
knowledge soundness. The error is preserved in the implication. -/
theorem srKnowledgeSoundness_implies_knowledgeSoundness
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (srInit : ProbComp (QueryImpl (srChallengeOracle StmtIn pSpec) Id))
    (srImpl : QueryImpl oSpec (StateT (QueryImpl (srChallengeOracle StmtIn pSpec) Id) ProbComp))
    (srKnowledgeError : ℝ≥0) :
      Verifier.StateRestoration.knowledgeSoundness srInit srImpl relIn relOut
        verifier srKnowledgeError →
      knowledgeSoundness init impl relIn relOut verifier srKnowledgeError := by sorry

-- TODO: state that round-by-round security implies state-restoration security for protocol with
-- arbitrary added (non-empty?) salts

-- TODO: state that state-restoration security for added salts imply state-restoration security for
-- the original protocol (with some better parameters)

-- TODO: state that state-restoration security implies basic security

end Implications

end Verifier

/-! ## Coordinate-wise special soundness generalizes special soundness

Both `Verifier.specialSound` (`Security.SpecialSoundness`) and
`Verifier.coordinateWiseSpecialSound` (`Security.CoordinateWiseSpecialSoundness`) are *defined* as
instances of the shape-generic `Verifier.treeSpecialSound`, differing only in the challenge-tree
shape they fix:

* plain special soundness fixes `distinctShape k` — arity `kᵢ`, node predicate `Function.Injective`
  (the `kᵢ` sibling challenges are pairwise distinct);
* CWSS fixes `D.toShape` — arity `ℓᵢ·(kᵢ-1)+1`, node predicate `IsSpecialSoundFamily ℓᵢ kᵢ`.

For the canonical `ℓᵢ = 1` structure `CWSSStructure.ofSpecialSound k` the two shapes are *equal*
(`toShape_ofSpecialSound_eq_distinctShape`): the arity is `kᵢ` and `IsSpecialSoundFamily 1 kᵢ`
reduces to injectivity (`CoordinateWise.isSpecialSoundFamily_one_iff_injective`). The bridge
`Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff` is then immediate from that shape
equality. -/

/-- Heterogeneous congruence for `Function.Injective`: injectivity transports across an equality of
the domain type together with a heterogeneous equality of the functions. -/
private theorem heq_injective {A A' β : Type} (h : A = A') {f : A → β} {g : A' → β}
    (hfg : HEq f g) : HEq (Function.Injective f) (Function.Injective g) := by
  subst h; obtain rfl := eq_of_heq hfg; exact HEq.rfl

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The CWSS shape of the canonical `ℓᵢ = 1` structure `CWSSStructure.ofSpecialSound k` is exactly
the plain special-soundness shape `distinctShape k`. This is the structural heart of the equivalence
between CWSS and plain special soundness: both the arity (`1·(kᵢ-1)+1 = kᵢ`) and the node predicate
(`IsSpecialSoundFamily 1 kᵢ` vs. `Function.Injective`) agree. -/
theorem toShape_ofSpecialSound_eq_distinctShape (k : pSpec.ChallengeIdx → ℕ) (hk : ∀ i, 2 ≤ k i) :
    (CWSSStructure.ofSpecialSound k hk).toShape = distinctShape k := by
  have harity : (CWSSStructure.ofSpecialSound k hk).toShape.arity = (distinctShape k).arity := by
    funext i
    change 1 * (k i - 1) + 1 = k i
    have := hk i; omega
  refine ChallengeTreeShape.ext harity (Function.hfunext rfl (fun i i' hi => ?_))
  obtain rfl := eq_of_heq hi
  refine Function.hfunext (by rw [harity]) (fun c c' hc => ?_)
  refine HEq.trans (heq_of_eq (propext ?_)) (heq_injective (congrArg Fin (congrFun harity i)) hc)
  change CoordinateWise.IsSpecialSoundFamily 1 (k i)
      (fun j : Fin (1 * (k i - 1) + 1) =>
        (Equiv.funUnique (Fin 1) (pSpec.Challenge i)).symm (c j)) ↔ Function.Injective c
  rw [CoordinateWise.isSpecialSoundFamily_one_iff_injective]
  exact Equiv.comp_injective c (Equiv.funUnique (Fin 1) (pSpec.Challenge i)).symm

namespace Verifier

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Coordinate-wise special soundness generalizes special soundness.** Coordinate-wise special
soundness for the canonical `ℓᵢ = 1` structure `CWSSStructure.ofSpecialSound k` is *equivalent* to
plain `(k)`-special soundness for the same input and output relations. Both unfold to
`Verifier.treeSpecialSound` of a shape, and the two shapes are equal
(`toShape_ofSpecialSound_eq_distinctShape`), so the bridge is immediate. This is the
`coordinateWiseSpecialSound (ofSpecialSound k) ↔ specialSound k` bridge promised in
`Security.SpecialSoundness`: CWSS recovers `k`-special soundness in the single-coordinate case. -/
theorem coordinateWiseSpecialSound_ofSpecialSound_iff (k : pSpec.ChallengeIdx → ℕ)
    (hk : ∀ i, 2 ≤ k i)
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) :
    verifier.coordinateWiseSpecialSound (WitOut := WitOut) init impl
      (CWSSStructure.ofSpecialSound k hk) relIn relOut
      ↔ verifier.specialSound init impl k relIn relOut := by
  unfold Verifier.coordinateWiseSpecialSound Verifier.specialSound
  rw [toShape_ofSpecialSound_eq_distinctShape]

end Verifier

namespace OracleVerifier

open ProtocolSpec

variable {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ i, OracleInterface (OStmtOut i)]
  [∀ i, OracleInterface (pSpec.Message i)]

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- **Coordinate-wise special soundness vs. plain special soundness, oracle form.** The oracle-
reduction analogue of `Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff`, obtained by passing
to the underlying non-oracle verifier (both notions are defined via `OracleVerifier.toVerifier`). -/
theorem coordinateWiseSpecialSound_ofSpecialSound_iff (k : pSpec.ChallengeIdx → ℕ)
    (hk : ∀ i, 2 ≤ k i)
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :
    verifier.coordinateWiseSpecialSound (WitOut := WitOut) init impl
      (CWSSStructure.ofSpecialSound k hk) relIn relOut
      ↔ verifier.specialSound init impl k relIn relOut :=
  Verifier.coordinateWiseSpecialSound_ofSpecialSound_iff init impl k hk relIn relOut
    verifier.toVerifier

end OracleVerifier
