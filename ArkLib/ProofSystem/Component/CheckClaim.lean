/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge

/-!
  # Simple (Oracle) Reduction: Check if a predicate / claim on a statement is satisfied

  This is a zero-round (oracle) reduction. There is no witness.

  1. Reduction version: the input relation becomes a predicate `pred` on the statement. The verifier
     `guard`s on `pred` (failing the `OptionT` computation when it does not hold) and returns the
     same statement if successful. The output relation is trivial (`Set.univ`), since the predicate
     has been checked by the verifier at runtime.

  2. Oracle reduction version: **the verifier is a pure pass-through**. It returns the input
     statement and oracle statements unchanged and does *not* run any check at runtime; the checked
     predicate `P : Statement → (∀ i, OStatement i) → Prop` is instead carried by the output
     relation `oracleRelOut P relIn := relIn ∩ {x | P x.1.1 x.1.2}`. Acceptance is exactly
     membership in `oracleRelOut.language`, i.e. `P` holding.

  ## Why the oracle verifier is pure

  The oracle verifier takes no predicate argument, never fails, and is
  `OracleVerifier.toVerifier.IsPure` — which is what lets it be a left factor in a
  coordinate-wise-special-soundness / tree-soundness `append`. The predicate lives in
  `oracleRelOut` rather than in a runtime `guard`. The `guard`-based *plain* reduction above keeps
  its runtime check, since it can only ever be a rightmost factor.

  As a result, the oracle output relation is no longer trivial: it is `oracleRelOut P relIn`, which
  refines `relIn` by `P`. Completeness therefore holds under the explicit hypothesis that every
  `relIn` input already satisfies `P` (`oracleReduction_completeness`), and soundness is captured by
  `oracleVerifier_coordinateWiseSpecialSoundWith`.

  Note: with the pure pass-through oracle verifier (and the refactor to disallow failure in
  `OracleComp`), this oracle reduction is a special case of `ReduceClaim` (identity maps).
-/

open OracleComp OracleInterface ProtocolSpec Function

namespace CheckClaim

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)

section Reduction

/-- The prover for the `CheckClaim` reduction. -/
@[inline, specialize]
def prover : Prover oSpec Statement Unit Statement Unit !p[] where
  PrvState := fun _ => Statement
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun stmt => pure (stmt, ())

variable (pred : Statement → Prop) [DecidablePred pred]

/-- The verifier for the `CheckClaim` reduction. -/
@[inline, specialize]
def verifier : Verifier oSpec Statement Statement !p[] where
  verify := fun stmt _ => do guard (pred stmt); return stmt

/-- The reduction for the `CheckClaim` reduction. -/
@[inline, specialize]
def reduction : Reduction oSpec Statement Unit Statement Unit !p[] where
  prover := prover oSpec Statement
  verifier := verifier oSpec Statement pred

@[reducible, simp]
def relIn : Set (Statement × Unit) := { ⟨stmt, _⟩ | pred stmt }

@[reducible, simp]
def relOut : Set (Statement × Unit) := Set.univ

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the
  input relation, and the output relation being always true. -/
@[simp]
theorem reduction_completeness [Nonempty σ] [DecidableEq Statement] :
    (reduction oSpec Statement pred).perfectCompleteness init impl
    (relIn Statement pred) (relOut Statement) := by
  simp only [Reduction.perfectCompleteness, Reduction.completeness, ENNReal.coe_zero, tsub_zero]
  intro stmt () valid
  simp only [relIn, Set.mem_setOf_eq] at valid
  -- valid : pred stmt
  -- First simplify the reduction run
  have hrun : (reduction oSpec Statement pred).run stmt () =
      (pure ((default, stmt, ()), stmt) :
        OptionT (OracleComp _) _) := by
    simp [reduction, Reduction.run, prover, verifier, Prover.run, Verifier.run,
          Prover.runToRound, guard, if_pos valid]; rfl
  simp only [hrun]
  -- Now identical to id_perfectCompleteness pattern
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    -- Unfold OptionT.run on pure, then simulateQ_pure, then StateT
    change none ∈ _root_.support
      (StateT.run' (simulateQ _ (pure (some ((default, stmt, ()), stmt)) :
        OracleComp _ _)) s) at hmem
    rw [simulateQ_pure] at hmem
    change none ∈ _root_.support
      (Prod.fst <$> (pure (some ((default, stmt, ()), stmt)) :
        StateT σ ProbComp _).run s) at hmem
    rw [StateT.run_pure] at hmem
    simp [map_pure] at hmem
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ _root_.support
      (StateT.run' (simulateQ _ (pure (some ((default, stmt, ()), stmt)) :
        OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ _root_.support
      (Prod.fst <$> (pure (some ((default, stmt, ()), stmt)) :
        StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp [map_pure, support_pure] at hx
    cases hx
    simp [relOut]

/-- The knowledge state function for the `CheckClaim` reduction, mirroring the trivial-verifier
  template `Verifier.KnowledgeStateFunction.id`: at round `0` the state simply records that the
  input is in `relIn`. -/
def knowledgeStateFunction :
    (verifier oSpec Statement pred).KnowledgeStateFunction
      init impl (relIn Statement pred) (relOut Statement)
      (Extractor.RoundByRound.id (Witness := Unit)) where
  toFun | ⟨0, _⟩ => fun stmtIn _ witIn => (stmtIn, witIn) ∈ relIn Statement pred
  toFun_empty := fun _ _ => by simp
  toFun_next := fun i => Fin.elim0 i
  toFun_full := fun stmtIn tr _ h => by
    -- Reduce the dependent-pattern goal to `pred stmtIn`.
    change pred stmtIn
    by_contra hpred
    -- If `pred stmtIn` is false then `guard` fails and the OptionT computation always returns
    -- `none`, so no probability event can be positive.
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, _⟩ := h
    rw [OptionT.mem_support_iff] at hx
    -- Reduce the failing verifier by unfolding the `guard` branch.
    have hverify : (verifier oSpec Statement pred).run stmtIn tr =
        (OptionT.mk (pure none) : OptionT (OracleComp oSpec) Statement) := by
      simp only [Verifier.run, verifier]
      change (do guard (pred stmtIn); return stmtIn :
        OptionT (OracleComp oSpec) Statement) = _
      simp [guard, hpred]
      rfl
    rw [hverify] at hx
    -- Now `simulateQ impl (OptionT.mk (pure none))` has empty support.
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    rw [show ((OptionT.mk (pure none) : OptionT (OracleComp oSpec) Statement)) =
        ((pure none : OracleComp oSpec (Option Statement)) : _) from rfl] at hx
    rw [simulateQ_pure] at hx
    change some x ∈ _root_.support
      (Prod.fst <$> (pure none : StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp [map_pure, support_pure] at hx

/-- The `CheckClaim` reduction satisfies perfect round-by-round knowledge soundness. -/
theorem verifier_rbr_knowledge_soundness :
    (verifier oSpec Statement pred).rbrKnowledgeSoundness init impl
      (relIn Statement pred) (relOut Statement) 0 := by
  refine ⟨_, _, knowledgeStateFunction oSpec Statement pred (init := init) (impl := impl), ?_⟩
  intro stmtIn witIn prover i
  exact Fin.elim0 i.1

end Reduction

section OracleReduction

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]

/-- The oracle prover for the `CheckClaim` oracle reduction: it forwards the statement and all
oracle statements unchanged (there is no message and no witness). -/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Statement OStatement Unit Statement OStatement Unit !p[] where
  PrvState := fun _ => Statement × (∀ i, OStatement i)
  input := Prod.fst
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun stmt => pure (stmt, ())

/-- The oracle verifier for the `CheckClaim` oracle reduction is a **pure pass-through**: it
returns the statement and all oracle statements unchanged. The predicate
being checked is *not* run as an effectful `guard`/oracle computation here; instead it lives in the
output relation `oracleRelOut`. This keeps the verifier `IsPure` (so it can be a left factor in a
CWSS composition) and sidesteps the unfinished no-failure `OracleComp` refactor. (The `guard`-based
plain-reduction variant above is retained as a rightmost-only factor.) -/
def outputEmbedding : OracleOutputEmbedding OStatement (!p[] : ProtocolSpec 0).Message
    OStatement where
  embed := Function.Embedding.inl
  hEq := by
    intro i
    rw [show Function.Embedding.inl i = Sum.inl i from rfl]
  outputInterface_heq := by
    intro i
    rw [show Function.Embedding.inl i = Sum.inl i from rfl]

@[inline, specialize]
def oracleVerifier : OracleVerifier oSpec
    Statement OStatement Statement OStatement !p[] where
  verify := fun stmt _ => pure stmt
  outputOracle := .inl (outputEmbedding OStatement)

@[simp]
theorem oracleVerifier_materializeOutput (challenges : (!p[] : ProtocolSpec 0).Challenges)
    (oStmt : ∀ i, OStatement i) (messages : (!p[] : ProtocolSpec 0).Messages) :
    (oracleVerifier oSpec Statement OStatement).materializeOutput challenges oStmt messages =
      oStmt := by
  unfold OracleVerifier.materializeOutput oracleVerifier
  change OracleVerifier.materializeOutputOracle (Sum.inl (outputEmbedding OStatement))
      challenges oStmt messages = oStmt
  simp only [OracleVerifier.materializeOutputOracle]
  funext i
  simp only [outputEmbedding]
  rfl

/-- The oracle reduction for the `CheckClaim` oracle reduction. -/
@[inline, specialize]
def oracleReduction : OracleReduction oSpec
    Statement OStatement Unit Statement OStatement Unit !p[] where
  prover := oracleProver oSpec Statement OStatement
  verifier := oracleVerifier oSpec Statement OStatement

variable {Statement} {OStatement}

/-- The pure pass-through oracle verifier's underlying non-oracle verifier returns the combined
input statement unchanged. -/
theorem oracleVerifier_toVerifier_run {stmt : Statement} {oStmt : ∀ i, OStatement i}
    {tr : (!p[] : ProtocolSpec 0).FullTranscript} :
    (oracleVerifier oSpec Statement OStatement).toVerifier.run ⟨stmt, oStmt⟩ tr =
      pure ⟨stmt, oStmt⟩ := by
  simp only [Verifier.run, OracleVerifier.toVerifier]
  rw [oracleVerifier_materializeOutput]
  simp only [oracleVerifier]
  simp [OptionT.run_pure, simulateQ_pure]
  apply OptionT.ext
  rfl

/-- The `CheckClaim` oracle verifier is pure: its underlying verifier deterministically returns the
combined statement, which discharges the deterministic-left hypothesis of the CWSS binary append. -/
instance instIsPure : (oracleVerifier oSpec Statement OStatement).toVerifier.IsPure :=
  ⟨fun p _ => p, fun ⟨_, _⟩ _ => oracleVerifier_toVerifier_run (oSpec := oSpec)⟩

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
  (P : Statement → (∀ i, OStatement i) → Prop)
  (relIn : Set ((Statement × ∀ i, OStatement i) × Unit))

/-- The output relation of the pure-pass-through `CheckClaim`: the input relation intersected with
the checked predicate `P` on the combined statement. Because the verifier is a pure pass-through,
"acceptance" is exactly membership in `oracleRelOut.language`, i.e. `P` holding — so the check is
enforced by the relation rather than by a runtime `guard`. -/
@[reducible, simp]
def oracleRelOut : Set ((Statement × ∀ i, OStatement i) × Unit) :=
  relIn ∩ {x | P x.1.1 x.1.2}

/-- **Perfect completeness of the pure pass-through `CheckClaim` oracle reduction.** Because the
verifier does not check `P` at runtime (it is a pure pass-through, with `P` living in
`oracleRelOut`), completeness needs the explicit hypothesis `hP` that every `relIn` input already
satisfies `P`. Under `hP`, the prover forwards `⟨stmt, oStmt⟩` unchanged and the verifier returns it
deterministically, so the output `⟨⟨stmt, oStmt⟩, ()⟩` lies in `oracleRelOut P relIn = relIn ∩ {x |
P x.1.1 x.1.2}`. -/
@[simp]
theorem oracleReduction_completeness
    (hP : ∀ stmt oStmt, (⟨⟨stmt, oStmt⟩, ()⟩ : (Statement × ∀ i, OStatement i) × Unit) ∈ relIn →
      P stmt oStmt) :
    (oracleReduction oSpec Statement OStatement).perfectCompleteness init impl
      relIn (oracleRelOut P relIn) := by
  simp only [OracleReduction.perfectCompleteness, Reduction.perfectCompleteness,
    Reduction.completeness, ENNReal.coe_zero, tsub_zero]
  intro ⟨stmt, oStmt⟩ witIn hIn
  -- Reduce the run to a deterministic `pure` of the (unchanged) input.
  have hrun : (oracleReduction oSpec Statement OStatement).toReduction.run
      ⟨stmt, oStmt⟩ witIn =
      (pure ((default, ((stmt, oStmt), ())), (stmt, oStmt)) : OptionT (OracleComp _) _) := by
    simp only [oracleReduction, OracleReduction.toReduction, Reduction.run, oracleProver,
      oracleVerifier, OracleVerifier.toVerifier, Prover.run, Verifier.run, Prover.runToRound]
    rfl
  rw [hrun]
  rw [ge_iff_le, one_le_probEvent_iff, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    simp only [probFailure_eq_zero, zero_add]
    apply probOutput_eq_zero_of_not_mem_support
    simp only [support_bind, Set.mem_iUnion, not_exists]
    intro s _ hmem
    change none ∈ _root_.support
      (StateT.run' (simulateQ _ (pure (some ((default, ((stmt, oStmt), ())), (stmt, oStmt))) :
        OracleComp _ _)) s) at hmem
    rw [simulateQ_pure] at hmem
    change none ∈ _root_.support
      (Prod.fst <$> (pure (some ((default, ((stmt, oStmt), ())), (stmt, oStmt))) :
        StateT σ ProbComp _).run s) at hmem
    rw [StateT.run_pure] at hmem
    simp [map_pure] at hmem
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    change some x ∈ _root_.support
      (StateT.run' (simulateQ _ (pure (some ((default, ((stmt, oStmt), ())), (stmt, oStmt))) :
        OracleComp _ _)) s) at hx
    rw [simulateQ_pure] at hx
    change some x ∈ _root_.support
      (Prod.fst <$> (pure (some ((default, ((stmt, oStmt), ())), (stmt, oStmt))) :
        StateT σ ProbComp _).run s) at hx
    rw [StateT.run_pure] at hx
    simp [map_pure, support_pure] at hx
    cases hx
    exact ⟨⟨hIn, hP stmt oStmt hIn⟩, rfl⟩

/-- **Coordinate-wise special soundness of `CheckClaim`, named form.** The verifier is a pure
pass-through with no challenge rounds, so CWSS collapses (via the oracle no-challenge bridge
`coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx`) to a transcript-level obligation. The
named extractor is trivial (`fun _ _ _ => some ()`, there is no witness); since the pass-through
output equals the input and `oracleRelOut P relIn ⊆ relIn`, accepting into `oracleRelOut.language`
forces the input into `relIn`. Holds for any coordinate-wise structure `D`.

The extractor is **witnessing-agnostic** — it never consults its leaf witnessing — which is the
shape of a *closing* factor of a chain. -/
theorem oracleVerifier_coordinateWiseSpecialSoundWith
    (D : CWSSStructure (!p[] : ProtocolSpec 0)) :
    (oracleVerifier oSpec Statement OStatement).coordinateWiseSpecialSoundWith init impl D
      relIn
      (oracleRelOut P relIn)
      (fun _ _ _ => some ()) := by
  have h := OracleVerifier.coordinateWiseSpecialSoundWith_of_isEmpty_challengeIdx init impl
    D
    (oracleVerifier oSpec Statement OStatement) relIn (oracleRelOut P relIn) (fun _ _ => ())
    (fun s tr hAcc => by
      have hmem := Verifier.mem_of_pure_accepting init impl
        (oracleVerifier oSpec Statement OStatement).toVerifier s tr
        (oracleRelOut P relIn).language _ (oracleVerifier_toVerifier_run (oSpec := oSpec)) hAcc
      obtain ⟨_, hu⟩ := (Set.mem_language_iff _ _).1 hmem
      exact hu.1)
  exact h

end OracleReduction

end CheckClaim
