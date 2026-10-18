/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

module

public import ArkLib.ProofSystem.Sumcheck.Spec.CollisionBound
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProjectionTransport
public import ArkLib.OracleReduction.Security.GuardedTerminal
public import ArkLib.OracleReduction.Completeness

/-!
# Knowledge states for corrected Sumcheck

Before the verifier challenge, knowledge is the original sum claim. At the final
round it is the passing sum check together with the related output claim.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

namespace Sumcheck.Spec.SingleRound.Simple

variable {R : Type} [CommSemiring R] {deg m : ℕ} (D : Fin m ↪ R)
  {ι : Type} (oSpec : OracleSpec ι) [DecidableEq R] [SampleableType R]

/-- Sumcheck relations have the unit witness, retained at every round. -/
def unitExtractor : Extractor.RoundByRound oSpec
    (StmtIn R × ∀ i, OStmtIn R deg i) Unit Unit (pSpec R deg) (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ _ => ()
  extractOut := fun _ _ _ => ()

/-- Knowledge before the challenge is unchanged; final knowledge records actual acceptance. -/
def roundKnowledge {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (verifier R deg D oSpec).KnowledgeStateFunction init impl
      (inputRelation R deg D) (outputRelation R deg) (unitExtractor oSpec) where
  toFun := fun i => match i with
    | ⟨0, _⟩ => fun input _ _ => (input, ()) ∈ inputRelation R deg D
    | ⟨1, _⟩ => fun input _ _ => (input, ()) ∈ inputRelation R deg D
    | ⟨2, _⟩ => fun input tr _ =>
      (verifierGuardedForm R deg D oSpec).check input tr = true ∧
      ((verifierGuardedForm R deg D oSpec).out input tr, ()) ∈ outputRelation R deg
  toFun_empty := by intro input wit; cases wit; rfl
  toFun_next := by
    intro i hi input tr msg wit h
    fin_cases i
    · exact h
    · exact Direction.noConfusion hi
  toFun_full := by
    intro input tr wit h
    cases wit
    exact (Verifier.GuardedForm.related_output_pos_iff init impl
      (verifierGuardedForm R deg D oSpec) (outputRelation R deg) input tr ()).mp h

end Sumcheck.Spec.SingleRound.Simple

namespace Sumcheck.Spec.SingleRound

/-- The projected sum is exactly the multivariate suffix sum, independently of its target. -/
theorem projected_sum_eq {R : Type} [CommSemiring R] {n deg m : ℕ}
    (D : Fin m ↪ R) (i : Fin n) (stmt : StatementRound R n i.castSucc)
    (p : OracleStatement R n deg ()) :
    ∑ a ∈ Finset.univ.map D,
      (projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval a =
    ∑ x ∈ (Finset.univ.map D) ^ᶠ (n - i.val),
      p.val.eval (Fin.append stmt.challenges x ∘ Fin.cast (by simp)) := by
  let target := ∑ x ∈ (Finset.univ.map D) ^ᶠ (n - i.val),
    p.val.eval (Fin.append stmt.challenges x ∘ Fin.cast (by simp))
  have h := Sumcheck.Interaction.SingleRound.projected_sum_of_relationRound R n deg D i
    (⟨target, stmt.challenges⟩ : StatementRound R n i.castSucc) p (by rfl)
  have hlist := Multiset.sum_map_toList (Finset.univ.map D).1
    (fun a => (projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval a)
  exact hlist.symm.trans h

/-- Projection preserves and reflects the input relation, not just honest inputs. -/
theorem projected_input_iff {R : Type} [CommSemiring R] {n deg m : ℕ}
    (D : Fin m ↪ R) (i : Fin n) (stmt : StatementRound R n i.castSucc)
    (p : OracleStatement R n deg ()) :
    ((stmt.target, fun _ => projectedRoundPolynomial R n deg D i stmt.challenges p), ()) ∈
      Simple.inputRelation R deg D ↔
    ((stmt, fun _ => p), ()) ∈ relationRound R n deg D i.castSucc := by
  change (∑ a ∈ Finset.univ.map D,
    (projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval a) = stmt.target ↔ _
  rw [projected_sum_eq]
  rfl

/-- A claimed next target satisfies the outer relation exactly when it equals the
projected polynomial's evaluation. This does not assume that the target is honest. -/
theorem projected_output_iff {R : Type} [CommSemiring R] {n deg m : ℕ}
    (D : Fin m ↪ R) (i : Fin n) (stmt : StatementRound R n i.castSucc)
    (p : OracleStatement R n deg ()) (r target : R) :
    (((⟨target, Fin.snoc stmt.challenges r⟩ : StatementRound R n i.succ),
      fun _ => p), ()) ∈ relationRound R n deg D i.succ ↔
    (projectedRoundPolynomial R n deg D i stmt.challenges p).val.eval r = target := by
  have h := Sumcheck.Interaction.SingleRound.relationRound_projected_output
    R n deg D i stmt p r
  change (∑ x ∈ (Finset.univ.map D) ^ᶠ (n - i.succ.val),
    p.val.eval (Fin.append (Fin.snoc stmt.challenges r) x ∘ Fin.cast (by simp))) = _ at h
  change (∑ x ∈ (Finset.univ.map D) ^ᶠ (n - i.succ.val),
    p.val.eval (Fin.append (Fin.snoc stmt.challenges r) x ∘ Fin.cast (by simp))) = target ↔ _
  rw [h]

/-- The Sumcheck projection lens satisfies the knowledge-soundness transport laws. -/
theorem provedExtractorLens {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
    {n deg m : ℕ} (D : Fin m ↪ R) {ι : Type} (oSpec : OracleSpec ι) (i : Fin n) :
    Extractor.Lens.IsKnowledgeSound
      (relationRound R n deg D i.castSucc) (Simple.inputRelation R deg D)
      (relationRound R n deg D i.succ) (Simple.outputRelation R deg)
      ((Simple.oracleVerifier R deg D oSpec).toVerifier.compatStatement (oStmtLens R n deg D i))
      (fun _ _ => True) ⟨oStmtLens R n deg D i, Witness.InvLens.trivial⟩ where
  lift_knowledgeSound := by
    rintro ⟨stmt, oracle⟩ ⟨⟩ ⟨⟩ _ h
    exact (projected_input_iff D i stmt (oracle ())).mp h
  proj_knowledgeSound := by
    rintro ⟨stmt, oracle⟩ out ⟨⟩ ⟨tr, hsupport⟩ hrel
    rw [Simple.oracleVerifier_eq_verifier] at hsupport
    simp only [Verifier.run, Simple.verifier, Statement.Lens.proj, oStmtLens,
      OracleComp.guard_eq] at hsupport
    split at hsupport
    · have hout : out = (((tr 0).val.eval (show R from tr 1), tr 1),
          fun _ => projectedRoundPolynomial R n deg D i stmt.challenges (oracle ())) := by
        simpa using hsupport
      subst out
      exact (projected_output_iff D i stmt (oracle ()) (tr 1) _).mp hrel
    · simp at hsupport

end Sumcheck.Spec.SingleRound


namespace Sumcheck.Spec.SingleRound.Simple

/-- Fixed-prefix RBR knowledge soundness for corrected Sumcheck over a finite domain. -/
theorem verifier_fixedPrefix {R : Type} [CommRing R] [IsDomain R] [Fintype R]
    [DecidableEq R] [SampleableType R] {deg m : ℕ} (D : Fin m ↪ R)
    {ι : Type} (oSpec : OracleSpec ι) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (verifier R deg D oSpec).rbrKnowledgeSoundness init impl
      (inputRelation R deg D) (outputRelation R deg)
      (fun _ => (deg : ℝ≥0) / Fintype.card R) := by
  apply OracleReduction.rbrKnowledgeSoundness_of_2msg_PtoV_uniformChallenge
    rfl rfl _ _ _ _ (fun _ => Unit) (unitExtractor oSpec) (roundKnowledge D oSpec init impl)
  intro input q
  by_cases h : (input, ()) ∈ inputRelation R deg D
  · simp [rbrExtractionFailureEvent, roundKnowledge, unitExtractor, h]
  · have hb := guarded_output_bound D oSpec input q h
    convert hb using 1 <;>
      simp only [rbrExtractionFailureEvent, roundKnowledge, unitExtractor, h,
        verifierGuardedForm, outputRelation, Transcript.concat,
        FullTranscript.mk1, FullTranscript.mk2, Fin.snoc, Nat.reduceAdd, Nat.add_zero,
        Fin.vcons_fin_zero, Fin.vappend_zero, Fin.isValue, Challenge, StmtIn, OStmtIn,
        StmtOut, OStmtOut, Fin.castSucc_one, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
        bind_pure_comp, ne_eq, Nat.cast_eq_zero,
        Fintype.card_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_natCast,
        Fin.succ_one_eq_two, true_and, exists_const, Set.mem_ofPred_eq, decide_eq_true_eq,
        Finset.sum_map]
    rfl

/-- The executable oracle verifier inherits the same fixed-prefix bound. -/
theorem oracleVerifier_fixedPrefix {R : Type} [CommRing R] [IsDomain R] [Fintype R]
    [DecidableEq R] [SampleableType R] {deg m : ℕ} (D : Fin m ↪ R)
    {ι : Type} (oSpec : OracleSpec ι) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (oracleVerifier R deg D oSpec).toVerifier.rbrKnowledgeSoundness init impl
      (inputRelation R deg D) (outputRelation R deg)
      (fun _ => (deg : ℝ≥0) / Fintype.card R) := by
  rw [oracleVerifier_eq_verifier]
  exact verifier_fixedPrefix D oSpec init impl

end Sumcheck.Spec.SingleRound.Simple

namespace Sumcheck.Spec.SingleRound

/-- The multivariate Sumcheck round inherits the fixed-prefix bound through its proved lens. -/
theorem oracleVerifier_fixedPrefix {R : Type} [CommRing R] [IsDomain R] [Fintype R]
    [DecidableEq R] [SampleableType R] {n deg m : ℕ} (D : Fin m ↪ R)
    {ι : Type} (oSpec : OracleSpec ι) (i : Fin n) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (oracleVerifier R n deg D oSpec i).toVerifier.rbrKnowledgeSoundness init impl
      (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ)
      (fun _ => (deg : ℝ≥0) / Fintype.card R) := by
  exact OracleVerifier.liftContext_rbr_knowledgeSoundness
    (stmtLens := oStmtExecutableLens R n deg D i)
    (witLens := Witness.InvLens.trivial)
    (Simple.oracleVerifier R deg D oSpec)
    (liftContextOutput R n deg D oSpec i)
    (lensKS := by simpa using provedExtractorLens D oSpec i)
    (Simple.oracleVerifier_fixedPrefix D oSpec init impl)

end Sumcheck.Spec.SingleRound

namespace Sumcheck.Spec.SingleRound

section Averaged

variable {R : Type} [CommRing R] [IsDomain R] [Fintype R]
  [DecidableEq R] [SampleableType R] {n deg m : ℕ} (D : Fin m ↪ R)
  {ι : Type} (oSpec : OracleSpec ι) {σ : Type} (init : ProbComp σ)
  (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The simple verifier's averaged guarantee follows from its fixed-prefix guarantee.
The domain hypothesis is required by the polynomial collision bound. -/
theorem Simple.verifier_rbrKnowledgeSoundnessAveraged :
    (Simple.verifier R deg D oSpec).rbrKnowledgeSoundnessAveraged init impl
      (Simple.inputRelation R deg D) (Simple.outputRelation R deg)
      (fun _ => (deg : ℝ≥0) / Fintype.card R) :=
  Verifier.rbrKnowledgeSoundness_implies_rbrKnowledgeSoundnessAveraged init impl
    (Simple.verifier_fixedPrefix D oSpec init impl)

/-- The executable simple verifier has the same averaged error. -/
theorem Simple.oracleVerifier_rbrKnowledgeSoundnessAveraged :
    (Simple.oracleVerifier R deg D oSpec).rbrKnowledgeSoundnessAveraged init impl
      (Simple.inputRelation R deg D) (Simple.outputRelation R deg)
      (fun _ => (deg : ℝ≥0) / Fintype.card R) :=
  Verifier.rbrKnowledgeSoundness_implies_rbrKnowledgeSoundnessAveraged init impl
    (Simple.oracleVerifier_fixedPrefix D oSpec init impl)

/-- The lifted executable round inherits the same averaged error through the proved lens. -/
theorem oracleVerifier_rbrKnowledgeSoundnessAveraged (i : Fin n) :
    (oracleVerifier R n deg D oSpec i).rbrKnowledgeSoundnessAveraged init impl
      (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ)
      (fun _ => (deg : ℝ≥0) / Fintype.card R) :=
  Verifier.rbrKnowledgeSoundness_implies_rbrKnowledgeSoundnessAveraged init impl
    (oracleVerifier_fixedPrefix D oSpec i init impl)

/-- Ordinary and executable lifting give the same single-round security guarantee. -/
theorem verifier_rbrKnowledgeSoundnessAveraged (i : Fin n) :
    (verifier R n deg D oSpec i).rbrKnowledgeSoundnessAveraged init impl
      (relationRound R n deg D i.castSucc) (relationRound R n deg D i.succ)
      (fun _ => (deg : ℝ≥0) / Fintype.card R) := by
  have h := oracleVerifier_rbrKnowledgeSoundnessAveraged (deg := deg) D oSpec init impl i
  unfold OracleVerifier.rbrKnowledgeSoundnessAveraged oracleVerifier at h
  rw [OracleVerifier.liftContext_toVerifier_comm, Simple.oracleVerifier_eq_verifier] at h
  exact h

end Averaged

end Sumcheck.Spec.SingleRound
