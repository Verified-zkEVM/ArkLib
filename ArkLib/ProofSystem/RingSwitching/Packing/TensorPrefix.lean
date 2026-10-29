/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.RingSwitch
public import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
public import ArkLib.ProofSystem.RingSwitching.Packing.Compatibility
public import ArkLib.ProofSystem.RingSwitching.Packing.BatchingAlgebra
public import ArkLib.ProofSystem.RingSwitching.Packing.FinalAlgebra

/-!
# Prefix ring switching through the shared protocol

DP24 packs the leading Boolean variables in the profile basis. The transmitted first message
has the original carrier type `P.A`: its column equivalence decodes the component evaluations.
The sampled batching challenge remains `L^κ`; the shared scalar rounds and matrix terminal
check then reduce to an evaluation of the same committed packed polynomial.

Operational definitions use the equality-fold rule over commutative rings. Collision bounds
use its separately certified strategy and no-zero-divisors hypothesis. Commitment compatibility
is a relation, with no honest coverage assumption in the security theorem. The head collision
law needs only equality of compatible carrier evaluations at the fixed query; full round-by-round
security also uses uniqueness of the packed polynomial through sumcheck.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over Binary
  Towers*][DP24], Construction 3.1.
-/

@[expose] public section

noncomputable section
namespace RingSwitching.Packing.TensorPrefix
open Module MvPolynomial ProtocolSpec OracleSpec OracleComp Sumcheck.Structured
  Probability ProbabilityTheory
open scoped NNReal ENNReal

variable {K L : Type} [CommRing K] [CommRing L] [Algebra K L]
  {κ ℓ ℓ' : ℕ} (P : RingSwitchingProfile K L κ) (h_l : ℓ = ℓ' + κ)

/-- Prefix packing with the original source dimension and evaluation query. -/
def layout : ClaimLayout (PackingData.ofBasis P.basis) ℓ' where
  Source := MultilinearPoly K ℓ
  Query := Fin ℓ → L
  components := (sourceDimensionEquiv h_l).trans (splitFirstEquiv κ ℓ')
  point := getEvaluationPointSuffix κ L ℓ ℓ' h_l
  weight r v := eqTilde (v : Fin κ → L) (fun i => r ⟨i.val, by omega⟩)
  eval r t := aeval r t.val
  reconstruct q p := aeval_eq_sum_splitFirst h_l p q

/-- Compatibility with the original packed-polynomial oracle statement. -/
abbrev commitment (a : AbstractOStmtIn L ℓ') : PackedCommitment L ℓ' :=
  a.toPackedCommitment

/-- Functional oracle compatibility is exactly the shared binding assumption. -/
theorem commitment_functional (a : AbstractOStmtIn L ℓ') (h : a.Functional) :
    (commitment a).Functional := fun h₁ h₂ => h _ _ _ h₁ h₂

/-- The original carrier is encoded by its column coordinates. -/
def messageEquiv : P.A ≃ ((Fin κ → Fin 2) → L) := P.columnEquiv.toEquiv

/-- The scalar relation on the original query and source polynomial. -/
abbrev relIn (a : AbstractOStmtIn L ℓ') :=
  Head.relIn (PackingData.ofBasis P.basis) ℓ' (layout P h_l) (commitment a)

section Program
variable [SampleableType L] (a : AbstractOStmtIn L ℓ')

/-- The unchanged carrier/challenge wire followed by the shared scalar rounds. -/
abbrev pSpec := RingSwitch.pSpec (M := P.A) (PackingData.ofBasis P.basis) ℓ'
  (BatchingRule.eqFold L κ)

/-- The verifier is an instance of the shared ring-switching verifier. -/
def verifier := RingSwitch.verifier (PackingData.ofBasis P.basis) ℓ' (layout P h_l)
  (messageEquiv P) (BatchingRule.eqFold L κ) (commitment a)

/-- The prover and verifier are an instance of the shared reduction. -/
def reduction := RingSwitch.reduction (PackingData.ofBasis P.basis) ℓ' (layout P h_l)
  (messageEquiv P) (BatchingRule.eqFold L κ) (commitment a)

/-- Using strict compatibility leaves the verifier unchanged. -/
theorem verifier_strictView_eq : verifier P h_l a.strictView = verifier P h_l a := rfl

/-- Using strict compatibility leaves the prover and verifier unchanged. -/
theorem reduction_strictView_eq : reduction P h_l a.strictView = reduction P h_l a := rfl

/-- Every valid initial claim completes on the same commitment, at every oracle state. -/
theorem perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction P h_l a).perfectCompleteness init impl (relIn P h_l a)
      ((commitment a).evalRelWithContext ((Fin ℓ → L) × (Fin κ → L))) :=
  RingSwitch.perfectCompleteness (PackingData.ofBasis P.basis) ℓ' (layout P h_l)
    (messageEquiv P) (BatchingRule.eqFold L κ) (commitment a) init impl

omit [SampleableType L] in
/-- The head verifier decodes the original carrier before the original scalar check. -/
theorem check_iff [DecidableEq L] (r : Fin ℓ → L) (s : L) (z : P.A) :
    Head.check (PackingData.ofBasis P.basis) ℓ' (layout P h_l) (r, s)
        (messageEquiv P z) ↔
      performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l s r z = true := by
  unfold performCheckOriginalEvaluation
  rw [decide_eq_true_iff, eqWeightedCoordSum_eq_sum]
  rfl

/-- The shared batching target is the original row-coordinate target. -/
theorem derivedTarget_messageEquiv_eq_compute_s0 (z : P.A) (c : Fin κ → L) :
    (PackingData.ofBasis P.basis).derivedTarget (messageEquiv P z)
        ((BatchingRule.eqFold L κ).weight c) = compute_s0 κ L K P z c := by
  change (PackingData.ofBasis P.basis).derivedTarget (P.decomposeColumns z)
    (fun u => eqTilde (u : Fin κ → L) c) = _
  rw [compute_s0_eq_sum, PackingData.derivedTarget, P.transpose_decomposeColumns]
  rfl

open scoped Classical in
/-- The shared head executes the original carrier check and row target. -/
theorem head_verifier_eq [DecidableEq L] :
    Head.verifier (PackingData.ofBasis P.basis) ℓ' (layout P h_l)
        (messageEquiv P) (BatchingRule.eqFold L κ) (commitment a) =
      scalarRoundOracleVerifier (oSpec := []ₒ) (OStmt := (commitment a).OStmt)
        (fun stmt z => performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l stmt.2 stmt.1 z = true)
        (fun stmt z c => (⟨(stmt.1, c), Fin.elim0, compute_s0 κ L K P z c⟩ :
          Head.Output (PackingData.ofBasis P.basis) ℓ' (layout P h_l)
            (BatchingRule.eqFold L κ))) := by
  unfold Head.verifier
  congr 1
  · funext stmt z
    exact propext (check_iff P h_l stmt.1 stmt.2 z)
  · funext stmt z c
    change (⟨(stmt.1, c), Fin.elim0, _⟩ : Head.Output
      (PackingData.ofBasis P.basis) ℓ' (layout P h_l) (BatchingRule.eqFold L κ)) = _
    exact congrArg (fun t => (⟨(stmt.1, c), Fin.elim0, t⟩ : Head.Output
      (PackingData.ofBasis P.basis) ℓ' (layout P h_l) (BatchingRule.eqFold L κ)))
      (derivedTarget_messageEquiv_eq_compute_s0 P z c)

omit [SampleableType L] in
/-- The shared packed witness is the original basis packing of the Boolean table. -/
theorem packedMLE_components_eq_packMLE (t : MultilinearPoly K ℓ) :
    (PackingData.ofBasis P.basis).packedMLE ((layout P h_l).components t) =
      packMLE κ L K ℓ ℓ' h_l P.basis t :=
  (packMLE_eq_packedMLE h_l P.basis t).symm

omit [SampleableType L] in
/-- The transmitted honest message equals the original embedded carrier evaluation. -/
theorem messageEquiv_symm_partials_eq_embedded_MLP_eval (r : Fin ℓ → L) (t : MultilinearPoly K ℓ) :
    (messageEquiv P).symm
        (Head.partials (PackingData.ofBasis P.basis) ℓ' (layout P h_l) r t) =
      embedded_MLP_eval κ L K P ℓ ℓ' h_l
        (packMLE κ L K ℓ ℓ' h_l P.basis t) r := by
  apply (messageEquiv P).injective
  rw [Equiv.apply_symm_apply]
  funext i
  change aeval (getEvaluationPointSuffix κ L ℓ ℓ' h_l r)
      ((layout P h_l).components t i).val = P.decomposeColumns
      (embedded_MLP_eval κ L K P ℓ ℓ' h_l (packMLE κ L K ℓ ℓ' h_l P.basis t) r) i
  rw [columns_embedded_MLP_eval, ← packedMLE_components_eq_packMLE,
    (PackingData.ofBasis P.basis).unpack_packedMLE]

omit [SampleableType L] in
/-- The shared extractor recovers the original source by basis-coordinate unpacking. -/
theorem components_symm_unpack_eq_unpackMLE (p : MultilinearPoly L ℓ') :
    (layout P h_l).components.symm ((PackingData.ofBasis P.basis).unpack p) =
      unpackMLE κ L K ℓ ℓ' h_l P.basis p := by
  apply (sourceDimensionEquiv h_l).injective
  change (sourceDimensionEquiv h_l)
    ((sourceDimensionEquiv h_l).symm
      (joinFirst κ ℓ' ((PackingData.ofBasis P.basis).unpack p))) = _
  rw [Equiv.apply_symm_apply]
  exact (unpackMLE_eq_joinFirst h_l P.basis p).symm

/-- The matrix terminal evaluates the original public equality multiplier. -/
theorem multiplier_evaluate_eq_compute_final_eq_value (r : Fin ℓ → L) (c : Fin κ → L) (r' : Fin
    ℓ' → L) :
    (Head.multiplier (PackingData.ofBasis P.basis) ℓ' (layout P h_l)
        (BatchingRule.eqFold L κ)).evaluate (r, c) r' =
      compute_final_eq_value κ L K P ℓ ℓ' h_l r r' c := by
  rw [(Head.multiplier (PackingData.ofBasis P.basis) ℓ' (layout P h_l)
    (BatchingRule.eqFold L κ)).evaluate_eq]
  rw [compute_final_eq_value_eq_eval, compute_A_MLE_eq_multiplier]
  rfl

end Program

section Security
variable [NoZeroDivisors L] [Fintype L] [SampleableType L] (a : AbstractOStmtIn L ℓ')

/-- If compatible packed polynomials have the same carrier evaluation at the fixed query,
an incorrect carrier has the same batching target with probability at most `κ/|L|`. -/
theorem pr_exists_target_collision_le_of_embedded_eval_eq
    (r : Fin ℓ → L) (ost : ∀ j, a.OStmtIn j) (z : P.A)
    (hbind : ∀ p p', a.initialCompatibility (p, ost) →
      a.initialCompatibility (p', ost) →
      embedded_MLP_eval κ L K P ℓ ℓ' h_l p r =
        embedded_MLP_eval κ L K P ℓ ℓ' h_l p' r) :
    Pr{let c ← $ᵗ (Fin κ → L)}[∃ p,
      a.initialCompatibility (p, ost) ∧ embedded_MLP_eval κ L K P ℓ ℓ' h_l p r ≠ z ∧
        compute_s0 κ L K P z c =
          compute_s0 κ L K P (embedded_MLP_eval κ L K P ℓ ℓ' h_l p r) c] ≤
      (((κ : ℝ≥0) / Fintype.card L : ℝ≥0) : ℝ≥0∞) := by
  let data := PackingData.ofBasis P.basis
  have hpartials : ∀ p p' : MultilinearPoly L ℓ',
      (commitment a).commitsTo ost p → (commitment a).commitsTo ost p' → ∀ i,
        aeval ((layout P h_l).point r) (data.unpack p i).val =
          aeval ((layout P h_l).point r) (data.unpack p' i).val := by
    intro p p' hp hp' i
    exact (columns_embedded_MLP_eval P h_l p r i).symm.trans
      ((congrArg (fun t => P.decomposeColumns t i) (hbind p p' hp hp')).trans
        (columns_embedded_MLP_eval P h_l p' r i))
  refine (prEvent_mono _ _ _ fun c h => ?_).trans
    (Head.pr_exists_derivedTarget_le_of_partials_eq data ℓ' (layout P h_l)
      (BatchingStrategy.eqFold L κ) (commitment a) (fun _ _ h => h) r ost
      (messageEquiv P z) hpartials)
  obtain ⟨p, hp, hwrong, heq⟩ := h
  refine ⟨p, hp, ?_, ?_⟩
  · intro hopen
    apply hwrong
    apply P.columnEquiv.injective
    funext i
    exact (columns_embedded_MLP_eval P h_l p r i).trans (hopen i).symm
  · change (data.derivedTarget (messageEquiv P z) ((BatchingRule.eqFold L κ).weight c), p) ∈ _
    rw [derivedTarget_messageEquiv_eq_compute_s0 P z c, heq, ←
      derivedTarget_messageEquiv_eq_compute_s0 P (embedded_MLP_eval κ L K P ℓ ℓ' h_l p r) c]
    exact data.sumcheckClaimRel_derivedTarget_of_openingClaimRel
      ((BatchingRule.eqFold L κ).weight c) ((layout P h_l).point r)
      (messageEquiv P (embedded_MLP_eval κ L K P ℓ ℓ' h_l p r)) p
      (columns_embedded_MLP_eval P h_l p r)

/-- The shared strategy assigns the original batching loss to the carrier wire. -/
abbrev rbrError := RingSwitch.rbrError (M := P.A) (PackingData.ofBasis P.basis) ℓ'
  (BatchingStrategy.eqFold L κ)

/-- The verifier inherits the shared round-by-round security proof. -/
theorem rbrKnowledgeSoundness (h : a.Functional) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier P h_l a).toVerifier.rbrKnowledgeSoundness init impl (relIn P h_l a)
      ((commitment a).evalRelWithContext ((Fin ℓ → L) × (Fin κ → L))) (rbrError P) :=
  RingSwitch.rbrKnowledgeSoundness (PackingData.ofBasis P.basis) ℓ' (layout P h_l)
    (messageEquiv P) (BatchingStrategy.eqFold L κ) (commitment a) (commitment_functional a h)
    (fun _ _ h => h) init impl

/-- The challenge-index sum is `κ/|L| + 2ℓ'/|L|`. -/
theorem rbrError_sum : ∑ i, rbrError (ℓ' := ℓ') P i =
    (κ : ℝ≥0) / Fintype.card L + (ℓ' : ℝ≥0) * (2 / Fintype.card L) :=
  RingSwitch.rbrError_sum (M := P.A) (PackingData.ofBasis P.basis) ℓ'
    (BatchingStrategy.eqFold L κ)

/-- Prefix packing is complete and round-by-round knowledge sound, with total
challenge error `κ / card L + 2ℓ' / card L`. -/
theorem perfectCompleteness_and_rbrKnowledgeSoundness
    (h : a.Functional) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction P h_l a).perfectCompleteness init impl (relIn P h_l a)
        ((commitment a).evalRelWithContext ((Fin ℓ → L) × (Fin κ → L))) ∧
      (verifier P h_l a).toVerifier.rbrKnowledgeSoundness init impl (relIn P h_l a)
        ((commitment a).evalRelWithContext ((Fin ℓ → L) × (Fin κ → L))) (rbrError P) ∧
      (∑ i, rbrError (ℓ' := ℓ') P i) =
        (κ : ℝ≥0) / Fintype.card L + (ℓ' : ℝ≥0) * (2 / Fintype.card L) := by
  have hgeneric := RingSwitch.perfectCompleteness_and_rbrKnowledgeSoundness
      (PackingData.ofBasis P.basis) ℓ' (layout P h_l) (messageEquiv P)
      (BatchingStrategy.eqFold L κ) (commitment a) (commitment_functional a h)
      (fun _ _ h => h) init impl
  exact ⟨hgeneric.1, hgeneric.2.1, hgeneric.2.2⟩

/-- Prefix packing is knowledge sound with error `κ/|L| + 2ℓ'/|L|`. -/
theorem knowledgeSoundness (h : a.Functional) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (verifier P h_l a).knowledgeSoundness init impl (relIn P h_l a)
      ((commitment a).evalRelWithContext ((Fin ℓ → L) × (Fin κ → L)))
      ((κ : ℝ≥0) / Fintype.card L + (ℓ' : ℝ≥0) * (2 / Fintype.card L)) :=
  RingSwitch.knowledgeSoundness (PackingData.ofBasis P.basis) ℓ' (layout P h_l)
    (messageEquiv P) (BatchingStrategy.eqFold L κ) (commitment a) (commitment_functional a h)
    (fun _ _ h => h) init impl

/-- Prefix packing is perfectly complete and knowledge sound with error `κ/|L| + 2ℓ'/|L|`. -/
theorem perfectCompleteness_and_knowledgeSoundness
    (h : a.Functional) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction P h_l a).perfectCompleteness init impl (relIn P h_l a)
        ((commitment a).evalRelWithContext ((Fin ℓ → L) × (Fin κ → L))) ∧
      (verifier P h_l a).knowledgeSoundness init impl (relIn P h_l a)
        ((commitment a).evalRelWithContext ((Fin ℓ → L) × (Fin κ → L)))
        ((κ : ℝ≥0) / Fintype.card L + (ℓ' : ℝ≥0) * (2 / Fintype.card L)) :=
  ⟨perfectCompleteness P h_l a init impl, knowledgeSoundness P h_l a h init impl⟩

end Security
end RingSwitching.Packing.TensorPrefix
