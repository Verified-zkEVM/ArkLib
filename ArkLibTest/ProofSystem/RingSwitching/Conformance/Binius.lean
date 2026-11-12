/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.Binius.FRIBinius.Conformance
import ArkLibTest.ProofSystem.RingSwitching.Packing.Orientation

/-!
# Prefix ring-switching regression controls

The DP24 head transmits the original tensor carrier and decodes its columns through the
shared verifier. The concrete binary tower distinguishes rows from columns and packed from
retained variables. A zero carrier exhibits a batching collision; false claims and false
sumcheck messages abort the materialized shared verifiers. The full frontend has an inhabited
input and an exact challenge-error sum below one.
-/

open Module MvPolynomial RingSwitching Sumcheck.Structured
open RingSwitching.Packing RingSwitching.Packing.Conformance

noncomputable section
namespace ArkLibTest.RingSwitchingConformance.Binius
open ConcreteBinaryTower
open ArkLibTest.RingSwitchingOrientation renaming K → GF2, L → GF4, p → P₄, r → r₀, t → tX₀
open ArkLibTest.RingSwitchingOrientation (beta tp shat beta_zero beta_one sum_one_bit shat_eq
  column_zero row_zero row_one bit_zero_ne_one)
attribute [local instance] ArkLibTest.RingSwitchingOrientation.algebraKL
local instance : SampleableType GF4 := SampleableType.ofFintype GF4
local notation "ζ" => ConcreteBinaryTower.Z 1

/-- A binding oracle statement over the orientation fixture: it holds the packed polynomial. -/
def exactOStmtIn : AbstractOStmtIn GF4 1 where
  ιₛᵢ := Unit
  OStmtIn := fun _ => MultilinearPoly GF4 1
  Oₛᵢ := fun _ => OracleInterface.instDefault
  initialCompatibility := fun x => x.1 = x.2 ()

/-- Exact commitments determine the packed polynomial at every oracle statement. -/
theorem exactOStmtIn_functional : exactOStmtIn.Functional := by
  intro o t₁ t₂ h₁ h₂
  exact h₁.trans h₂.symm

/-- The oracle statement committing to the honest packed polynomial `tp`. -/
def oStmt₀ : ∀ j, exactOStmtIn.OStmtIn j := fun _ => tp

abbrev data := PackingData.ofBasis P₄.basis
abbrev layout := TensorPrefix.layout P₄ (ℓ := 2) (ℓ' := 1) rfl
abbrev pc := TensorPrefix.commitment exactOStmtIn
abbrev rule := BatchingRule.eqFold GF4 1
abbrev codec := TensorPrefix.messageEquiv P₄

def claimAt (s : GF4) : (Fin 2 → GF4) × GF4 := (r₀, s)

def acceptedStatement (s : GF4) (z : P₄.A) (c : Fin 1 → GF4) :=
  Head.nextStatement data 1 layout rule (claimAt s) (codec z) c

theorem accepted_iff (s : GF4) (z : P₄.A) (c : Fin 1 → GF4)
    (p : MultilinearPoly GF4 1) :
    ((acceptedStatement s z c, oStmt₀), p) ∈ Head.relOut data 1 layout rule pc ↔
      (compute_s0 1 GF4 GF2 P₄ z c, p) ∈ data.sumcheckClaimRel 1
        ((TensorPrefix.layout P₄ (ℓ' := 1) rfl).point r₀) (batchingWeight c) ∧ p = tp := by
  erw [Head.relOut_iff]
  change (data.derivedTarget (codec z) (rule.weight c), p) ∈ _ ∧ p = tp ↔ _
  rw [TensorPrefix.derivedTarget_messageEquiv_eq_compute_s0]
  rfl

theorem honest_input : ((claimAt 0, oStmt₀), tX₀) ∈ TensorPrefix.relIn P₄ rfl exactOStmtIn := by
  constructor
  · simp [claimAt, TensorPrefix.layout, tX₀, r₀]
  · rw [TensorPrefix.packedMLE_components_eq_packMLE]
    rfl

example {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :=
  TensorPrefix.rbrKnowledgeSoundness P₄ rfl exactOStmtIn exactOStmtIn_functional init impl

/-- With one packed variable, a layout-weighted sum is the linear interpolation at the point's
first coordinate. -/
theorem sum_weight (x : Fin 2 → GF4) (f : (Fin 1 → Fin 2) → GF4) :
    ∑ v, (TensorPrefix.layout P₄ (ℓ' := 1) rfl).weight x v * f v =
      (1 - x 0) * f (fun _ => 0) + x 0 * f (fun _ => 1) := by
  simp [sum_one_bit, TensorPrefix.layout, eqTilde]

/-- At a point with a Boolean first coordinate, layout-weighted sums select that bit. -/
theorem sum_weight_of_bit (x : Fin 2 → GF4) (b : Fin 2) (hx : x 0 = b)
    (f : (Fin 1 → Fin 2) → GF4) :
    ∑ v, (TensorPrefix.layout P₄ (ℓ' := 1) rfl).weight x v * f v = f (fun _ => b) := by
  rw [sum_weight, hx]
  fin_cases b <;> simp

/-- At the zero point, layout-weighted sums select the coordinate at the zero bit. -/
theorem sum_weight_zero (f : (Fin 1 → Fin 2) → GF4) :
    ∑ v, (TensorPrefix.layout P₄ (ℓ' := 1) rfl).weight r₀ v * f v = f (fun _ => 0) :=
  sum_weight_of_bit r₀ 0 (by simp [r₀]) f

/-- With one batching variable, a batched sum is the linear interpolation at the challenge. -/
theorem sum_batchingWeight (c : Fin 1 → GF4) (f : (Fin 1 → Fin 2) → GF4) :
    ∑ u, batchingWeight c u * f u = (1 - c 0) * f (fun _ => 0) + c 0 * f (fun _ => 1) := by
  simp [sum_one_bit, batchingWeight, eqTilde]

/-- At a Boolean challenge, batched sums select that bit. -/
theorem sum_batchingWeight_of_bit (c : Fin 1 → GF4) (b : Fin 2) (hc : c 0 = b)
    (f : (Fin 1 → Fin 2) → GF4) :
    ∑ u, batchingWeight c u * f u = f (fun _ => b) := by
  rw [sum_batchingWeight, hc]
  fin_cases b <;> simp

/-- At the zero challenge, batched sums select the coordinate at the zero bit. -/
theorem sum_batchingWeight_zero (f : (Fin 1 → Fin 2) → GF4) :
    ∑ u, batchingWeight (0 : Fin 1 → GF4) u * f u = f (fun _ => 0) :=
  sum_batchingWeight_of_bit 0 0 (by simp) f

/-- The second basis vector `ζ` is nonzero. -/
theorem Z_one_ne_zero : ζ ≠ (0 : GF4) := beta_one ▸ beta.ne_zero _

/-- At every challenge, the honest carrier's batched rows are the shared sumcheck claim of the
packed polynomial. -/
theorem honest_sumcheckClaimRel (c : Fin 1 → GF4) :
    (∑ u, batchingWeight c u * P₄.decomposeRows shat u, tp) ∈
      (Packing.PackingData.ofBasis P₄.basis).sumcheckClaimRel 1
        ((TensorPrefix.layout P₄ (ℓ' := 1) rfl).point r₀) (batchingWeight c) := by
  have h := (Packing.PackingData.ofBasis P₄.basis).sumcheckClaim_of_slices (C := GF4)
    (embedded_MLP_eval_sliceRel P₄ rfl tp r₀) (batchingWeight c)
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
  exact h

/-- The carrier check accepts the honest input. -/
example : performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl 0 r₀ shat = true :=
  (check_iff_layout_weight P₄ rfl 0 r₀ shat).2 (by rw [sum_weight_zero, column_zero])

/-- The same packed polynomial satisfies the accepted sumcheck relation. -/
theorem honest_output (c : Fin 1 → GF4) :
    ((acceptedStatement 0 shat c, oStmt₀), tp) ∈ Head.relOut data 1 layout rule pc := by
  apply (accepted_iff 0 shat c tp).2
  exact ⟨by simpa only [compute_s0_eq_sum] using honest_sumcheckClaimRel c, rfl⟩

example : performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl 0 r₀ 0 = true :=
  (check_iff_layout_weight P₄ rfl 0 r₀ 0).2 (by rw [sum_weight_zero, P₄.decomposeColumns_zero]; rfl)

/-- A zero carrier at challenge zero cannot satisfy the accepted relation for any packed witness. -/
example (p : MultilinearPoly GF4 1) :
    ((acceptedStatement 0 0 0, oStmt₀), p) ∉ Head.relOut data 1 layout rule pc := by
  intro h
  obtain ⟨hclaim, rfl⟩ := (accepted_iff 0 0 0 p).1 h
  have h0 := (show _ = _ from hclaim).trans (show _ = _ from honest_sumcheckClaimRel 0).symm
  rw [compute_s0_eq_sum, sum_batchingWeight_zero, sum_batchingWeight_zero,
    P₄.decomposeRows_zero, shat_eq, row_zero] at h0
  exact Z_one_ne_zero h0.symm

/-- At challenge zero a false scalar claim has no simultaneously checked, related output. -/
example (z : P₄.A) (p : MultilinearPoly GF4 1) :
    ¬ (performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl 1 r₀ z = true ∧
      ((acceptedStatement 1 z 0, oStmt₀), p) ∈ Head.relOut data 1 layout rule pc) := by
  rintro ⟨hcheck, hrel⟩
  obtain ⟨hclaim, rfl⟩ := (accepted_iff 1 z 0 p).1 hrel
  have hrow : P₄.decomposeRows z (fun _ => 0) = ζ := by
    have h0 := (show _ = _ from hclaim).trans (show _ = _ from honest_sumcheckClaimRel 0).symm
    rwa [compute_s0_eq_sum, sum_batchingWeight_zero, sum_batchingWeight_zero,
      shat_eq, row_zero] at h0
  have hcol := (check_iff_layout_weight P₄ rfl _ _ _).1 hcheck
  change (1 : GF4) = ∑ v, (TensorPrefix.layout P₄ (ℓ' := 1) rfl).weight r₀ v *
    P₄.decomposeColumns z v at hcol
  rw [sum_weight_zero] at hcol
  have key := data.repr_transpose (P₄.decomposeColumns z) (fun _ => 0) (fun _ => 0)
  rw [P₄.transpose_decomposeColumns, hrow, ← hcol, ← beta_one, ← beta_zero] at key
  change beta.repr (beta _) _ = beta.repr (beta _) _ at key
  rw [Basis.repr_self, Basis.repr_self, Finsupp.single_eq_same, Finsupp.single_eq_of_ne] at key
  · exact zero_ne_one key
  · exact fun h => absurd (congrFun h 0) (by decide)

/-- The honest carrier's columns open the components of the source `tX₀ = X₀` at the retained
point. -/
theorem columns_openingClaimRel :
    ((P₄.decomposeColumns shat, (TensorPrefix.layout P₄ (ℓ' := 1) rfl).point r₀),
        (TensorPrefix.layout P₄ (ℓ' := 1) rfl).components tX₀) ∈
      (Packing.PackingData.ofBasis P₄.basis).openingClaimRel 1 :=
  (embedded_MLP_eval_packMLE_eq_iff_openingClaimRel P₄ rfl tX₀ r₀ shat).1 rfl

/-- Its rows `(ζ, 0)` do not open them, so swapping rows and columns is caught. -/
example : ((P₄.decomposeRows shat, (TensorPrefix.layout P₄ (ℓ' := 1) rfl).point r₀),
      (TensorPrefix.layout P₄ (ℓ' := 1) rfl).components tX₀) ∉
    (Packing.PackingData.ofBasis P₄.basis).openingClaimRel 1 := by
  intro h
  have h0 : P₄.decomposeRows shat (fun _ => 0) = P₄.decomposeColumns shat (fun _ => 0) :=
    (h _).trans (columns_openingClaimRel _).symm
  rw [column_zero, shat_eq, row_zero] at h0
  exact Z_one_ne_zero h0

/-- A source in the retained variable, `t₁ = X₁`. -/
def t₁ : MultilinearPoly GF2 2 :=
  ⟨MvPolynomial.X 1, by
    rw [mem_restrictDegree_iff_degreeOf_le]
    intro i
    simp only [degreeOf_X]
    split <;> omega⟩

/-- The honest carrier of `t₁` at a point with retained coordinate `ζ`. -/
def shat₁ : P₄.A :=
  embedded_MLP_eval 1 GF4 GF2 P₄ 2 1 rfl (packMLE 1 GF4 GF2 2 1 rfl beta t₁) ![0, ζ]

/-- Both columns of `shat₁` are `ζ`: the honest check reads column `b` back as `t₁(b, ζ)`
at the packed prefix `b`, and the carrier does not depend on the prefix. -/
theorem columns_shat₁ (v : Fin 1 → Fin 2) : P₄.decomposeColumns shat₁ v = ζ := by
  have hcol (b : Fin 2) : P₄.decomposeColumns shat₁ (fun _ => b) = ζ := by
    have h := (check_iff_layout_weight P₄ rfl _ _ _).1
      (performCheckOriginalEvaluation_honest P₄ rfl t₁ ![(b : GF4), ζ])
    rw [sum_weight_of_bit _ b (by simp)] at h
    exact h.symm.trans (by simp [t₁])
  obtain ⟨b, rfl⟩ : ∃ b : Fin 2, v = fun _ => b := ⟨v 0, funext fun i => by fin_cases i; rfl⟩
  exact hcol b

/-- Row zero of `shat₁` is `0`: its coordinates are the zero coordinates of the columns `ζ`,
through the shared transpose. -/
theorem row_zero_shat₁ : P₄.decomposeRows shat₁ (fun _ => 0) = 0 := by
  refine beta.repr.injective (Finsupp.ext fun v => ?_)
  have h := (Packing.PackingData.ofBasis P₄.basis).repr_transpose (P₄.decomposeColumns shat₁)
    (fun _ => 0) v
  rw [P₄.transpose_decomposeColumns, columns_shat₁, ← beta_one] at h
  change beta.repr _ v = beta.repr (beta _) _ at h
  rw [h, Basis.repr_self, map_zero, Finsupp.zero_apply]
  exact Finsupp.single_eq_of_ne fun h => absurd (congrFun h 0) (by decide)

/-- At the nonconstant source `t₁` and the point `(0, ζ)`, the honest check accepts the true
claim `t₁(0, ζ) = ζ`, which is the column read-back. -/
example : performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl (ζ) ![0, ζ] shat₁ = true := by
  have h := performCheckOriginalEvaluation_honest P₄ rfl t₁ ![0, ζ]
  rwa [show aeval ![0, ζ] t₁.val = ζ by simp [t₁]] at h

/-- Reading the claim back from the rows instead gives `0`, so a row/column swap rejects the
honest claim. -/
example : ζ ≠ ∑ v, (TensorPrefix.layout P₄ (ℓ' := 1) rfl).weight ![0, ζ] v *
    P₄.decomposeRows shat₁ v := by
  rw [sum_weight_of_bit _ 0 (by simp), row_zero_shat₁]
  exact Z_one_ne_zero

/-! ### A packed/retained swap

At `t = X₀` and the point `(ζ, 0)`, the honest carrier is still `shat`, which depends only on the
retained coordinate `0`. The prefix-weighted columns read back the true claim `ζ`; weighting the
columns by the retained coordinate instead reads back column zero, `0`. -/

/-- The honest carrier at `(ζ, 0)` is `shat`. -/
theorem carrier_Z_one_zero : embedded_MLP_eval 1 GF4 GF2 P₄ 2 1 rfl tp ![ζ, 0] = shat := by
  unfold shat embedded_MLP_eval
  dsimp only
  congr 2
  funext i
  fin_cases i
  simp [r₀]

/-- The honest check at `(ζ, 0)` accepts the true claim `X₀(ζ, 0) = ζ`. -/
example : performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl (ζ) ![ζ, 0] shat = true := by
  have h := performCheckOriginalEvaluation_honest P₄ rfl tX₀ ![ζ, 0]
  rw [show aeval ![ζ, 0] tX₀.val = ζ by simp [tX₀]] at h
  rw [← carrier_Z_one_zero]
  exact h

/-- Weighting the columns of `shat` by the retained coordinate of `(ζ, 0)` instead of the packed
one gives `0`, so a packed/retained swap rejects the honest claim. -/
example : ζ ≠ ∑ v : Fin 1 → Fin 2,
    eqTilde (v : Fin 1 → GF4) (getEvaluationPointSuffix 1 GF4 2 1 rfl ![ζ, 0]) *
      P₄.decomposeColumns shat v := by
  simp only [sum_one_bit, column_zero]
  simp [eqTilde, getEvaluationPointSuffix, Z_one_ne_zero]

/-- The zero carrier is different from the honest carrier but collides at challenge one. -/
theorem zero_carrier_collides : (0 : P₄.A) ≠ shat ∧
    performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl 0 r₀ 0 = true ∧
    ((acceptedStatement 0 0 1, oStmt₀), tp) ∈ Head.relOut data 1 layout rule pc := by
  have hone : (1 : Fin 1 → GF4) 0 = ((1 : Fin 2) : GF4) := by simp
  refine ⟨?_, (check_iff_layout_weight P₄ rfl 0 r₀ 0).2 ?_, (accepted_iff 0 0 1 tp).2 ⟨?_, rfl⟩⟩
  · intro h
    have h0 := congrArg (fun z => P₄.decomposeRows z (fun _ => 0)) h
    simp only [P₄.decomposeRows_zero, shat_eq, row_zero, Pi.zero_apply] at h0
    exact Z_one_ne_zero h0.symm
  · rw [sum_weight_zero, P₄.decomposeColumns_zero]
    rfl
  · have h := honest_sumcheckClaimRel 1
    rw [sum_batchingWeight_of_bit _ 1 hone, shat_eq, row_one] at h
    change _ = _
    rw [compute_s0_eq_sum, sum_batchingWeight_of_bit _ 1 hone, P₄.decomposeRows_zero]
    exact h

/-- The zero-polynomial commitment. -/
def oStmtZero : ∀ j, exactOStmtIn.OStmtIn j := fun _ => (0 : MultilinearPoly GF4 1)

/-- A zero commitment has no source witness for the false scalar claim one. -/
theorem false_zero_input (t : MultilinearPoly GF2 2) :
    ((claimAt 1, oStmtZero), t) ∉ TensorPrefix.relIn P₄ rfl exactOStmtIn := by
  rintro ⟨hs, hp⟩
  change data.packedMLE (layout.components t) = 0 at hp
  have hc := congrArg data.unpack hp
  rw [data.unpack_packedMLE] at hc
  have hu : data.unpack (0 : MultilinearPoly GF4 1) = 0 := by
    funext i
    apply Subtype.ext
    simp [PackingData.unpack]
  rw [hu] at hc
  have he := hs.trans (layout.reconstruct r₀ t)
  rw [hc] at he
  simp [claimAt] at he

/-- A false scalar claim aborts the materialized head independently of its oracle statement. -/
theorem failed_check_aborts (ost : ∀ j, exactOStmtIn.OStmtIn j) (c : Fin 1 → GF4) :
    (Head.verifier data 1 layout codec rule pc).toVerifier.verify
      (claimAt 1, ost) (ProtocolSpec.FullTranscript.mk2 shat c) = failure := by
  classical
  have hcheck : performCheckOriginalEvaluation 1 GF4 GF2 P₄ 2 1 rfl 1 r₀ shat = false := by
    rw [Bool.eq_false_iff]
    intro h
    have hs := (check_iff_layout_weight P₄ rfl _ _ _).1 h
    change (1 : GF4) = ∑ v, (TensorPrefix.layout P₄ (ℓ' := 1) rfl).weight r₀ v * _ at hs
    rw [sum_weight_zero, column_zero] at hs
    exact one_ne_zero hs
  have hc : ¬ Head.check data 1 layout (claimAt 1) (codec shat) := by
    intro h
    have hh := (TensorPrefix.check_iff P₄ rfl r₀ 1 shat).1 h
    rw [hcheck] at hh
    contradiction
  have hfalse : (Head.guardedForm data 1 layout codec rule pc).check
      (claimAt 1, ost) (ProtocolSpec.FullTranscript.mk2 shat c) = false := by
    rw [Head.guardedForm_check]
    change decide (Head.check data 1 layout (claimAt 1) (codec shat)) = false
    exact decide_eq_false hc
  rw [(Head.guardedForm data 1 layout codec rule pc).verify_eq, hfalse]
  rfl

example (c : Fin 1 → GF4) :
    (Head.verifier data 1 layout codec rule pc).toVerifier.verify
      (claimAt 1, oStmtZero) (ProtocolSpec.FullTranscript.mk2 shat c) = failure :=
  failed_check_aborts oStmtZero c

/-- A zero degree-two message cannot support target one in the shared sumcheck round. -/
example (c : GF4) :
    (ProductSumcheck.Round.verifier (Context := layout.Query × rule.Challenge) pc
      (0 : Fin 1)).toVerifier.verify
      ({ acceptedStatement 0 shat 0 with target := 1 }, oStmt₀)
      (ProtocolSpec.FullTranscript.mk2 (0 : Polynomial.degreeLE GF4 2) c) = failure := by
  erw [ProductSumcheck.Round.verifier_verify]
  simp [ProductSumcheck.Round.check, ProtocolSpec.FullTranscript.messages,
    ProtocolSpec.FullTranscript.mk2]

/-- A zero final value cannot support target one in the matrix terminal check. -/
example : (ProductSumcheck.Terminal.verifier
    (Head.multiplier data 1 layout rule) pc).toVerifier.verify
    ((⟨(r₀, (0 : Fin 1 → GF4)), 0, 1⟩ :
      ProductSumcheck.Statement (layout.Query × rule.Challenge) GF4 (Fin.last 1)), oStmt₀)
    (ProductSumcheck.Terminal.transcript 0) = failure := by
  erw [ProductSumcheck.Terminal.verifier_verify]
  simp [ProductSumcheck.Terminal.check, ProductSumcheck.Terminal.transcript,
    ProtocolSpec.FullTranscript.messages]

end ArkLibTest.RingSwitchingConformance.Binius
end
