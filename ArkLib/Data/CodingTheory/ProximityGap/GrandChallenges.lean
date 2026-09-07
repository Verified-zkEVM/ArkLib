/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Proximity grand challenges

This file expresses the mutual-correlated-agreement and list-decoding challenges as boundary
problems on the integer agreement grid. A boundary answer is safe at `k / n` and unsafe at
`(k + 1) / n`; an endpoint answer certifies safety at every grid point through radius one.

The mutual-correlated-agreement challenge uses `CoreDefinitions.mcaError` with
`AffineLineGenerator F`. The prize specializations use Reed--Solomon codes at the exact rates
`1/2`, `1/4`, `1/8`, and `1/16`.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26]
-/

namespace ProximityGap

open scoped NNReal
open CoreDefinitions

/-! ## The integer-agreement grid -/

/-- Grid point `k / n` in `ℝ≥0`, where `n := |ι|`. -/
noncomputable def gridPt {ι : Type} [Fintype ι] (k : ℕ) : ℝ≥0 :=
  (k : ℝ≥0) / (Fintype.card ι : ℝ≥0)

/-- `k ≤ n` puts the grid point in the closed unit interval. -/
theorem gridPt_le_one {ι : Type} [Fintype ι] [Nonempty ι] {k : ℕ}
    (hk : k ≤ Fintype.card ι) : gridPt (ι := ι) k ≤ 1 := by
  have hn : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  rw [gridPt, div_le_one hn]
  exact_mod_cast hk

/-- Monotonicity of the agreement grid. -/
theorem gridPt_mono {ι : Type} [Fintype ι] {k k' : ℕ} (h : k ≤ k') :
    gridPt (ι := ι) k ≤ gridPt (ι := ι) k' := by
  unfold gridPt
  gcongr

/-- Cancelling the positive grid denominator in `ℝ≥0`. -/
theorem gridPt_mul_card {ι : Type} [Fintype ι] [Nonempty ι] (k : ℕ) :
    gridPt (ι := ι) k * (Fintype.card ι : ℝ≥0) = (k : ℝ≥0) := by
  have hn : (Fintype.card ι : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [gridPt, div_mul_cancel₀ _ hn]

/-- Real-valued version of `gridPt_mul_card`. -/
theorem gridPt_coe_mul_card {ι : Type} [Fintype ι] [Nonempty ι] (k : ℕ) :
    (gridPt (ι := ι) k : ℝ) * (Fintype.card ι : ℝ) = (k : ℝ) := by
  exact_mod_cast gridPt_mul_card (ι := ι) k

/-- Affine-line MCA is monotone along the integer-agreement grid. -/
theorem mcaError_gridPt_mono {F ι : Type} [Field F] [Fintype F]
    [Fintype ι] [Nonempty ι] (C : LinearCode ι F) {k k' : ℕ} (h : k ≤ k') :
    mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k : ℝ) ≤
      mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k' : ℝ) :=
  mcaError_mono (AffineLineGenerator F) C (by exact_mod_cast gridPt_mono h)

/-! ## Logical challenge predicates -/

/-- An adjacent affine-line MCA crossing, or safety at every grid point through radius one. -/
def grandMcaChallenge {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι]
    (C : LinearCode ι F) (ε_star : ℝ≥0) : Prop :=
  (∃ k : ℕ, k < Fintype.card ι ∧
      mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k : ℝ) ≤ (ε_star : ENNReal) ∧
      mcaError (AffineLineGenerator F) C (gridPt (ι := ι) (k + 1) : ℝ) >
        (ε_star : ENNReal)) ∨
    ∀ k : ℕ, k ≤ Fintype.card ι →
      mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k : ℝ) ≤ (ε_star : ENNReal)

/-- An adjacent list-size crossing, or safety at every grid point through radius one. -/
def grandListDecodingChallenge {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι]
    (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) : Prop :=
  (∃ k : ℕ, k < Fintype.card ι ∧
      (Code.Lambda (C ^⋈ (Fin m)) (gridPt (ι := ι) k : ℝ) : ENNReal) ≤
        (ε_star : ENNReal) * (Fintype.card F : ENNReal) ∧
      (Code.Lambda (C ^⋈ (Fin m)) (gridPt (ι := ι) (k + 1) : ℝ) : ENNReal) >
        (ε_star : ENNReal) * (Fintype.card F : ENNReal)) ∨
    ∀ k : ℕ, k ≤ Fintype.card ι →
      (Code.Lambda (C ^⋈ (Fin m)) (gridPt (ι := ι) k : ℝ) : ENNReal) ≤
        (ε_star : ENNReal) * (Fintype.card F : ENNReal)

/-! ## Prize constants and smooth Reed--Solomon specializations -/

/-- The `j`th prize rate, one of `1/2`, `1/4`, `1/8`, and `1/16`. -/
def prizeRate (j : Fin 4) : ℚ≥0 := 1 / 2 ^ (j.val + 1)

/-- The prize error threshold `2⁻¹²⁸`. -/
def prizeThreshold : ℚ≥0 := 1 / 2 ^ (128 : ℕ)

/-- Denominator of the `j`th prize rate. -/
def prizeDenominator (j : Fin 4) : ℕ := 2 ^ (j.val + 1)

/-- Exact message length for the `j`th prize rate. -/
def prizeDimension {ι : Type} [Fintype ι] (j : Fin 4) : ℕ :=
  Fintype.card ι / prizeDenominator j

/-- Domain-size conditions under which all four prize rates are exact. -/
structure PrizeDomainAdmissible (ι : Type) [Fintype ι] : Prop where
  /-- Every prize denominator through `16` fits in the evaluation domain. -/
  card_ge : 16 ≤ Fintype.card ι
  /-- Every prize denominator divides the evaluation-domain size. -/
  denominator_dvd : ∀ j : Fin 4, prizeDenominator j ∣ Fintype.card ι

namespace GrandChallenges

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι]

omit [Fintype F] [Nonempty ι] in
/-- A smooth evaluation domain of length at least `16` is prize-domain admissible. -/
theorem PrizeDomainAdmissible.of_smooth (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (hcard : 16 ≤ Fintype.card ι) : PrizeDomainAdmissible ι := by
  refine ⟨hcard, fun j => ?_⟩
  obtain ⟨k, hk⟩ := ReedSolomon.Smooth.h_card_pow2 (domain := domain)
  rw [hk]
  apply Nat.pow_dvd_pow
  have hj : j.val + 1 ≤ 4 := by omega
  have hk4 : 4 ≤ k := by
    apply (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp
    simpa [hk] using hcard
  exact hj.trans hk4

/-- The affine-line MCA challenge for a Reed--Solomon code over a smooth domain. -/
def grandMcaChallengeRs (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (k : ℕ) (ε_star : ℝ≥0) : Prop :=
  grandMcaChallenge (ReedSolomon.code domain k) ε_star

/-- The list-decoding challenge for a Reed--Solomon code over a smooth domain. -/
def grandListDecodingChallengeRs (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (k m : ℕ) (ε_star : ℝ≥0) : Prop :=
  grandListDecodingChallenge (ReedSolomon.code domain k : Set (ι → F)) m ε_star

omit [Fintype F] [DecidableEq F] [Nonempty ι] in
/-- The code selected by `prizeDimension` has exactly the advertised prize rate. -/
theorem prizeCode_rate_eq (domain : ι ↪ F) (h : PrizeDomainAdmissible ι) (j : Fin 4) :
    LinearCode.rate (ReedSolomon.code domain (prizeDimension (ι := ι) j)) = prizeRate j := by
  unfold prizeDimension
  rw [ReedSolomon.rateOfLinearCode_eq_div (Nat.div_le_self _ _)]
  unfold prizeRate
  have hdpos : 0 < prizeDenominator j := by
    simp [prizeDenominator]
  rw [Nat.cast_div (h.denominator_dvd j) (by exact_mod_cast hdpos.ne')]
  unfold prizeDenominator
  have hn : (Fintype.card ι : ℚ≥0) ≠ 0 := by
    have hcard := h.card_ge
    exact_mod_cast (by omega : Fintype.card ι ≠ 0)
  field_simp [hn]
  norm_cast

/-- The affine-line MCA challenge at every prize rate. -/
def mcaPrize (domain : ι ↪ F) [ReedSolomon.Smooth domain] : Prop :=
  PrizeDomainAdmissible ι ∧ ∀ j : Fin 4,
    grandMcaChallengeRs domain (prizeDimension (ι := ι) j) (prizeThreshold : ℝ≥0)

/-- The list-decoding challenge at every prize rate for a nonempty interleaving width. -/
def listDecodingPrize (domain : ι ↪ F) [ReedSolomon.Smooth domain] (m : ℕ) : Prop :=
  0 < m ∧ PrizeDomainAdmissible ι ∧ ∀ j : Fin 4,
    grandListDecodingChallengeRs domain
      (prizeDimension (ι := ι) j) m (prizeThreshold : ℝ≥0)

/-! ## Mutual correlated agreement boundary data -/

/-- An adjacent affine-line MCA boundary. -/
structure GrandMcaResolution (C : LinearCode ι F) (ε_star : ℝ≥0) where
  /-- Boundary grid index. -/
  kStar : ℕ
  /-- Both adjacent grid points lie in `[0,1]`. -/
  lt_card : kStar < Fintype.card ι
  /-- The error bound is safe at `kStar / n`. -/
  below : mcaError (AffineLineGenerator F) C (gridPt (ι := ι) kStar : ℝ) ≤
    (ε_star : ENNReal)
  /-- The error bound is unsafe at `(kStar + 1) / n`. -/
  above : mcaError (AffineLineGenerator F) C (gridPt (ι := ι) (kStar + 1) : ℝ) >
    (ε_star : ENNReal)

/-- A radius where the affine-line MCA error is within the threshold. -/
structure McaLowerWitness (C : LinearCode ι F) (ε_star : ℝ≥0) where
  /-- Certified radius. -/
  δ : ℝ≥0
  /-- The radius lies in `[0,1]`. -/
  le_one : δ ≤ 1
  /-- The affine-line MCA error is within the threshold. -/
  bound : mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal)

/-- A radius where the affine-line MCA error exceeds the threshold. -/
structure McaUpperWitness (C : LinearCode ι F) (ε_star : ℝ≥0) where
  /-- Certified radius. -/
  δ : ℝ≥0
  /-- The radius lies in `[0,1]`. -/
  le_one : δ ≤ 1
  /-- The affine-line MCA error exceeds the threshold. -/
  exceeds : mcaError (AffineLineGenerator F) C (δ : ℝ) > (ε_star : ENNReal)

namespace GrandMcaResolution

variable {C : LinearCode ι F} {ε_star : ℝ≥0}

omit [DecidableEq F] [Nonempty ι] in
/-- Below the safe grid point, the MCA bound remains safe. -/
theorem le_of_gridPt (R : GrandMcaResolution C ε_star) {δ : ℝ≥0}
    (hδ : δ ≤ gridPt (ι := ι) R.kStar) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal) :=
  le_trans (mcaError_mono (AffineLineGenerator F) C (by exact_mod_cast hδ)) R.below

omit [DecidableEq F] [Nonempty ι] in
/-- At or above the adjacent unsafe point, the MCA bound remains unsafe. -/
theorem gt_of_gridPt (R : GrandMcaResolution C ε_star) {δ : ℝ≥0}
    (hδ : gridPt (ι := ι) (R.kStar + 1) ≤ δ) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) > (ε_star : ENNReal) :=
  lt_of_lt_of_le R.above
    (mcaError_mono (AffineLineGenerator F) C (by exact_mod_cast hδ))

omit [DecidableEq F] in
/-- Exact safe half of the boundary cell. -/
theorem le_of_lt_next (R : GrandMcaResolution C ε_star) {δ : ℝ≥0}
    (hδ : δ < gridPt (ι := ι) (R.kStar + 1)) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal) := by
  have hn : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hfloor : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ ≤ R.kStar := by
    have hltNN : δ * (Fintype.card ι : ℝ≥0) < ((R.kStar + 1 : ℕ) : ℝ≥0) := by
      have h := hδ
      rw [gridPt, lt_div_iff₀ hn] at h
      exact_mod_cast h
    have hlt : (δ : ℝ) * (Fintype.card ι : ℝ) < (R.kStar + 1 : ℕ) := by
      exact_mod_cast hltNN
    have := (Nat.floor_lt (by positivity)).mpr hlt
    omega
  let j := ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊
  have hgrid : ⌊(gridPt (ι := ι) j : ℝ) * (Fintype.card ι : ℝ)⌋₊ = j := by
    rw [gridPt_coe_mul_card]
    exact Nat.floor_natCast _
  rw [mcaError_eq_of_floor_eq (AffineLineGenerator F) C (by positivity) (by positivity) hgrid.symm]
  exact le_trans (mcaError_gridPt_mono C hfloor) R.below

omit [DecidableEq F] in
/-- The MCA sublevel set is exactly the right-open interval ending at the unsafe grid point. -/
theorem sublevel_iff (R : GrandMcaResolution C ε_star) {δ : ℝ≥0} :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal) ↔
      δ < gridPt (ι := ι) (R.kStar + 1) := by
  refine ⟨fun hle => ?_, R.le_of_lt_next⟩
  by_contra hge
  push Not at hge
  exact absurd hle (not_le.mpr (R.gt_of_gridPt hge))

omit [DecidableEq F] in
/-- The adjacent-grid MCA boundary index is unique. -/
theorem kStar_unique (R R' : GrandMcaResolution C ε_star) : R.kStar = R'.kStar := by
  rcases lt_trichotomy R.kStar R'.kStar with h | h | h
  · exact absurd
      (le_trans (mcaError_gridPt_mono C (by omega : R.kStar + 1 ≤ R'.kStar)) R'.below)
      (not_le.mpr R.above)
  · exact h
  · exact absurd
      (le_trans (mcaError_gridPt_mono C (by omega : R'.kStar + 1 ≤ R.kStar)) R.below)
      (not_le.mpr R'.above)

/-- A resolution supplies a safe one-sided witness. -/
noncomputable def toLowerWitness (R : GrandMcaResolution C ε_star) :
    McaLowerWitness C ε_star :=
  ⟨gridPt (ι := ι) R.kStar, gridPt_le_one (le_of_lt R.lt_card), R.below⟩

/-- A resolution supplies an unsafe one-sided witness. -/
noncomputable def toUpperWitness (R : GrandMcaResolution C ε_star) :
    McaUpperWitness C ε_star :=
  ⟨gridPt (ι := ι) (R.kStar + 1), gridPt_le_one (Nat.succ_le_iff.mpr R.lt_card), R.above⟩

end GrandMcaResolution

/-- An adjacent affine-line MCA boundary satisfies the logical challenge. -/
theorem GrandMcaResolution.to_challenge {C : LinearCode ι F} {ε_star : ℝ≥0}
    (R : GrandMcaResolution C ε_star) : grandMcaChallenge C ε_star :=
  Or.inl ⟨R.kStar, R.lt_card, R.below, R.above⟩

/-- An affine-line MCA answer: either an adjacent boundary or an endpoint certificate. -/
inductive GrandMcaAnswer (C : LinearCode ι F) (ε_star : ℝ≥0) : Type where
  /-- An adjacent-boundary answer. -/
  | boundary (R : GrandMcaResolution C ε_star)
  /-- Safety at every grid point through radius one. -/
  | allGood
      (h : ∀ k : ℕ, k ≤ Fintype.card ι →
        mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k : ℝ) ≤
          (ε_star : ENNReal))

/-- An affine-line MCA answer satisfies the logical challenge. -/
theorem GrandMcaAnswer.to_challenge {C : LinearCode ι F} {ε_star : ℝ≥0}
    (A : GrandMcaAnswer C ε_star) : grandMcaChallenge C ε_star := by
  cases A with
  | boundary R => exact R.to_challenge
  | allGood h => exact Or.inr h

/-- An affine-line MCA answer at each prize rate. -/
structure McaPrizeResolution (domain : ι ↪ F) [ReedSolomon.Smooth domain] : Type where
  /-- The evaluation domain realizes all four prize rates exactly. -/
  admissible : PrizeDomainAdmissible ι
  /-- Per-rate prize answers. -/
  answer : ∀ j : Fin 4,
    GrandMcaAnswer
      (ReedSolomon.code domain (prizeDimension (ι := ι) j))
      (prizeThreshold : ℝ≥0)

/-- Per-rate affine-line MCA answers satisfy the prize proposition. -/
theorem McaPrizeResolution.to_prize {domain : ι ↪ F} [ReedSolomon.Smooth domain]
    (R : McaPrizeResolution domain) : mcaPrize domain :=
  ⟨R.admissible, fun j => (R.answer j).to_challenge⟩

omit [DecidableEq F] [Nonempty ι] in
/-- A safe witness lies strictly below the unsafe edge of every resolution. -/
theorem McaLowerWitness.lt_boundary {C : LinearCode ι F} {ε_star : ℝ≥0}
    (w : McaLowerWitness C ε_star) (R : GrandMcaResolution C ε_star) :
    w.δ < gridPt (ι := ι) (R.kStar + 1) := by
  by_contra h
  push Not at h
  exact absurd w.bound (not_le.mpr (R.gt_of_gridPt h))

omit [DecidableEq F] [Nonempty ι] in
/-- An unsafe witness lies strictly above the safe edge of every resolution. -/
theorem McaUpperWitness.boundary_lt {C : LinearCode ι F} {ε_star : ℝ≥0}
    (w : McaUpperWitness C ε_star) (R : GrandMcaResolution C ε_star) :
    gridPt (ι := ι) R.kStar < w.δ := by
  by_contra h
  push Not at h
  exact absurd (R.le_of_gridPt h) (not_le.mpr w.exceeds)

/-- An affine-line MCA upper bound at a unit-interval radius gives a safe witness. -/
def McaLowerWitness.ofLe {C : LinearCode ι F} {ε_star δ : ℝ≥0}
    (hδ : δ ≤ 1)
    (h : mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal)) :
    McaLowerWitness C ε_star := ⟨δ, hδ, h⟩

/-- An affine-line MCA lower bound at a unit-interval radius gives an unsafe witness. -/
def McaUpperWitness.ofGt {C : LinearCode ι F} {ε_star δ : ℝ≥0} (hδ : δ ≤ 1)
    (h : mcaError (AffineLineGenerator F) C (δ : ℝ) > (ε_star : ENNReal)) :
    McaUpperWitness C ε_star := ⟨δ, hδ, h⟩

open Classical in
/-- A correlated-agreement lower bound at a unit-interval radius gives an unsafe MCA witness. -/
def McaUpperWitness.ofEpsCaGt {C : LinearCode ι F} {ε_star δ : ℝ≥0}
    (hδ : δ ≤ 1)
    (h : epsCa (F := F) (A := F) (C : Set (ι → F)) δ δ > (ε_star : ENNReal)) :
    McaUpperWitness C ε_star :=
  ⟨δ, hδ, lt_of_lt_of_le h (epsCa_le_mcaError_affineLine C δ)⟩

/-! ## List-decoding boundary carriers -/

/-- A full list-decoding resolution on adjacent grid points. -/
structure GrandListResolution (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) where
  /-- Boundary grid index. -/
  kStar : ℕ
  /-- Both adjacent grid points lie in `[0,1]`. -/
  lt_card : kStar < Fintype.card ι
  /-- The list-size bound is safe at `kStar / n`. -/
  below : (Code.Lambda (C ^⋈ (Fin m)) (gridPt (ι := ι) kStar : ℝ) : ENNReal) ≤
    (ε_star : ENNReal) * (Fintype.card F : ENNReal)
  /-- The list-size bound is unsafe at `(kStar + 1) / n`. -/
  above : (Code.Lambda (C ^⋈ (Fin m)) (gridPt (ι := ι) (kStar + 1) : ℝ) : ENNReal) >
    (ε_star : ENNReal) * (Fintype.card F : ENNReal)

/-- One-sided safe list-size witness. -/
structure ListLowerWitness (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) where
  /-- Certified radius. -/
  δ : ℝ≥0
  /-- The radius lies in `[0,1]`. -/
  le_one : δ ≤ 1
  /-- The list-size bound is safe. -/
  bound : (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) ≤
    (ε_star : ENNReal) * (Fintype.card F : ENNReal)

/-- One-sided unsafe list-size witness. -/
structure ListUpperWitness (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) where
  /-- Certified radius. -/
  δ : ℝ≥0
  /-- The radius lies in `[0,1]`. -/
  le_one : δ ≤ 1
  /-- The list-size bound is unsafe. -/
  exceeds : (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
    (ε_star : ENNReal) * (Fintype.card F : ENNReal)

omit [Field F] [Fintype F] [DecidableEq F] [Nonempty ι] in
/-- The maximized list size is monotone on nonnegative radii. -/
theorem lambda_mono_nnreal {C : Set (ι → F)} {m : ℕ} {a b : ℝ≥0} (hab : a ≤ b) :
    (Code.Lambda (C ^⋈ (Fin m)) (a : ℝ) : ENNReal) ≤
      (Code.Lambda (C ^⋈ (Fin m)) (b : ℝ) : ENNReal) := by
  have hr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  exact_mod_cast Code.Lambda_mono (C := C ^⋈ (Fin m)) hr

/-- `Lambda` is constant on equal integer-agreement floor cells of nonnegative radii. -/
theorem lambda_eq_of_floor_eq {B : Type}
    {C : Set (ι → B)} {δ δ' : ℝ≥0}
    (h : ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ =
      ⌊δ' * (Fintype.card ι : ℝ≥0)⌋₊) :
    Code.Lambda C (δ : ℝ) = Code.Lambda C (δ' : ℝ) := by
  classical
  unfold Code.Lambda
  apply iSup_congr
  intro y
  congr 1
  ext c
  rw [Code.mem_closeCodewordsRel_iff, Code.mem_closeCodewordsRel_iff]
  apply and_congr_right
  intro _
  constructor
  · intro hd
    have hdnn : δᵣ(y, c) ≤ δ := by exact_mod_cast hd
    rw [Code.pairRelDist_le_iff_pairDist_le] at hdnn
    rw [h] at hdnn
    rw [← Code.pairRelDist_le_iff_pairDist_le] at hdnn
    exact_mod_cast hdnn
  · intro hd
    have hdnn : δᵣ(y, c) ≤ δ' := by exact_mod_cast hd
    rw [Code.pairRelDist_le_iff_pairDist_le] at hdnn
    rw [← h] at hdnn
    rw [← Code.pairRelDist_le_iff_pairDist_le] at hdnn
    exact_mod_cast hdnn

namespace GrandListResolution

variable {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}

omit [Field F] [DecidableEq F] [Nonempty ι] in
/-- Below the safe list grid point, the bound remains safe. -/
theorem le_of_gridPt (R : GrandListResolution C m ε_star) {δ : ℝ≥0}
    (hδ : δ ≤ gridPt (ι := ι) R.kStar) :
    (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) ≤
      (ε_star : ENNReal) * (Fintype.card F : ENNReal) :=
  le_trans (lambda_mono_nnreal hδ) R.below

omit [Field F] [DecidableEq F] [Nonempty ι] in
/-- At or above the adjacent unsafe list grid point, the bound remains unsafe. -/
theorem gt_of_gridPt (R : GrandListResolution C m ε_star) {δ : ℝ≥0}
    (hδ : gridPt (ι := ι) (R.kStar + 1) ≤ δ) :
    (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
      (ε_star : ENNReal) * (Fintype.card F : ENNReal) :=
  lt_of_lt_of_le R.above (lambda_mono_nnreal hδ)

omit [Field F] [DecidableEq F] in
/-- Exact safe half of the list-decoding boundary cell. -/
theorem le_of_lt_next (R : GrandListResolution C m ε_star) {δ : ℝ≥0}
    (hδ : δ < gridPt (ι := ι) (R.kStar + 1)) :
    (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) ≤
      (ε_star : ENNReal) * (Fintype.card F : ENNReal) := by
  have hn : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hfloor : ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊ ≤ R.kStar := by
    have hlt : δ * (Fintype.card ι : ℝ≥0) < ((R.kStar + 1 : ℕ) : ℝ≥0) := by
      have h := hδ
      rw [gridPt, lt_div_iff₀ hn] at h
      exact h
    have := (Nat.floor_lt (by positivity)).mpr hlt
    omega
  let j := ⌊δ * (Fintype.card ι : ℝ≥0)⌋₊
  have hgrid : ⌊gridPt (ι := ι) j * (Fintype.card ι : ℝ≥0)⌋₊ = j := by
    rw [gridPt_mul_card]
    exact Nat.floor_natCast _
  rw [lambda_eq_of_floor_eq (C := C ^⋈ (Fin m)) hgrid.symm]
  exact le_trans (lambda_mono_nnreal (gridPt_mono hfloor)) R.below

omit [Field F] [DecidableEq F] in
/-- The list-decoding sublevel set is exactly the right-open interval ending at the unsafe grid
point. -/
theorem sublevel_iff (R : GrandListResolution C m ε_star) {δ : ℝ≥0} :
    (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) ≤
        (ε_star : ENNReal) * (Fintype.card F : ENNReal) ↔
      δ < gridPt (ι := ι) (R.kStar + 1) := by
  refine ⟨fun hle => ?_, R.le_of_lt_next⟩
  by_contra hge
  push Not at hge
  exact absurd hle (not_le.mpr (R.gt_of_gridPt hge))

omit [Field F] [DecidableEq F] [Nonempty ι] in
/-- The adjacent-grid list-decoding boundary index is unique. -/
theorem kStar_unique (R R' : GrandListResolution C m ε_star) : R.kStar = R'.kStar := by
  rcases lt_trichotomy R.kStar R'.kStar with h | h | h
  · exact absurd
      (le_trans (lambda_mono_nnreal (gridPt_mono (by omega : R.kStar + 1 ≤ R'.kStar))) R'.below)
      (not_le.mpr R.above)
  · exact h
  · exact absurd
      (le_trans (lambda_mono_nnreal (gridPt_mono (by omega : R'.kStar + 1 ≤ R.kStar))) R.below)
      (not_le.mpr R'.above)

end GrandListResolution

/-- An adjacent list-size boundary satisfies the logical challenge. -/
theorem GrandListResolution.to_challenge
    {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (R : GrandListResolution C m ε_star) : grandListDecodingChallenge C m ε_star :=
  Or.inl ⟨R.kStar, R.lt_card, R.below, R.above⟩

/-- A list-decoding answer: either an adjacent boundary or an endpoint certificate. -/
inductive GrandListAnswer (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) : Type where
  /-- An adjacent-boundary answer. -/
  | boundary (R : GrandListResolution C m ε_star)
  /-- Safety at every grid point through radius one. -/
  | allGood
      (h : ∀ k : ℕ, k ≤ Fintype.card ι →
        (Code.Lambda (C ^⋈ (Fin m)) (gridPt (ι := ι) k : ℝ) : ENNReal) ≤
          (ε_star : ENNReal) * (Fintype.card F : ENNReal))

/-- A list-decoding answer satisfies the logical challenge. -/
theorem GrandListAnswer.to_challenge
    {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (A : GrandListAnswer C m ε_star) : grandListDecodingChallenge C m ε_star := by
  cases A with
  | boundary R => exact R.to_challenge
  | allGood h => exact Or.inr h

/-- A list-decoding answer at each prize rate. -/
structure ListPrizeResolution (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (m : ℕ) : Type where
  /-- The interleaving width is nonempty. -/
  m_pos : 0 < m
  /-- The evaluation domain realizes all four prize rates exactly. -/
  admissible : PrizeDomainAdmissible ι
  /-- Per-rate prize answers. -/
  answer : ∀ j : Fin 4,
    GrandListAnswer
      (ReedSolomon.code domain (prizeDimension (ι := ι) j) : Set (ι → F))
      m (prizeThreshold : ℝ≥0)

/-- Per-rate list-decoding answers satisfy the prize proposition. -/
theorem ListPrizeResolution.to_prize {domain : ι ↪ F} [ReedSolomon.Smooth domain]
    {m : ℕ} (R : ListPrizeResolution domain m) : listDecodingPrize domain m :=
  ⟨R.m_pos, R.admissible, fun j => (R.answer j).to_challenge⟩

omit [Field F] [DecidableEq F] [Nonempty ι] in
/-- A safe list witness lies strictly below the unsafe edge of every resolution. -/
theorem ListLowerWitness.lt_boundary {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (w : ListLowerWitness C m ε_star) (R : GrandListResolution C m ε_star) :
    w.δ < gridPt (ι := ι) (R.kStar + 1) := by
  by_contra h
  push Not at h
  exact absurd w.bound (not_le.mpr (R.gt_of_gridPt h))

omit [Field F] [DecidableEq F] [Nonempty ι] in
/-- An unsafe list witness lies strictly above the safe edge of every resolution. -/
theorem ListUpperWitness.boundary_lt {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (w : ListUpperWitness C m ε_star) (R : GrandListResolution C m ε_star) :
    gridPt (ι := ι) R.kStar < w.δ := by
  by_contra h
  push Not at h
  exact absurd (R.le_of_gridPt h) (not_le.mpr w.exceeds)

/-- A list-size upper bound at a unit-interval radius gives a safe witness. -/
def ListLowerWitness.ofLe {C : Set (ι → F)} {m : ℕ} {ε_star δ : ℝ≥0}
    (hδ : δ ≤ 1)
    (h : (Code.Lambda (C^⋈(Fin m)) (δ : ℝ) : ENNReal) ≤
      (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    ListLowerWitness C m ε_star := ⟨δ, hδ, h⟩

/-- A list-size lower bound at a unit-interval radius gives an unsafe witness. -/
def ListUpperWitness.ofGt {C : Set (ι → F)} {m : ℕ} {ε_star δ : ℝ≥0}
    (hδ : δ ≤ 1)
    (h : (Code.Lambda (C^⋈(Fin m)) (δ : ℝ) : ENNReal) >
      (ε_star : ENNReal) * (Fintype.card F : ENNReal)) :
    ListUpperWitness C m ε_star := ⟨δ, hδ, h⟩

/-- A single word with an oversized point list gives an unsafe witness. This is the primitive
form: `Lambda` is a supremum over words, so exhibiting one word whose interleaved point list
outruns the threshold suffices, and no bound on any other word is needed.

It is the entry point for a concrete large-list construction, which produces exactly this shape —
a specific word together with a lower bound on its own list. -/
def ListUpperWitness.ofEncardGt {C : Set (ι → F)} {m : ℕ} {ε_star δ : ℝ≥0}
    (hδ : δ ≤ 1) (f : ι → (Fin m → F))
    (h : (ε_star : ENNReal) * (Fintype.card F : ENNReal) <
      ((Code.closeCodewordsRel (C^⋈(Fin m)) f (δ : ℝ)).encard : ENNReal)) :
    ListUpperWitness C m ε_star :=
  ListUpperWitness.ofGt hδ
    (lt_of_lt_of_le h (by
      exact_mod_cast Code.encard_closeCodewordsRel_le_Lambda (C ^⋈ (Fin m)) (δ : ℝ) f))

end GrandChallenges

end ProximityGap
