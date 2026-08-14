/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Grand challenges from ABF26 Section 1

The MCA and list-decoding prizes are integer-grid boundary problems. For a length-`n` code, a
resolution certifies that the target bound is safe at `k / n` and unsafe at `(k + 1) / n`. This
adjacent-cell convention is exact for MCA and makes its boundary index unique. The complete
challenge propositions also include the endpoint case where every grid point through radius one
is safe.

The MCA fields below mention the merged `CoreDefinitions.mcaError` value itself, specialized to
`AffineLineGenerator F`. No independent prize error function occurs in the scored contract.

This is the capacity-independent challenge core. Bounds from Sections 4--5 can construct its
generic witnesses from a separate extension module without making this file depend on a theorem
catalogue.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26]
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

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

/-- Real-valued version of `gridPt_mul_card`, used by the canonical `mcaError` floor API. -/
theorem gridPt_coe_mul_card {ι : Type} [Fintype ι] [Nonempty ι] (k : ℕ) :
    (gridPt (ι := ι) k : ℝ) * (Fintype.card ι : ℝ) = (k : ℝ) := by
  exact_mod_cast gridPt_mul_card (ι := ι) k

/-- Affine-line MCA is monotone along the integer-agreement grid. -/
theorem mcaError_gridPt_mono {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] (C : LinearCode ι F) {k k' : ℕ} (h : k ≤ k') :
    mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k : ℝ) ≤
      mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k' : ℝ) :=
  mcaError_mono (AffineLineGenerator F) C (by exact_mod_cast gridPt_mono h)

/-- Affine-line MCA is constant on equal integer-agreement floor cells. -/
theorem mcaError_eq_of_nnreal_floor_eq {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] (C : LinearCode ι F) {δ δ' : ℝ≥0}
    (h : ⌊(δ : ℝ) * (Fintype.card ι : ℝ)⌋₊ =
      ⌊(δ' : ℝ) * (Fintype.card ι : ℝ)⌋₊) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) =
      mcaError (AffineLineGenerator F) C (δ' : ℝ) :=
  mcaError_eq_of_floor_eq (AffineLineGenerator F) C (by positivity) (by positivity) h

/-! ## Logical challenge predicates -/

/-- **ABF26 Grand MCA Challenge**: an adjacent integer-grid crossing, or the `δ* = 1`
endpoint where every grid point through radius one is safe. -/
def grandMCAChallenge {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι]
    (C : LinearCode ι F) (ε_star : ℝ≥0) : Prop :=
  (∃ k : ℕ, k < Fintype.card ι ∧
      mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k : ℝ) ≤ (ε_star : ENNReal) ∧
      mcaError (AffineLineGenerator F) C (gridPt (ι := ι) (k + 1) : ℝ) >
        (ε_star : ENNReal)) ∨
    ∀ k : ℕ, k ≤ Fintype.card ι →
      mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k : ℝ) ≤ (ε_star : ENNReal)

/-- **ABF26 Grand List Decoding Challenge**: an adjacent integer-grid crossing, or the `δ* = 1`
endpoint where every grid point through radius one is safe. -/
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

/-- ABF26 prize rates `{1/2, 1/4, 1/8, 1/16}` as exact nonnegative rationals. -/
def prizeRates (j : Fin 4) : ℚ≥0 := 1 / 2 ^ (j.val + 1)

/-- ABF26 prize threshold `2⁻¹²⁸` as an exact nonnegative rational. -/
def epsStar : ℚ≥0 := 1 / 2 ^ (128 : ℕ)

namespace GrandChallenges

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Grand MCA challenge for an ordinary Reed--Solomon code over a smooth domain. -/
def grandMCAChallengeRS (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (k : ℕ) (ε_star : ℝ≥0) : Prop :=
  grandMCAChallenge (ReedSolomon.code domain k) ε_star

/-- Rate-addressed Grand MCA challenge, with message length `⌊ρ n⌋`. -/
def grandMCAChallengeRSrate (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (ρ ε_star : ℝ≥0) : Prop :=
  grandMCAChallengeRS domain ⌊ρ * (Fintype.card ι : ℝ≥0)⌋₊ ε_star

/-- Grand List Decoding Challenge for an ordinary Reed--Solomon code over a smooth domain. -/
def grandListDecodingChallengeRS (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (k m : ℕ) (ε_star : ℝ≥0) : Prop :=
  grandListDecodingChallenge (ReedSolomon.code domain k : Set (ι → F)) m ε_star

/-- Logical trace of the MCA prize at all four rates. -/
def mcaPrize (domain : ι ↪ F) [ReedSolomon.Smooth domain] : Prop :=
  ∀ j : Fin 4, grandMCAChallengeRSrate domain (prizeRates j : ℝ≥0) (epsStar : ℝ≥0)

/-- Logical trace of the list-decoding prize at all four rates. -/
def listDecodingPrize (domain : ι ↪ F) [ReedSolomon.Smooth domain] (m : ℕ) : Prop :=
  ∀ j : Fin 4,
    grandListDecodingChallengeRS domain
      ⌊(prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ m (epsStar : ℝ≥0)

/-! ## MCA boundary carriers -/

/-- A full MCA resolution: safe at `kStar / n`, unsafe at the adjacent grid point. -/
structure GrandMCAResolution (C : LinearCode ι F) (ε_star : ℝ≥0) where
  /-- Unique boundary grid index. -/
  kStar : ℕ
  /-- Both adjacent grid points lie in `[0,1]`. -/
  lt_card : kStar < Fintype.card ι
  /-- The error bound is safe at `kStar / n`. -/
  below : mcaError (AffineLineGenerator F) C (gridPt (ι := ι) kStar : ℝ) ≤
    (ε_star : ENNReal)
  /-- The error bound is unsafe at `(kStar + 1) / n`. -/
  above : mcaError (AffineLineGenerator F) C (gridPt (ι := ι) (kStar + 1) : ℝ) >
    (ε_star : ENNReal)

/-- One-sided safe MCA witness. -/
structure MCALowerWitness (C : LinearCode ι F) (ε_star : ℝ≥0) where
  /-- Certified radius. -/
  δ : ℝ≥0
  /-- The radius lies in `[0,1]`. -/
  le_one : δ ≤ 1
  /-- Canonical affine-line MCA is within the threshold. -/
  bound : mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal)

/-- One-sided unsafe MCA witness. -/
structure MCAUpperWitness (C : LinearCode ι F) (ε_star : ℝ≥0) where
  /-- Certified radius. -/
  δ : ℝ≥0
  /-- Canonical affine-line MCA exceeds the threshold. -/
  exceeds : mcaError (AffineLineGenerator F) C (δ : ℝ) > (ε_star : ENNReal)

namespace GrandMCAResolution

variable {C : LinearCode ι F} {ε_star : ℝ≥0}

/-- Below the safe grid point, the MCA bound remains safe. -/
theorem le_of_gridPt (R : GrandMCAResolution C ε_star) {δ : ℝ≥0}
    (hδ : δ ≤ gridPt (ι := ι) R.kStar) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal) :=
  le_trans (mcaError_mono (AffineLineGenerator F) C (by exact_mod_cast hδ)) R.below

/-- At or above the adjacent unsafe point, the MCA bound remains unsafe. -/
theorem gt_of_gridPt (R : GrandMCAResolution C ε_star) {δ : ℝ≥0}
    (hδ : gridPt (ι := ι) (R.kStar + 1) ≤ δ) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) > (ε_star : ENNReal) :=
  lt_of_lt_of_le R.above
    (mcaError_mono (AffineLineGenerator F) C (by exact_mod_cast hδ))

/-- Exact safe half of the boundary cell. -/
theorem le_of_lt_next (R : GrandMCAResolution C ε_star) {δ : ℝ≥0}
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
  rw [mcaError_eq_of_nnreal_floor_eq C hgrid.symm]
  exact le_trans (mcaError_gridPt_mono C hfloor) R.below

/-- The MCA sublevel set is exactly the right-open interval ending at the unsafe grid point. -/
theorem sublevel_iff (R : GrandMCAResolution C ε_star) {δ : ℝ≥0} :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal) ↔
      δ < gridPt (ι := ι) (R.kStar + 1) := by
  refine ⟨fun hle => ?_, R.le_of_lt_next⟩
  by_contra hge
  push Not at hge
  exact absurd hle (not_le.mpr (R.gt_of_gridPt hge))

/-- The adjacent-grid MCA boundary index is unique. -/
theorem kStar_unique (R R' : GrandMCAResolution C ε_star) : R.kStar = R'.kStar := by
  rcases lt_trichotomy R.kStar R'.kStar with h | h | h
  · exact absurd
      (le_trans (mcaError_gridPt_mono C (by omega : R.kStar + 1 ≤ R'.kStar)) R'.below)
      (not_le.mpr R.above)
  · exact h
  · exact absurd
      (le_trans (mcaError_gridPt_mono C (by omega : R'.kStar + 1 ≤ R.kStar)) R.below)
      (not_le.mpr R'.above)

/-- The paper's strict-above operational criterion at the upper edge of the boundary cell. -/
theorem paper_criterion (R : GrandMCAResolution C ε_star) :
    ∀ δ : ℝ≥0, gridPt (ι := ι) (R.kStar + 1) < δ →
      mcaError (AffineLineGenerator F) C (δ : ℝ) > (ε_star : ENNReal) :=
  fun _ hδ => R.gt_of_gridPt (le_of_lt hδ)

/-- A resolution supplies a safe one-sided witness. -/
noncomputable def toLowerWitness (R : GrandMCAResolution C ε_star) :
    MCALowerWitness C ε_star :=
  ⟨gridPt (ι := ι) R.kStar, gridPt_le_one (le_of_lt R.lt_card), R.below⟩

/-- A resolution supplies an unsafe one-sided witness. -/
noncomputable def toUpperWitness (R : GrandMCAResolution C ε_star) :
    MCAUpperWitness C ε_star :=
  ⟨gridPt (ι := ι) (R.kStar + 1), R.above⟩

end GrandMCAResolution

/-- A resolution proves the logical Grand MCA Challenge. -/
theorem grandMCAChallenge_of_resolution {C : LinearCode ι F} {ε_star : ℝ≥0}
    (R : GrandMCAResolution C ε_star) : grandMCAChallenge C ε_star :=
  Or.inl ⟨R.kStar, R.lt_card, R.below, R.above⟩

/-- Complete MCA answer data: an adjacent boundary, or a certificate that every grid point through
radius one is safe. -/
inductive GrandMCAAnswer (C : LinearCode ι F) (ε_star : ℝ≥0) : Type where
  /-- Generic adjacent-boundary answer. -/
  | boundary (R : GrandMCAResolution C ε_star)
  /-- Endpoint answer `δ* = 1`. -/
  | allGood
      (h : ∀ k : ℕ, k ≤ Fintype.card ι →
        mcaError (AffineLineGenerator F) C (gridPt (ι := ι) k : ℝ) ≤
          (ε_star : ENNReal))

/-- Every complete MCA answer proves the full logical challenge, including `allGood` at
`δ* = 1`. -/
theorem GrandMCAAnswer.toChallenge {C : LinearCode ι F} {ε_star : ℝ≥0}
    (A : GrandMCAAnswer C ε_star) : grandMCAChallenge C ε_star := by
  cases A with
  | boundary R => exact grandMCAChallenge_of_resolution R
  | allGood h => exact Or.inr h

/-- MCA submission data at all prize rates, over an ordinary smooth-domain RS code. -/
structure MCAPrizeResolution (domain : ι ↪ F) [ReedSolomon.Smooth domain] : Type where
  /-- Per-rate prize answers. -/
  answer : ∀ j : Fin 4,
    GrandMCAAnswer
      (ReedSolomon.code domain
        ⌊(prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊)
      (epsStar : ℝ≥0)

/-- Complete per-rate MCA answers prove the logical prize proposition. -/
theorem MCAPrizeResolution.toPrize {domain : ι ↪ F} [ReedSolomon.Smooth domain]
    (R : MCAPrizeResolution domain) : mcaPrize domain :=
  fun j => (R.answer j).toChallenge

/-- A safe witness lies strictly below the unsafe edge of every resolution. -/
theorem MCALowerWitness.lt_boundary {C : LinearCode ι F} {ε_star : ℝ≥0}
    (w : MCALowerWitness C ε_star) (R : GrandMCAResolution C ε_star) :
    w.δ < gridPt (ι := ι) (R.kStar + 1) := by
  by_contra h
  push Not at h
  exact absurd w.bound (not_le.mpr (R.gt_of_gridPt h))

/-- An unsafe witness lies strictly above the safe edge of every resolution. -/
theorem MCAUpperWitness.boundary_lt {C : LinearCode ι F} {ε_star : ℝ≥0}
    (w : MCAUpperWitness C ε_star) (R : GrandMCAResolution C ε_star) :
    gridPt (ι := ι) R.kStar < w.δ := by
  by_contra h
  push Not at h
  exact absurd (R.le_of_gridPt h) (not_le.mpr w.exceeds)

/-- Any canonical MCA upper bound at a unit-interval radius gives a safe witness. -/
def MCALowerWitness.ofLe {C : LinearCode ι F} {ε_star δ : ℝ≥0}
    (hδ : δ ≤ 1)
    (h : mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal)) :
    MCALowerWitness C ε_star := ⟨δ, hδ, h⟩

/-- Any canonical MCA lower bound gives an unsafe witness. -/
def MCAUpperWitness.ofGt {C : LinearCode ι F} {ε_star δ : ℝ≥0}
    (h : mcaError (AffineLineGenerator F) C (δ : ℝ) > (ε_star : ENNReal)) :
    MCAUpperWitness C ε_star := ⟨δ, h⟩

/-- A CA lower bound gives an unsafe MCA witness via ABF26 Fact 4.5. -/
def MCAUpperWitness.ofEpsCAGt {C : LinearCode ι F} {ε_star δ : ℝ≥0}
    (h : epsCA (F := F) (A := F) (C : Set (ι → F)) δ δ > (ε_star : ENNReal)) :
    MCAUpperWitness C ε_star :=
  ⟨δ, lt_of_lt_of_le h (epsCA_le_mcaError_affineLine C δ)⟩

/-! ## List-decoding boundary carriers -/

/-- A full list-decoding resolution on adjacent grid points. -/
structure GrandListResolution (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) where
  /-- Unique boundary grid index. -/
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
  /-- The list-size bound is unsafe. -/
  exceeds : (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
    (ε_star : ENNReal) * (Fintype.card F : ENNReal)

/-- Monotonicity of the maximized list size after coercion to `ENNReal`. -/
theorem lambda_coe_mono {C : Set (ι → F)} {m : ℕ} {a b : ℝ≥0} (hab : a ≤ b) :
    (Code.Lambda (C ^⋈ (Fin m)) (a : ℝ) : ENNReal) ≤
      (Code.Lambda (C ^⋈ (Fin m)) (b : ℝ) : ENNReal) := by
  have hr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  exact_mod_cast Code.Lambda_mono (C := C ^⋈ (Fin m)) hr

namespace GrandListResolution

variable {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}

/-- Below the safe list grid point, the bound remains safe. -/
theorem le_of_gridPt (R : GrandListResolution C m ε_star) {δ : ℝ≥0}
    (hδ : δ ≤ gridPt (ι := ι) R.kStar) :
    (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) ≤
      (ε_star : ENNReal) * (Fintype.card F : ENNReal) :=
  le_trans (lambda_coe_mono hδ) R.below

/-- At or above the adjacent unsafe list grid point, the bound remains unsafe. -/
theorem gt_of_gridPt (R : GrandListResolution C m ε_star) {δ : ℝ≥0}
    (hδ : gridPt (ι := ι) (R.kStar + 1) ≤ δ) :
    (Code.Lambda (C ^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
      (ε_star : ENNReal) * (Fintype.card F : ENNReal) :=
  lt_of_lt_of_le R.above (lambda_coe_mono hδ)

end GrandListResolution

/-- A list resolution proves the logical challenge. -/
theorem grandListDecodingChallenge_of_resolution
    {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (R : GrandListResolution C m ε_star) : grandListDecodingChallenge C m ε_star :=
  Or.inl ⟨R.kStar, R.lt_card, R.below, R.above⟩

/-- Complete list-decoding answer data, including the `δ* = 1` endpoint case. -/
inductive GrandListDecodingAnswer (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) : Type where
  /-- Generic adjacent-boundary answer. -/
  | boundary (R : GrandListResolution C m ε_star)
  /-- Endpoint answer `δ* = 1`. -/
  | allGood
      (h : ∀ k : ℕ, k ≤ Fintype.card ι →
        (Code.Lambda (C ^⋈ (Fin m)) (gridPt (ι := ι) k : ℝ) : ENNReal) ≤
          (ε_star : ENNReal) * (Fintype.card F : ENNReal))

/-- Every complete list-decoding answer proves the full logical challenge, including `allGood` at
`δ* = 1`. -/
theorem GrandListDecodingAnswer.toChallenge
    {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (A : GrandListDecodingAnswer C m ε_star) : grandListDecodingChallenge C m ε_star := by
  cases A with
  | boundary R => exact grandListDecodingChallenge_of_resolution R
  | allGood h => exact Or.inr h

/-- List-decoding submission data at all prize rates. -/
structure ListDecodingPrizeResolution (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (m : ℕ) : Type where
  /-- Per-rate prize answers. -/
  answer : ∀ j : Fin 4,
    GrandListDecodingAnswer
      (ReedSolomon.code domain
        ⌊(prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      m (epsStar : ℝ≥0)

/-- Complete per-rate list-decoding answers prove the logical prize proposition. -/
theorem ListDecodingPrizeResolution.toPrize {domain : ι ↪ F} [ReedSolomon.Smooth domain]
    {m : ℕ} (R : ListDecodingPrizeResolution domain m) : listDecodingPrize domain m :=
  fun j => (R.answer j).toChallenge

/-- A safe list witness lies strictly below the unsafe edge of every resolution. -/
theorem ListLowerWitness.lt_boundary {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (w : ListLowerWitness C m ε_star) (R : GrandListResolution C m ε_star) :
    w.δ < gridPt (ι := ι) (R.kStar + 1) := by
  by_contra h
  push Not at h
  exact absurd w.bound (not_le.mpr (R.gt_of_gridPt h))

/-- An unsafe list witness lies strictly above the safe edge of every resolution. -/
theorem ListUpperWitness.boundary_lt {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (w : ListUpperWitness C m ε_star) (R : GrandListResolution C m ε_star) :
    gridPt (ι := ι) R.kStar < w.δ := by
  by_contra h
  push Not at h
  exact absurd (R.le_of_gridPt h) (not_le.mpr w.exceeds)

/-- Generic symbolic bracket combining safe and unsafe one-sided MCA progress. -/
theorem mca_threshold_bracketed
    (domain : ι ↪ F) (k : ℕ) (ε_star : ℝ≥0)
    (wlo : MCALowerWitness (ReedSolomon.code domain k) ε_star)
    (whi : MCAUpperWitness (ReedSolomon.code domain k) ε_star)
    (R : GrandMCAResolution (ReedSolomon.code domain k) ε_star) :
    gridPt (ι := ι) R.kStar < whi.δ ∧
      wlo.δ < gridPt (ι := ι) (R.kStar + 1) :=
  ⟨whi.boundary_lt R, wlo.lt_boundary R⟩

end GrandChallenges

end ProximityGap
