/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Grand Challenges from ABF26 §1

The paper *Open Problems in List Decoding and Correlated Agreement* (Arnon, Boneh, Fenzi;
April 8, 2026) frames its survey around two open problems, stated on page 5:

1. **Grand MCA Challenge.** Given a Reed-Solomon code `C := RS[F, L, k]` over a smooth
   evaluation domain `L`, with constant rate `ρ(C) := k/|L| ∈ {1/2, 1/4, 1/8, 1/16}` and a
   threshold `ε*` (e.g. `2^(-128)`), determine the largest `δ*_C ∈ [0, 1]` such that
   `ε_mca(C, δ*_C) ≤ ε*`, assuming `|F|` is sufficiently large so that such a `δ*_C` exists.

2. **Grand List Decoding Challenge.** With the same RS setup and a constant interleaving
   parameter `m`, determine the largest `δ*_C ∈ [0, 1]` such that
   `|Λ(C^≡m, δ*_C)| ≤ ε* · |F|`, again assuming sufficiently large `|F|`.

The paper notes that resolving these challenges does not require an efficient
list-decoding algorithm; the questions are purely combinatorial.

## Formalisation choices: the boundary lives on the `1/n` grid

Both `ε_mca(C, δ)` and the maximised list size `Λ(C^⋈m, δ)` depend on `δ` only through an
integer threshold on the size of an agreement set `S ⊆ [n]` (`n := |L|`): `def:mca` gates
on `|S| ≥ (1-δ)·n`, and list membership on relative distance `δᵣ ≤ δ`. Since `|S|` and the
distance counts are integers, both quantities are **right-continuous step functions**,
constant on every cell `[j/n, (j+1)/n)` and changing only at grid points `j/n`. Hence the
sublevel set `{δ : ε_mca(δ) ≤ ε*}` is a *right-open* interval `[0, (k*+1)/n)`.

**Consequence.** "The largest `δ*` with `ε_mca(δ*) ≤ ε*`" (the paper's challenge box,
`[ABF26]` §1, ef-millenium.tex L835) is generically *unattained* — no real `δ*` satisfies
both `ε_mca(δ*) ≤ ε*` and `ε_mca(δ) > ε*` for all `δ > δ*`. The paper's operational
*resolution criterion* (L841–845) asks only to "specify `δ*` … and prove that for all
`δ > δ*`, `ε_mca(C, δ) > ε*`". We therefore formalise a resolution as the **boundary grid
index** `k`: the two facts `ε_mca(k/n) ≤ ε*` and `ε_mca((k+1)/n) > ε*` pin the threshold to
the cell `(k/n, (k+1)/n]` — the finest resolution the challenge admits — and monotonicity
(`epsMCA_mono` / `Lambda_mono`) extends them to the whole line. This form is *satisfiable*
(at `k = k*`), *constructive* (the answer is the integer `k`), and needs only monotonicity.

Resolution paths (one-sided progress):

- **Upper-bound progress**: any `ε_mca(C, δ) ≤ ε*` at a grid point is an `MCALowerWitness`,
  forcing `δ ≤ k/n`. Table 1 of the paper (`BCIKS20`, `BCHKS25`, `GG25`, …) supplies these.
- **Lower-bound progress**: any `ε_mca(C, δ) > ε*` is an `MCAUpperWitness`, forcing the
  boundary below `δ`. The bracket `[lower, upper]` tightens toward a single cell.

The two challenges sit at the centre of the dependency graph of the paper: §3 list-decoding
bounds feed into the list-decoding challenge directly, and §4 / §5 results bound `ε_mca`
either above (for the upper-bound direction) or below (for the lower-bound direction).
-/

-- Several framework lemmas use only a subset of the `ι`/`F` typeclass instances in their
-- types; suppress the noisy `unused...InType` / `unusedSectionVars` warnings file-wide here,
-- matching the idiom in `Errors.lean` and `CapacityBounds.lean`.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal

universe u

/-! ## The `1/n` grid

`ε_mca` and `Λ` only change at relative distances `k/n` (`n := |ι| = |L|`), so the
challenges are posed on this grid. `gridPt k := k/n`. -/

/-- Grid point `k/n ∈ ℝ≥0` (relative distance with denominator `n := |ι|`). -/
noncomputable def gridPt {ι : Type} [Fintype ι] (k : ℕ) : ℝ≥0 :=
  (k : ℝ≥0) / (Fintype.card ι : ℝ≥0)

/-- `k ≤ n ⇒ k/n ≤ 1`. -/
theorem gridPt_le_one {ι : Type} [Fintype ι] [Nonempty ι] {k : ℕ}
    (hk : k ≤ Fintype.card ι) : gridPt (ι := ι) k ≤ 1 := by
  have hn : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  rw [gridPt, div_le_one hn]; exact_mod_cast hk

/-- The grid is monotone: `k ≤ k' ⇒ k/n ≤ k'/n`. -/
theorem gridPt_mono {ι : Type} [Fintype ι] {k k' : ℕ} (h : k ≤ k') :
    gridPt (ι := ι) k ≤ gridPt (ι := ι) k' := by
  unfold gridPt; gcongr

/-- Monotonicity of `ε_mca` along the grid: `k ≤ k' ⇒ ε_mca(k/n) ≤ ε_mca(k'/n)`. -/
theorem epsMCA_gridPt_mono {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (C : Set (ι → F)) {k k' : ℕ} (h : k ≤ k') :
    epsMCA (F := F) (A := F) C (gridPt (ι := ι) k) ≤
      epsMCA (F := F) (A := F) C (gridPt (ι := ι) k') :=
  epsMCA_mono C (gridPt_mono h)

/-- **ABF26 §1 Grand MCA Challenge** (boundary form).

The boundary grid index `k`: `ε_mca(C, k/n) ≤ ε*` and `ε_mca(C, (k+1)/n) > ε*`, so the true
threshold lies in the cell `(k/n, (k+1)/n]`. Since `ε_mca` changes only at grid points, this
determines the challenge's answer to its finest meaningful resolution.

This replaces the earlier "largest real `δ*` with `ε_mca(δ*) ≤ ε*` and strict failure
above" form, which is *unsatisfiable* for a right-continuous step function (the sublevel set
`[0,(k*+1)/n)` has no attained maximum). The present form is the honest reading of the
paper's resolution criterion (`[ABF26]` §1, ef-millenium.tex L841–845) and, unlike a bare
existential over reals, cannot be discharged by a spurious `δ* = 1`: it asserts an actual
crossing `ε_mca(k/n) ≤ ε* < ε_mca((k+1)/n)`. The *challenge* is exhibiting `k` (data,
`GrandMCAResolution`); this predicate is its logical trace.

**Scope.** Requiring an actual crossing (`k < n` with `ε_mca((k+1)/n) > ε*`) deliberately
excludes the degenerate all-good regime where `ε_mca(δ) ≤ ε*` for every `δ ∈ [0,1]` (answer
`δ* = 1`): there the predicate is truthfully *false* (no crossing exists), not a resolution.
This is immaterial for the prize regime — `ε_mca(1)` is ~`1 ≫ 2^(-128)` for any real
Reed-Solomon code, so a crossing always exists — but it is a genuine narrowing versus the
paper's literal `δ* ∈ [0,1]`, recorded here rather than papered over. -/
def grandMCAChallenge {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C : LinearCode ι F) (ε_star : ℝ≥0) : Prop :=
  ∃ k : ℕ, k < Fintype.card ι ∧
    epsMCA (F := F) (A := F) ((C : Set (ι → F))) (gridPt (ι := ι) k) ≤ (ε_star : ENNReal) ∧
    epsMCA (F := F) (A := F) ((C : Set (ι → F))) (gridPt (ι := ι) (k + 1)) > (ε_star : ENNReal)

/-- **ABF26 §1 Grand List Decoding Challenge** (boundary form).

The boundary grid index `k` for the maximised list size `Λ(C^≡m, δ)` (ABF26 D2.8) against
the threshold `ε* · |F|`. Like `ε_mca`, `Λ` is a step function in `δ` (list membership is
`δᵣ ≤ δ`, and relative distance is `1/n`-quantised), so the same boundary-cell reading
applies. The bound `ε* · |F|` is read in `ENNReal` to handle the `Λ = ⊤` edge case
uniformly. -/
def grandListDecodingChallenge {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) : Prop :=
  ∃ k : ℕ, k < Fintype.card ι ∧
    (ListDecodable.Lambda (C^⋈ (Fin m)) (gridPt (ι := ι) k : ℝ) : ENNReal) ≤
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) ∧
    (ListDecodable.Lambda (C^⋈ (Fin m)) (gridPt (ι := ι) (k + 1) : ℝ) : ENNReal) >
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal))

/-! ## Prize parameter regime (ABF26 §1)

The two grand-challenge boxes fix the rate to one of `{1/2, 1/4, 1/8, 1/16}` and the
threshold to `ε* = 2^(-128)`. These are paper-level numeric choices; we expose them as
`ℝ≥0` constants so the prize can be stated as a `Fin 4`-indexed family. -/

open scoped NNReal

/-- **ABF26 §1 prize rates** `{1/2, 1/4, 1/8, 1/16}`, indexed by `Fin 4` via
`ρ_j := 2^(-(j+1))`. -/
noncomputable def prizeRates (j : Fin 4) : ℝ≥0 := 1 / 2 ^ (j.val + 1)

/-- **ABF26 §1 negligibility threshold** `ε* := 2^(-128)`. -/
noncomputable def epsStar : ℝ≥0 := 1 / 2 ^ (128 : ℕ)

namespace GrandChallenges

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## Reed-Solomon + rate targets

The grand challenges are posed for `C := RS[F, L, k]` **over a smooth evaluation
domain** `L` — both prize boxes in ABF26 §1 fix "a Reed-Solomon code defined over some
smooth evaluation domain `L ⊆ F`" (a multiplicative coset of a subgroup of `F*` of
power-of-two order, ABF26 Definition 2.x / `def:smooth`). We carry this as a
`ReedSolomon.Smooth domain` instance argument — the same in-tree encoding used by
`rs_epsCA_lower_capacity_kkh26` in `CapacityBounds` — so a claimed prize resolution
cannot target a non-smooth domain. These specialisations plug the Reed-Solomon code
directly into the generic predicates; a rate-addressed companion sets `k := ⌊ρ · |L|⌋`. -/

/-- The **Grand MCA Challenge** for `C := RS[F, domain, k]` over a smooth domain. -/
def grandMCAChallengeRS (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (k : ℕ) (ε_star : ℝ≥0) : Prop :=
  grandMCAChallenge (ReedSolomon.code domain k) ε_star

/-- The **Grand MCA Challenge** for the Reed-Solomon code of rate `ρ` over a smooth
domain, i.e. `k := ⌊ρ · |L|⌋`. -/
def grandMCAChallengeRSrate (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (ρ ε_star : ℝ≥0) : Prop :=
  grandMCAChallengeRS domain ⌊ρ * (Fintype.card ι : ℝ≥0)⌋₊ ε_star

/-- The **Grand List Decoding Challenge** for `C := RS[F, domain, k]` over a smooth
domain, `m`-fold interleaved. -/
def grandListDecodingChallengeRS (domain : ι ↪ F) [ReedSolomon.Smooth domain]
    (k m : ℕ) (ε_star : ℝ≥0) : Prop :=
  grandListDecodingChallenge (ReedSolomon.code domain k : Set (ι → F)) m ε_star

/-- The **ABF26 §1 MCA prize**: resolve the Grand MCA Challenge (over a smooth domain)
at *every* prize rate `ρ ∈ {1/2,1/4,1/8,1/16}` with `ε* = 2^(-128)`. -/
def mcaPrize (domain : ι ↪ F) [ReedSolomon.Smooth domain] : Prop :=
  ∀ j : Fin 4, grandMCAChallengeRSrate domain (prizeRates j) epsStar

/-- The **ABF26 §1 list-decoding prize** at interleaving `m`: resolve the Grand List
Decoding Challenge (over a smooth domain) at every prize rate with `ε* = 2^(-128)`. -/
def listDecodingPrize (domain : ι ↪ F) [ReedSolomon.Smooth domain] (m : ℕ) : Prop :=
  ∀ j : Fin 4,
    grandListDecodingChallengeRS domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ m epsStar

/-! ## Witness-carrying resolutions for the Grand MCA Challenge

A `GrandMCAResolution` is the boundary grid index the challenge asks for: `ε_mca` within
`ε*` at `k/n` and exceeding it at `(k+1)/n`. The two one-sided witnesses record *partial*
progress — a verified upper bound on `ε_mca` at some radius (forcing the boundary `≥`
there) or a verified lower bound (forcing the boundary `≤`). Each one-sided witness pins one
end of the search interval and accumulates monotonically as the bounds in `CapacityBounds`
tighten. -/

/-- A full resolution of the Grand MCA Challenge for `C` at threshold `ε*`: the boundary
grid index `k`. Satisfiable (at `k = k*`) and constructive, unlike the unattained
"largest real `δ*`" form. -/
structure GrandMCAResolution (C : Set (ι → F)) (ε_star : ℝ≥0) where
  /-- The boundary grid index `k` (the true threshold lies in `(k/n, (k+1)/n]`). -/
  k : ℕ
  /-- `k < n`, so both `k/n` and `(k+1)/n` lie in `[0, 1]`. -/
  lt_card : k < Fintype.card ι
  /-- `ε_mca(C, k/n) ≤ ε*` — the bound still holds at `k/n`. -/
  below : epsMCA (F := F) (A := F) C (gridPt (ι := ι) k) ≤ (ε_star : ENNReal)
  /-- `ε_mca(C, (k+1)/n) > ε*` — the bound has failed by the next grid point. -/
  above : epsMCA (F := F) (A := F) C (gridPt (ι := ι) (k + 1)) > (ε_star : ENNReal)

/-- **Lower one-sided progress.** A radius `δ ≤ 1` at which `ε_mca` is still within `ε*`.
Forces the boundary `≥ δ`. -/
structure MCALowerWitness (C : Set (ι → F)) (ε_star : ℝ≥0) where
  /-- The certified radius. -/
  δ : ℝ≥0
  /-- `δ ∈ [0, 1]`. -/
  le_one : δ ≤ 1
  /-- `ε_mca(C, δ) ≤ ε*`. -/
  bound : epsMCA (F := F) (A := F) C δ ≤ (ε_star : ENNReal)

/-- **Upper one-sided progress.** A radius `δ` at which `ε_mca` already exceeds `ε*`.
Forces the boundary `≤ δ`. -/
structure MCAUpperWitness (C : Set (ι → F)) (ε_star : ℝ≥0) where
  /-- The certified radius. -/
  δ : ℝ≥0
  /-- `ε_mca(C, δ) > ε*`. -/
  exceeds : epsMCA (F := F) (A := F) C δ > (ε_star : ENNReal)

namespace GrandMCAResolution

variable {C : Set (ι → F)} {ε_star : ℝ≥0}

/-- Below the boundary cell (`δ ≤ k/n`), `ε_mca` is within `ε*`. -/
theorem le_of_gridPt (R : GrandMCAResolution C ε_star) {δ : ℝ≥0}
    (hδ : δ ≤ gridPt (ι := ι) R.k) :
    epsMCA (F := F) (A := F) C δ ≤ (ε_star : ENNReal) :=
  le_trans (epsMCA_mono C hδ) R.below

/-- At or above the next grid point (`(k+1)/n ≤ δ`), `ε_mca` exceeds `ε*`. -/
theorem gt_of_gridPt (R : GrandMCAResolution C ε_star) {δ : ℝ≥0}
    (hδ : gridPt (ι := ι) (R.k + 1) ≤ δ) :
    epsMCA (F := F) (A := F) C δ > (ε_star : ENNReal) :=
  lt_of_lt_of_le R.above (epsMCA_mono C hδ)

/-- **Paper resolution criterion (ABF26 §1, ef-millenium.tex L841–845).** A resolution meets
the paper's operational criterion at `δ* := (k+1)/n`: `ε_mca(δ) > ε*` for every `δ > δ*`.
Non-vacuity (that `δ*` is not spuriously large) is witnessed separately by `below`. -/
theorem paper_criterion (R : GrandMCAResolution C ε_star) :
    ∀ δ : ℝ≥0, gridPt (ι := ι) (R.k + 1) < δ →
      epsMCA (F := F) (A := F) C δ > (ε_star : ENNReal) :=
  fun _ hδ => R.gt_of_gridPt (le_of_lt hδ)

/-- A resolution yields a lower one-sided witness at `k/n`. -/
noncomputable def toLowerWitness (R : GrandMCAResolution C ε_star) : MCALowerWitness C ε_star :=
  ⟨gridPt (ι := ι) R.k, gridPt_le_one (le_of_lt R.lt_card), R.below⟩

/-- A resolution yields an upper one-sided witness at `(k+1)/n`. -/
noncomputable def toUpperWitness (R : GrandMCAResolution C ε_star) : MCAUpperWitness C ε_star :=
  ⟨gridPt (ι := ι) (R.k + 1), R.above⟩

end GrandMCAResolution

/-- A resolution *is* a proof of the Grand MCA Challenge predicate. -/
theorem grandMCAChallenge_of_resolution {C : LinearCode ι F} {ε_star : ℝ≥0}
    (R : GrandMCAResolution (C : Set (ι → F)) ε_star) :
    grandMCAChallenge C ε_star :=
  ⟨R.k, R.lt_card, R.below, R.above⟩

/-- A lower witness sits strictly below the upper edge of the boundary cell:
`w.δ < (k+1)/n` for any resolution. -/
theorem MCALowerWitness.lt_boundary {C : Set (ι → F)} {ε_star : ℝ≥0}
    (w : MCALowerWitness C ε_star) (R : GrandMCAResolution C ε_star) :
    w.δ < gridPt (ι := ι) (R.k + 1) := by
  by_contra h
  push Not at h
  exact absurd w.bound (not_le.mpr (R.gt_of_gridPt h))

/-- An upper witness sits strictly above the lower edge of the boundary cell:
`k/n < w.δ` for any resolution. Uses `epsMCA_mono`. -/
theorem MCAUpperWitness.boundary_lt {C : Set (ι → F)} {ε_star : ℝ≥0}
    (w : MCAUpperWitness C ε_star) (R : GrandMCAResolution C ε_star) :
    gridPt (ι := ι) R.k < w.δ := by
  by_contra h
  push Not at h
  exact absurd (R.le_of_gridPt h) (not_le.mpr w.exceeds)

/-! ## Generic bridges: a single `ε_mca` / `ε_ca` bound is a one-sided witness

These are the connective edges from `CapacityBounds`. Each is pure plumbing — sorry-free
even though the bounds they will consume are external admits. -/

/-- **Bridge (upper bound ⇒ lower witness).** Any `ε_mca(C, δ) ≤ ε*` at `δ ≤ 1` is an
`MCALowerWitness`. -/
def MCALowerWitness.ofLe {C : Set (ι → F)} {ε_star δ : ℝ≥0}
    (hδ : δ ≤ 1) (h : epsMCA (F := F) (A := F) C δ ≤ (ε_star : ENNReal)) :
    MCALowerWitness C ε_star := ⟨δ, hδ, h⟩

/-- **Bridge (lower bound ⇒ upper witness).** Any `ε_mca(C, δ) > ε*` is an
`MCAUpperWitness`. -/
def MCAUpperWitness.ofGt {C : Set (ι → F)} {ε_star δ : ℝ≥0}
    (h : epsMCA (F := F) (A := F) C δ > (ε_star : ENNReal)) :
    MCAUpperWitness C ε_star := ⟨δ, h⟩

/-- **Bridge (CA lower bound ⇒ upper witness).** For a `Submodule` code, `ε_ca(C, δ, δ) > ε*`
forces `ε_mca(C, δ) > ε*` via `ε_ca ≤ ε_mca` (ABF26 Fact 4.5, `epsCA_le_epsMCA`). This is
the connective used by the §4 *lower* bounds, which are stated in terms of `ε_ca`. -/
def MCAUpperWitness.ofEpsCAGt {MC : Submodule F (ι → F)} {ε_star δ : ℝ≥0}
    (h : epsCA (F := F) (A := F) (MC : Set (ι → F)) δ δ > (ε_star : ENNReal)) :
    MCAUpperWitness (MC : Set (ι → F)) ε_star :=
  ⟨δ, lt_of_lt_of_le h (epsCA_le_epsMCA MC δ)⟩

/-! ## Concrete bridges from `CapacityBounds`

One representative of each direction, consuming an actual external-admit bound. The
numeric hypotheses (`hle` / `h_gt`) — that the explicit symbolic right-hand side compares
to `ε*` as required — are the Phase-5 computations; here we wire the symbolic edge. -/

/-- **Bridge from ABF26 Theorem 4.12 [BCHKS25 Thm 4.6].** When the Johnson-range MCA bound
for `RS[F, domain, k]` lands within `ε*` at radius `δ`, it certifies an `MCALowerWitness`.
The hypothesis `hle` is the Phase-5 numeric check that the explicit BCHKS25 RHS is `≤ ε*`. -/
def MCALowerWitness.ofJohnsonBCHKS25
    (domain : ι ↪ F) (k : ℕ) (η δ ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) - (η : ℝ))
    (hδ_le_one : δ ≤ 1)
    (hle :
        ENNReal.ofReal
          (let n : ℝ := Fintype.card ι
           let ρ_plus : ℝ := k / n + 1 / n
           let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
           ((2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * δ * ρ_plus)
              / (3 * ρ_plus ^ ((3 : ℝ) / 2)) * n
            + (m + 1/2) / ρ_plus ^ ((1 : ℝ) / 2))
             / (Fintype.card F : ℝ)) ≤ (ε_star : ENNReal)) :
    MCALowerWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star :=
  MCALowerWitness.ofLe hδ_le_one
    (le_trans (CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ_johnson) hle)

/-! ## §4.5 conjecture and its positive-direction link to the prize

ABF26 Conjecture `conj:mca-conjecture` posits a uniform polynomial upper bound on `ε_mca`
for *all* Reed-Solomon codes. If it holds, every radius `δ < 1 - ρ` whose conjectural bound
is `≤ ε*` is a lower witness — the conjecture would directly fuel one-sided MCA progress. -/

/-- The right-hand side of the §4.5 MCA conjecture, as a real number:
`(1/|F|) · |L|^{c₁} / (ρ^{c₂} · η^{c₃})` with `ρ := k/|L|` and `η := 1 - ρ - δ`. -/
noncomputable def mcaConjectureBound (n q k : ℕ) (δ : ℝ≥0) (c₁ c₂ c₃ : ℝ) : ℝ :=
  (1 / (q : ℝ)) * (n : ℝ) ^ c₁
    / (((k : ℝ) / n) ^ c₂ * (1 - (k : ℝ) / n - (δ : ℝ)) ^ c₃)

/-- **ABF26 §4.5 Conjecture (`conj:mca-conjecture`).** There exist constants `c₁, c₂, c₃`
such that for every Reed-Solomon code `RS[F, L, k]` of rate `ρ := k/|L|` and every
`δ < 1 - ρ`, `ε_mca(C, δ) ≤ (1/|F|) · |L|^{c₁} / (ρ^{c₂} · η^{c₃})` with `η := 1 - ρ - δ`.
The constants are existentially quantified *over all RS codes*, matching the paper.

**Positive-rate hypothesis `0 < k`.** The bound has `ρ^{c₂}` in a denominator, so it is
only meaningful for positive rate `ρ = k/|L| > 0`; the prize regime `ρ ∈ {1/2,…,1/16}` is
positive anyway. We make this explicit (cf. the explicit denominator-positivity hypotheses
in `CapacityBounds`): without it the `k = 0` case would, under real division's `x/0 = 0`
convention, collapse the right-hand side to `0` and assert `ε_mca ≤ 0` (a degenerate
*strengthening*, not the intended trivially-true `+∞`).

**Source status (verified 2026-06-03).** In the current `[ABF26]` `.tex` source this
conjecture lives inside an `\ignore{…}` block (around line 2030), i.e. it is a *draft*
statement not rendered in the compiled paper. The term-by-term content here is faithful to
that draft; treat it as tracking a draft conjecture, not a stable rendered theorem. -/
def mcaConjecture : Prop :=
  ∃ c₁ c₂ c₃ : ℝ,
    ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
      {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
      (domain : ιC ↪ FC) (k : ℕ) (δ : ℝ≥0),
      0 < k →
      (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC →
      epsMCA (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC))) δ ≤
        ENNReal.ofReal
          (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃)

/-- **Positive-direction link to the prize.** Under the §4.5 MCA conjecture, for the
exposed constants, any RS code and radius `δ < 1 - ρ` with `δ ≤ 1` whose conjectural bound
is `≤ ε*` admits an `MCALowerWitness`. (`MCALowerWitness` is data, so the conclusion is its
`Nonempty`-ification — the constants `c₁ c₂ c₃` come from the conjecture's `Prop`-level
existential.) See `[ABF26]` §4.5, Conjecture `conj:mca-conjecture`. -/
theorem nonempty_mcaLowerWitness_of_mcaConjecture (h : mcaConjecture) :
    ∃ c₁ c₂ c₃ : ℝ,
      ∀ {ιC : Type} [Fintype ιC] [Nonempty ιC] [DecidableEq ιC]
        {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC]
        (domain : ιC ↪ FC) (k : ℕ) (ε_star δ : ℝ≥0),
        0 < k →
        (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ιC → δ ≤ 1 →
        ENNReal.ofReal
            (mcaConjectureBound (Fintype.card ιC) (Fintype.card FC) k δ c₁ c₂ c₃) ≤
          (ε_star : ENNReal) →
        Nonempty (MCALowerWitness (ReedSolomon.code domain k : Set (ιC → FC)) ε_star) := by
  obtain ⟨c₁, c₂, c₃, hbound⟩ := h
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro ιC _ _ _ FC _ _ _ domain k ε_star δ hk hδ hδ1 hle
  exact ⟨⟨δ, hδ1, le_trans (hbound domain k δ hk hδ) hle⟩⟩

/-! ## Witness-carrying resolutions for the Grand List Decoding Challenge

The list-decoding mirror of the MCA framework. The maximised list size `Λ(C^⋈m, δ)`
(ABF26 D2.8) plays the role of `ε_mca`, the threshold is `ε* · |F|`, and monotonicity of
`Λ` in the radius (`ListDecodable.Lambda_mono`) replaces `epsMCA_mono`. The boundary form is
identical: `Λ` is a step function on the `1/n` grid, so the resolution is a grid index `k`. -/

/-- A full resolution of the Grand List Decoding Challenge for `C`, `m`-fold interleaved:
the boundary grid index `k`. -/
structure GrandListResolution (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) where
  /-- The boundary grid index `k`. -/
  k : ℕ
  /-- `k < n`. -/
  lt_card : k < Fintype.card ι
  /-- `|Λ(C^⋈m, k/n)| ≤ ε* · |F|`. -/
  below : (ListDecodable.Lambda (C^⋈ (Fin m)) (gridPt (ι := ι) k : ℝ) : ENNReal) ≤
    ((ε_star : ENNReal) * (Fintype.card F : ENNReal))
  /-- `|Λ(C^⋈m, (k+1)/n)| > ε* · |F|`. -/
  above : (ListDecodable.Lambda (C^⋈ (Fin m)) (gridPt (ι := ι) (k + 1) : ℝ) : ENNReal) >
    ((ε_star : ENNReal) * (Fintype.card F : ENNReal))

/-- **Lower one-sided progress** for list decoding. A radius `δ ≤ 1` at which the list
size is still within `ε* · |F|`. Forces the boundary `≥ δ`. -/
structure ListLowerWitness (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) where
  /-- The certified radius. -/
  δ : ℝ≥0
  /-- `δ ∈ [0, 1]`. -/
  le_one : δ ≤ 1
  /-- `|Λ(C^⋈m, δ)| ≤ ε* · |F|`. -/
  bound : (ListDecodable.Lambda (C^⋈ (Fin m)) (δ : ℝ) : ENNReal) ≤
    ((ε_star : ENNReal) * (Fintype.card F : ENNReal))

/-- **Upper one-sided progress** for list decoding. A radius `δ` at which the list size
already exceeds `ε* · |F|`. Forces the boundary `≤ δ`. -/
structure ListUpperWitness (C : Set (ι → F)) (m : ℕ) (ε_star : ℝ≥0) where
  /-- The certified radius. -/
  δ : ℝ≥0
  /-- `|Λ(C^⋈m, δ)| > ε* · |F|`. -/
  exceeds : (ListDecodable.Lambda (C^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
    ((ε_star : ENNReal) * (Fintype.card F : ENNReal))

/-- Monotonicity of the (coerced) maximised list size in the radius — the list-decoding
analogue of `epsMCA_mono`, lifted from `ListDecodable.Lambda_mono`. -/
theorem lambda_coe_mono {C : Set (ι → F)} {m : ℕ} {a b : ℝ≥0} (hab : a ≤ b) :
    (ListDecodable.Lambda (C^⋈ (Fin m)) (a : ℝ) : ENNReal) ≤
    (ListDecodable.Lambda (C^⋈ (Fin m)) (b : ℝ) : ENNReal) := by
  have hr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  exact_mod_cast ListDecodable.Lambda_mono (C := C^⋈ (Fin m)) hr

namespace GrandListResolution

variable {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}

/-- Below the boundary cell (`δ ≤ k/n`), the list size is within `ε* · |F|`. -/
theorem le_of_gridPt (R : GrandListResolution C m ε_star) {δ : ℝ≥0}
    (hδ : δ ≤ gridPt (ι := ι) R.k) :
    (ListDecodable.Lambda (C^⋈ (Fin m)) (δ : ℝ) : ENNReal) ≤
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) :=
  le_trans (lambda_coe_mono hδ) R.below

/-- At or above the next grid point (`(k+1)/n ≤ δ`), the list size exceeds `ε* · |F|`. -/
theorem gt_of_gridPt (R : GrandListResolution C m ε_star) {δ : ℝ≥0}
    (hδ : gridPt (ι := ι) (R.k + 1) ≤ δ) :
    (ListDecodable.Lambda (C^⋈ (Fin m)) (δ : ℝ) : ENNReal) >
      ((ε_star : ENNReal) * (Fintype.card F : ENNReal)) :=
  lt_of_lt_of_le R.above (lambda_coe_mono hδ)

end GrandListResolution

/-- A list-decoding resolution *is* a proof of the Grand List Decoding Challenge predicate. -/
theorem grandListDecodingChallenge_of_resolution {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (R : GrandListResolution C m ε_star) :
    grandListDecodingChallenge C m ε_star :=
  ⟨R.k, R.lt_card, R.below, R.above⟩

/-- A list lower witness sits strictly below the upper edge of the boundary cell. -/
theorem ListLowerWitness.lt_boundary {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (w : ListLowerWitness C m ε_star) (R : GrandListResolution C m ε_star) :
    w.δ < gridPt (ι := ι) (R.k + 1) := by
  by_contra h
  push Not at h
  exact absurd w.bound (not_le.mpr (R.gt_of_gridPt h))

/-- A list upper witness sits strictly above the lower edge of the boundary cell. -/
theorem ListUpperWitness.boundary_lt {C : Set (ι → F)} {m : ℕ} {ε_star : ℝ≥0}
    (w : ListUpperWitness C m ε_star) (R : GrandListResolution C m ε_star) :
    gridPt (ι := ι) R.k < w.δ := by
  by_contra h
  push Not at h
  exact absurd (R.le_of_gridPt h) (not_le.mpr w.exceeds)

/-! ## First instantiation: the symbolic ρ = 1/2 interval (Phase 1 scaffold)

Phase 1 wires the *symbolic* search interval for the boundary; the numeric endpoints (which
prize rate, which `δ` make the explicit RHS compare to `ε*`) are Phase 5. The lemma below
records that the two one-sided witnesses bracket the boundary cell of any resolution — the
shape `[boundary ≥ Johnson-range lower witness (T4.12 [BCHKS25], [Hab25]), boundary ≤
capacity upper witness (T4.16 [BCHKS25], [KK25])]` that one-sided progress accumulates into.
See `[ABF26]` §1 (Grand MCA Challenge) and §4.2. -/

/-- **Symbolic bracket (ρ = 1/2 scaffold).** For an RS code at threshold `ε*`, a
Johnson-range lower witness and a capacity upper witness bracket the boundary cell
`(k/n, (k+1)/n]` of any resolution: `k/n < δ_hi` and `δ_lo < (k+1)/n`. This is the
connective the per-rate prize progress accumulates into; instantiate `wlo` via
`MCALowerWitness.ofJohnsonBCHKS25` and `whi` via `MCAUpperWitness.ofEpsCAGt` once Phase-5
supplies the numeric checks. See `[ABF26]` §1 (Grand MCA Challenge). -/
theorem mca_threshold_bracketed
    (domain : ι ↪ F) (k : ℕ) (ε_star : ℝ≥0)
    (wlo : MCALowerWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star)
    (whi : MCAUpperWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star)
    (R : GrandMCAResolution (ReedSolomon.code domain k : Set (ι → F)) ε_star) :
    gridPt (ι := ι) R.k < whi.δ ∧ wlo.δ < gridPt (ι := ι) (R.k + 1) :=
  ⟨whi.boundary_lt R, wlo.lt_boundary R⟩

end GrandChallenges

end ProximityGap
