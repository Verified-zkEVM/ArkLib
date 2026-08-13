/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.InformationTheory.Hamming
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Large-alphabet barrier: statements, coordinate blocks, and family counting

The **statement layer** of the [AGL23] exponential-alphabet barrier — the `AGL*` `Prop`
abbreviations, and the four structures (`AGLBarrierParameters`, `AGLCoordinateBlocks`,
`AGLLargeUnionFamily`, `AGLRoundedBarrierData`) that let obligations be passed around as values —
together with the coordinate-block constructions and the cardinality counting for the indexed
families of restrictions.

See `ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean` for the family overview and the
references, and `Bounds/LargeAlphabet.lean` for the two theorems this development serves.

## References

The keys cited here — [AGL23] — are resolved in the reference list of
`ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean`, which every file in this directory shares.
-/

-- All three are load-bearing, verified by removing them and rebuilding: the statements below carry
-- `[Fintype ι]` / `[DecidableEq F]` and section variables that their *proofs* do not use, which the
-- corresponding linters each report.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open Code

section LargeAlphabetBarrier

/-- The barrier's integer parameters, bundled with the three inequalities that make them fit: the
`ℓ + 1` agreement blocks fit inside the radius, a codeword avoiding the family's set still lies
within the radius, and a repeated codeword would have to beat the boosted radius. -/
structure AGLBarrierParameters (ℓ n radius boosted : ℕ) where
  aFamily : ℕ
  aUnion : ℕ
  dZero : ℕ
  dOne : ℕ
  W : ℕ
  center_block_bound : dZero + ℓ * dOne ≤ radius
  other_codeword_bound : n - dZero - dOne - aFamily ≤ radius
  repeated_codeword_contradiction : n - aUnion < boosted

/-- **Many large sets share a large `ℓ`-wise intersection.** Given `M ≥ ⌈4ℓ²/p⌉` subsets of the
coordinates each of size `> p·n`, some `ℓ` of them meet in at least `⌈(3p^ℓ/4)·n⌉` coordinates.
This is what lets a balanced centre be built from `ℓ` nearby codewords. -/
def AGLCommonDisagreementIntersection : Prop :=
  ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (p : ℝ), 0 < p → p < 1 →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (M : ℕ), Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) ≤ M →
      ∀ S : Fin M → Finset ι,
        (∀ j, Nat.floor (p * Fintype.card ι) < (S j).card) →
        ∃ J : Finset (Fin M), J.card = ℓ ∧
          Nat.ceil ((3 * p ^ ℓ / 4) * Fintype.card ι) ≤
            ({i : ι | ∀ j, j ∈ J → i ∈ S j} : Set ι).ncard

/-- A block structure on the coordinates: one `zero` block of size `dZero` and `ℓ` further pairwise
disjoint blocks of size `dOne`, all disjoint from `zero`. -/
structure AGLCoordinateBlocks (ι : Type) [DecidableEq ι]
    (ℓ dZero dOne : ℕ) where
  zero : Finset ι
  other : Fin ℓ → Finset ι
  card_zero : zero.card = dZero
  card_other : ∀ j, (other j).card = dOne
  zero_disjoint : ∀ j, Disjoint zero (other j)
  other_disjoint : ∀ i j, i ≠ j → Disjoint (other i) (other j)

/-- Such blocks exist whenever the coordinates can hold them, `dZero + ℓ · dOne ≤ n`. -/
def AGLCoordinateBlocksExistence : Prop :=
  ∀ (ℓ dZero dOne : ℕ),
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι],
      dZero + ℓ * dOne ≤ Fintype.card ι →
      ∃ _blocks : AGLCoordinateBlocks ι ℓ dZero dOne, True

/-- The coordinates a block structure uses number exactly `dZero + ℓ · dOne`. -/
def AGLCoordinateBlocksUsedCard : Prop :=
  ∀ (ℓ dZero dOne : ℕ),
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (blocks : AGLCoordinateBlocks ι ℓ dZero dOne),
      let used := blocks.zero ∪ Finset.univ.biUnion blocks.other
      used.card = dZero + ℓ * dOne

/-- A set of size at least `k · t` contains `k` pairwise disjoint subsets of size `t`. -/
def AGLDisjointEqualBlocks : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (k t : ℕ), k * t ≤ S.card →
      ∃ blocks : Fin k → Finset ι,
        (∀ j, blocks j ⊆ S) ∧
        (∀ j, (blocks j).card = t) ∧
        ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j)

/-- **Small fibers force a large image.** If every fiber of `f` on `s` has fewer than `W` elements
and `W · ℓ ≤ |s|`, then `f` takes at least `ℓ` distinct values on `s`. -/
def AGLDistinctAlternativesOfBoundedFibers : Prop :=
  ∀ {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) (W ℓ : ℕ), 0 < W →
      W * ℓ ≤ s.card →
      (∀ y, (s.filter fun x => f x = y).card < W) →
      ℓ ≤ (s.image f).card

/-- Double counting `ℓ`-subsets of set-indices against coordinates:
`∑ᵢ C(incidence i, ℓ) = ∑_{|J| = ℓ} |{i : i ∈ S j for all j ∈ J}|`. -/
def AGLIncidenceDoubleCount : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (ℓ : ℕ) (S : κ → Finset ι),
    let incidence : ι → ℕ := fun i => (Finset.univ.filter fun j => i ∈ S j).card
    let common : Finset κ → Finset ι := fun J =>
      Finset.univ.filter fun i => ∀ j ∈ J, i ∈ S j
    ∑ i, Nat.choose (incidence i) ℓ =
      ∑ J ∈ Finset.univ.powersetCard ℓ, (common J).card

/-- From a bound on the *mean* incidence to a bound on its `ℓ`-th binomial moment:
`p·M·n ≤ ∑ᵢ aᵢ` implies `(3p^ℓ/4) · C(M, ℓ) · n ≤ ∑ᵢ C(aᵢ, ℓ)`, by convexity once `M ≥ ⌈4ℓ²/p⌉`. -/
def AGLIncidenceMomentLower : Prop :=
  ∀ (ℓ M n : ℕ) (p : ℝ), 2 ≤ ℓ → 0 < n → 0 < p → p < 1 →
    Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) ≤ M →
    ∀ a : Fin n → ℕ,
      p * M * n ≤ ∑ i, (a i : ℝ) →
      (3 * p ^ ℓ / 4) * Nat.choose M ℓ * n ≤
        ∑ i, (Nat.choose (a i) ℓ : ℝ)

/-- The numeric slack the moment bound needs: `(3p^ℓ/4) · M^ℓ ≤ (p·M − (ℓ−1))^ℓ` once
`M ≥ ⌈4ℓ²/p⌉`. -/
def AGLIncidencePowerGap : Prop :=
  ∀ (ℓ M : ℕ) (p : ℝ), 2 ≤ ℓ → 0 < p →
    Nat.ceil (4 * (ℓ : ℝ) ^ 2 / p) ≤ M →
    (3 * p ^ ℓ / 4) * (M : ℝ) ^ ℓ ≤
      (p * M - (ℓ - 1)) ^ ℓ

/-- Counting incidences two ways: `∑ᵢ #{j : i ∈ S j} = ∑_j |S j|`. -/
def AGLIncidenceSumDoubleCount : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S : κ → Finset ι),
    ∑ i, (Finset.univ.filter fun j => i ∈ S j).card =
      ∑ j, (S j).card

/-- A **large-union family**: a finite family of coordinate sets, all of size `aFamily`, such that
*any* `W` of them already cover at least `aUnion` coordinates. The barrier uses one to force a
codeword that avoids a family member to be far from the centre. -/
structure AGLLargeUnionFamily (ι : Type) [DecidableEq ι]
    (W aFamily aUnion : ℕ) where
  sets : Finset (Finset ι)
  card_each : ∀ A ∈ sets, A.card = aFamily
  large_union : ∀ T : Finset (Finset ι), T ⊆ sets → T.card = W →
    aUnion ≤ (T.biUnion id).card

/-- Large-union families exist at densities `0 < α < β < 1`, with exponentially many sets:
`2^(γ·m)` of them for some `γ > 0` and all large `m`. -/
def AGLLargeUnionExistence : Prop :=
  ∀ (α β : ℝ), 0 < α → α < β → β < 1 →
    ∃ W : ℕ, 0 < W ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ m₀ : ℕ,
      ∀ m : ℕ, m₀ ≤ m →
        ∃ family : AGLLargeUnionFamily (Fin m) W
          (Nat.floor (α * m)) (Nat.ceil (β * m)),
          (2 : ℝ) ^ (γ * m) ≤ family.sets.card

/-- A large-union family can be reparametrised to nearby sizes `a₁ ≥ a₀`, `b₁ ≤ b₀`, at the cost
of a factor `W` in the number of sets. -/
def AGLLargeUnionFamilyResize : Prop :=
  ∀ (W a₀ b₀ a₁ b₁ : ℕ), 0 < W → a₀ ≤ a₁ → a₁ < b₀ → b₁ ≤ b₀ →
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι], a₁ ≤ Fintype.card ι →
      ∀ source : AGLLargeUnionFamily ι W a₀ b₀,
        ∃ target : AGLLargeUnionFamily ι W a₁ b₁,
          source.sets.card ≤ W * target.sets.card

/-- A large-union family on `Fin m` transports to one on the *unused* coordinates of a block
structure, keeping its size and staying disjoint from every block. -/
def AGLLargeUnionFamilyTransport : Prop :=
  ∀ (ℓ dZero dOne W aFamily aUnion : ℕ),
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (blocks : AGLCoordinateBlocks ι ℓ dZero dOne),
      let used := blocks.zero ∪ Finset.univ.biUnion blocks.other
      ∀ (m : ℕ), m = Fintype.card ι - used.card →
        ∀ source : AGLLargeUnionFamily (Fin m) W aFamily aUnion,
          ∃ target : AGLLargeUnionFamily ι W aFamily aUnion,
            target.sets.card = source.sets.card ∧
            ∀ S ∈ target.sets, Disjoint S blocks.zero ∧
              ∀ j, Disjoint S (blocks.other j)

/-- The barrier's parameters after rounding to integers: radius, boosted radius, block sizes, the
used and unused coordinate counts, and the family's set and union sizes. -/
structure AGLRoundedBarrierData where
  radius : ℕ
  boosted : ℕ
  dZero : ℕ
  dOne : ℕ
  used : ℕ
  unused : ℕ
  aFamily : ℕ
  aUnion : ℕ

/-- `D` is `d`-**separated**: distinct elements are at Hamming distance at least `d`. -/
def AGLSeparated {ι F : Type} [Fintype ι] [DecidableEq F]
    (D : Set (ι → F)) (d : ℕ) : Prop :=
  ∀ ⦃u : ι → F⦄, u ∈ D → ∀ ⦃v : ι → F⦄, v ∈ D → u ≠ v → d ≤ hammingDist u v

/-- **The pigeonhole bound**, by counting rather than by a probabilistic argument. Given a separated
code whose list size at the radius is at most `ℓ`, plus a block structure and a large-union family
disjoint from it, a code with `2 · |A|^aFamily ≤ |C|` cannot exist: some alternative on the family's
sets must repeat, and a repeat contradicts separation. -/
def AGLDeterministicPigeonholeBound : Prop :=
  ∀ (ℓ n radius boosted : ℕ), 2 ≤ ℓ → 0 < n →
    ∀ {ι A : Type} [Fintype ι] [DecidableEq ι]
      [Fintype A] [DecidableEq A]
      (C : Set (ι → A)), 2 ≤ Fintype.card A →
      Fintype.card ι = n → C.Finite →
      ∀ (params : AGLBarrierParameters ℓ n radius boosted), 0 < params.W →
      ∀ (blocks : AGLCoordinateBlocks ι ℓ params.dZero params.dOne)
        (family : AGLLargeUnionFamily ι params.W params.aFamily params.aUnion),
        (∀ S ∈ family.sets, Disjoint S blocks.zero ∧
          ∀ j, Disjoint S (blocks.other j)) →
        AGLSeparated C boosted →
        2 * Fintype.card A ^ params.aFamily ≤ C.ncard →
        Lambda C ((radius : ℝ) / n) ≤ (ℓ : ℕ∞) →
        family.sets.card ≤
          2 * params.W * ℓ * Fintype.card A ^ params.dZero

/-- **Greedy extraction of a separated subcode.** If every ball of radius `d` around a codeword
holds at most `B` codewords, then `C` has a `(d+1)`-separated subset `D` with `|C| ≤ B · |D|`. -/
def AGLGreedySeparatedExtraction : Prop :=
  ∀ {ι A : Type} [Fintype ι] [DecidableEq A]
    (C : Set (ι → A)) (d B : ℕ), C.Finite →
    (∀ c ∈ C,
      ({x : ι → A | x ∈ C ∧ hammingDist c x ≤ d} : Set (ι → A)).ncard ≤ B) →
    ∃ D : Set (ι → A), D ⊆ C ∧ D.Finite ∧ AGLSeparated D (d + 1) ∧
      C.ncard ≤ B * D.ncard

/-- The mean of the shifted incidences `aᵢ + 1 − ℓ` is at least `p·M − (ℓ−1)`. -/
def AGLShiftedIncidenceMeanLower : Prop :=
  ∀ (ℓ M n : ℕ) (p : ℝ), 2 ≤ ℓ → 0 < n →
    ∀ a : Fin n → ℕ,
      p * M * n ≤ ∑ i, (a i : ℝ) →
      p * M - (ℓ - 1) ≤
        (∑ i, ((a i + 1 - ℓ : ℕ) : ℝ)) / n

/-- The binomial ratio estimate behind the sparse count:
`C(b−1, a) / C(m, a) ≤ ((b−1)/(m+1−a))^a`. -/
def AGLSparseChooseRatioBound : Prop :=
  ∀ (m a b : ℕ), a ≤ b - 1 → b - 1 ≤ m →
    ((Nat.choose (b - 1) a : ℝ) / Nat.choose m a) ≤
      ((((b - 1 : ℕ) : ℝ) / ((m + 1 - a : ℕ) : ℝ)) ^ a)

/-- The *sparse* large-union existence statement, at `α + β < 1` rather than `β < 1`. This is the
regime the barrier needs, and it is what the numerics below deliver. -/
def AGLSparseLargeUnionExistence : Prop :=
  ∀ (α β : ℝ), 0 < α → α < β → α + β < 1 →
    ∃ W : ℕ, 0 < W ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ m₀ : ℕ,
      ∀ m : ℕ, m₀ ≤ m →
        ∃ family : AGLLargeUnionFamily (Fin m) W
          (Nat.floor (α * m)) (Nat.ceil (β * m)),
          (2 : ℝ) ^ (γ * m) ≤ family.sets.card

/-- The purely numeric inequalities behind sparse existence: with `T = 2^(m/W)` candidate families,
the count of *bad* families is smaller than the total, so a good one exists. -/
def AGLSparseLargeUnionNumerics : Prop :=
  ∀ (α β : ℝ), 0 < α → α < β → α + β < 1 →
    ∃ W : ℕ, 0 < W ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ m₀ : ℕ,
      ∀ m : ℕ, m₀ ≤ m →
        let a := Nat.floor (α * m)
        let b := Nat.ceil (β * m)
        let T := 2 ^ (m / W)
        a < b ∧ b ≤ m ∧ W ≤ T ∧
          Nat.choose T W * Nat.choose m (b - 1) *
              Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W) <
            Nat.choose m a ^ T ∧
          W * Nat.ceil ((2 : ℝ) ^ (γ * m)) ≤ T

/-- The numerics imply sparse existence — the probabilistic-method step, done by counting. -/
def AGLSparseLargeUnionExistenceOfNumerics : Prop :=
  AGLSparseLargeUnionNumerics → AGLSparseLargeUnionExistence

/-- The unused coordinates of a block structure are in bijection with `Fin` of their number, which
is how a family built on `Fin m` is transported onto them. -/
def AGLUnusedCoordinatesEquivFin : Prop :=
  ∀ (ℓ dZero dOne : ℕ),
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (blocks : AGLCoordinateBlocks ι ℓ dZero dOne),
      let used := blocks.zero ∪ Finset.univ.biUnion blocks.other
      Nonempty (Fin (Fintype.card ι - used.card) ≃ {i : ι // i ∉ used})

theorem aglAlphabetCardGeRpowOfAlphaLeEta
    (α η : ℝ) (hη_pos : 0 < η) (hαη : α ≤ η)
    {A : Type} [Fintype A] (hcard : 2 ≤ Fintype.card A) :
    (Fintype.card A : ℝ) ≥ (2 : ℝ) ^ (α / η) := by
  have hexp : α / η ≤ 1 := (div_le_one hη_pos).2 hαη
  have hpow : (2 : ℝ) ^ (α / η) ≤ 2 := by
    calc
      (2 : ℝ) ^ (α / η) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = 2 := by norm_num
  have hcardR : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hcard
  exact hpow.trans hcardR

/-- The **bad** `T`-indexed families of `a`-subsets of `Fin m`: those for which some `W` of the sets
have union smaller than `b`. Their complement gives a large-union family. -/
noncomputable def aglBadIndexedFamilies
    (m a T W b : ℕ) :
    Finset (Fin T → {S : Finset (Fin m) // S.card = a}) := by
  classical
  exact Finset.univ.filter fun A =>
    ∃ J : Finset (Fin T), J.card = W ∧
      (J.biUnion fun j => (A j).1).card < b

/-- Counting the bad families: at most `C(T,W) · C(m,b−1) · C(b−1,a)^W · C(m,a)^(T−W)`, obtained by
choosing the witnessing `W` indices and the `(b−1)`-set covering them. -/
def AGLBadIndexedFamiliesCardBound : Prop :=
  ∀ (m a T W b : ℕ), 0 < W → W ≤ T → 0 < b → b ≤ m → a < b →
    (aglBadIndexedFamilies m a T W b).card ≤
      Nat.choose T W * Nat.choose m (b - 1) *
        Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W)

/-- Every bad family admits a witness: `W` indices and a set of size `b−1` containing all of their
sets. -/
def AGLBadIndexedFamiliesWitnessCover : Prop :=
  ∀ (m a T W b : ℕ), 0 < b → b ≤ m →
    ∀ A ∈ aglBadIndexedFamilies m a T W b,
      ∃ J : Finset (Fin T), ∃ U : Finset (Fin m),
        J.card = W ∧ U.card = b - 1 ∧
          ∀ j ∈ J, (A j).val ⊆ U

/-- A family that is *not* bad yields a large-union family, with `T ≤ W · |family.sets|`. -/
def AGLGoodIndexedFamilyToLargeUnionFamily : Prop :=
  ∀ (m a T W b : ℕ), 0 < W → a < b →
    ∀ A : Fin T → {S : Finset (Fin m) // S.card = a},
      A ∉ aglBadIndexedFamilies m a T W b →
      ∃ family : AGLLargeUnionFamily (Fin m) W a b,
        T ≤ W * family.sets.card

theorem aglBadIndexedFamiliesWitnessCover :
    AGLBadIndexedFamiliesWitnessCover := by
  classical
  intro m a T W b hb hbm A hA
  have hbad := (Finset.mem_filter.mp hA).2
  obtain ⟨J, hJcard, hUnion⟩ := hbad
  have hUnionCard :
      (J.biUnion fun j => (A j).val).card ≤ b - 1 := by
    omega
  have hbCard : b - 1 ≤ Fintype.card (Fin m) := by
    simpa only [Fintype.card_fin] using (Nat.sub_le b 1).trans hbm
  obtain ⟨U, hUnionSub, hUcard⟩ :=
    Finset.exists_superset_card_eq hUnionCard hbCard
  refine ⟨J, U, hJcard, hUcard, ?_⟩
  intro j hj x hx
  apply hUnionSub
  exact Finset.mem_biUnion.mpr ⟨j, hj, hx⟩

/-- The density at which the large-union family's sets are drawn: half the rate. -/
noncomputable def aglBarrierAlphaDensity (R : ℝ) : ℝ := R / 2

theorem aglBarrierExponentContradiction
    (K M n : ℕ) (γ : ℝ) (hγ : 0 < γ) (hn : 0 < n)
    (hlower : (2 : ℝ) ^ (γ * n) ≤ M)
    (hupper : (M : ℝ) ≤ (K : ℝ) * (2 : ℝ) ^ ((γ / 4) * n))
    (habsorb : (K : ℝ) * (2 : ℝ) ^ ((γ / 4) * n) ≤
      (2 : ℝ) ^ ((γ / 2) * n)) : False := by
  have hchain : (2 : ℝ) ^ (γ * n) ≤
      (2 : ℝ) ^ ((γ / 2) * n) := hlower.trans (hupper.trans habsorb)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hexp : (γ / 2) * (n : ℝ) < γ * n := by nlinarith
  have hstrict : (2 : ℝ) ^ ((γ / 2) * n) <
      (2 : ℝ) ^ (γ * n) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexp
  exact (not_lt_of_ge hchain) hstrict

/-- The barrier's length constant, `8·(B + ℓ + 10)`. -/
noncomputable def aglBarrierK (ℓ B : ℕ) : ℝ :=
  ((8 * (B + ℓ + 10) : ℕ) : ℝ)

theorem aglBarrierKSlack
    (ℓ B : ℕ) (hℓ : 2 ≤ ℓ) :
    (B : ℝ) + 4 + 1 / (ℓ : ℝ) ≤
      aglBarrierK ℓ B * (1 - 1 / (ℓ : ℝ)) - 1 := by
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓpos : (0 : ℝ) < ℓ := by linarith
  have hB : (0 : ℝ) ≤ B := by positivity
  unfold aglBarrierK
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  field_simp [ne_of_gt hℓpos]
  nlinarith

/-- The **boosted radius** `p + p^ℓ/(2ℓ)`: slightly beyond `p`, which is the room the
balanced-centre construction needs. -/
noncomputable def aglBoostedRadius (ℓ : ℕ) (p : ℝ) : ℝ :=
  p + p ^ ℓ / (2 * ℓ)

/-- **Balanced centre from `ℓ` nearby codewords.** If `c` and `v 1, …, v ℓ` are pairwise within the
boosted radius and they disagree with `c` on a large common set, then some single word `y` is within
radius `p` of all of them — so the point list at `y` has `ℓ + 1` members. -/
def AGLBalancedCenterConstruction : Prop :=
  ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (p : ℝ), 0 < p → p < 1 →
    ∀ {ι A : Type} [Fintype ι] [DecidableEq ι] [DecidableEq A]
      (c : ι → A) (v : Fin ℓ → ι → A),
      (∀ j, hammingDist c (v j) ≤
        Nat.floor (aglBoostedRadius ℓ p * Fintype.card ι)) →
      8 * (ℓ : ℝ) ≤ p ^ ℓ * Fintype.card ι →
      Nat.ceil ((3 * p ^ ℓ / 4) * Fintype.card ι) ≤
        ({i : ι | ∀ j, c i ≠ v j i} : Set ι).ncard →
      ∃ y : ι → A,
        hammingDist c y ≤ Nat.floor (p * Fintype.card ι) ∧
        ∀ j, hammingDist (v j) y ≤ Nat.floor (p * Fintype.card ι)

/-- **The local neighbourhood bound.** A list size of at most `ℓ` at radius `p` caps how many
codewords sit within the *boosted* radius of any one codeword, at `ℓ + ⌈4ℓ²/p⌉`. Proved by feeding
the balanced-centre construction a hypothetical excess. -/
def AGLLocalNeighborhoodBound : Prop :=
  ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (p : ℝ), 0 < p → p < 1 →
    ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
      {A : Type} [Fintype A] [DecidableEq A]
      (C : Set (ι → A)), Lambda C p ≤ (ℓ : ℕ∞) →
      8 * (ℓ : ℝ) ≤ p ^ ℓ * Fintype.card ι →
      ∀ c ∈ C,
        ({x : ι → A | x ∈ C ∧
          hammingDist c x ≤
            Nat.floor (aglBoostedRadius ℓ p * Fintype.card ι)} : Set (ι → A)).ncard
          ≤ ℓ + Nat.ceil (4 * ((ℓ : ℝ) ^ 2) / p)

theorem aglBalancedCenterArithmetic
    (ℓ : ℕ) (p : ℝ) (n : ℕ) (hℓ : 2 ≤ ℓ) (hp : 0 < p) (hp_lt : p < 1)
    (hsize : 8 * (ℓ : ℝ) ≤ p ^ ℓ * n) :
    Nat.floor (p * n) ≤ Nat.floor (aglBoostedRadius ℓ p * n) ∧
      Nat.floor (aglBoostedRadius ℓ p * n) -
          (Nat.floor (aglBoostedRadius ℓ p * n) - Nat.floor (p * n)) =
        Nat.floor (p * n) ∧
      ℓ * (Nat.floor (aglBoostedRadius ℓ p * n) - Nat.floor (p * n)) ≤
        Nat.floor (p * n) ∧
      ℓ * (Nat.floor (aglBoostedRadius ℓ p * n) - Nat.floor (p * n)) ≤
        Nat.ceil ((3 * p ^ ℓ / 4) * n) := by
  have hℓpos : 0 < ℓ := by omega
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hnR : (0 : ℝ) < n := by
    by_contra hn
    have hnle : (n : ℝ) ≤ 0 := le_of_not_gt hn
    have hprod : p ^ ℓ * (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hp.le ℓ) hnle
    have hleft : (0 : ℝ) < 8 * ℓ := by positivity
    nlinarith
  have hboost : p ≤ aglBoostedRadius ℓ p := by
    unfold aglBoostedRadius
    have hpow : 0 ≤ p ^ ℓ := by positivity
    have hden : (0 : ℝ) < 2 * ℓ := by positivity
    exact le_add_of_nonneg_right (div_nonneg hpow hden.le)
  have hboostPos : 0 < aglBoostedRadius ℓ p := hp.trans_le hboost
  have hmul : p * n ≤ aglBoostedRadius ℓ p * n :=
    mul_le_mul_of_nonneg_right hboost hnR.le
  have hrle : Nat.floor (p * n) ≤
      Nat.floor (aglBoostedRadius ℓ p * n) := Nat.floor_mono hmul
  refine ⟨hrle, ?_, ?_, ?_⟩
  · omega
  · let r := Nat.floor (p * n)
    let r' := Nat.floor (aglBoostedRadius ℓ p * n)
    let t := r' - r
    have htcast : (t : ℝ) = (r' : ℝ) - r := Nat.cast_sub hrle
    have hr'le : (r' : ℝ) ≤ aglBoostedRadius ℓ p * n :=
      Nat.floor_le (mul_nonneg hboostPos.le hnR.le)
    have hr'le' : (r' : ℝ) ≤ p * n + p ^ ℓ * n / (2 * ℓ) := by
      calc
        (r' : ℝ) ≤ aglBoostedRadius ℓ p * n := hr'le
        _ = p * n + p ^ ℓ * n / (2 * ℓ) := by
          unfold aglBoostedRadius
          ring
    have hrlt : p * n < (r : ℝ) + 1 := Nat.lt_floor_add_one _
    have ht : (t : ℝ) ≤ p ^ ℓ * n / (2 * ℓ) + 1 := by
      rw [htcast]
      linarith
    have hmul_t : (ℓ : ℝ) * t ≤ p ^ ℓ * n / 2 + ℓ := by
      have h := mul_le_mul_of_nonneg_left ht hℓR.le
      calc
        (ℓ : ℝ) * t ≤ (ℓ : ℝ) * (p ^ ℓ * n / (2 * ℓ) + 1) := h
        _ = p ^ ℓ * n / 2 + ℓ := by
          field_simp [ne_of_gt hℓR]
    have hfive : (ℓ : ℝ) * t ≤ 5 * (p ^ ℓ * n) / 8 := by
      nlinarith
    have hpPowLt : p ^ ℓ < p :=
      pow_lt_self_of_lt_one₀ hp hp_lt (by omega)
    have hP_lt : p ^ ℓ * n < p * n :=
      mul_lt_mul_of_pos_right hpPowLt hnR
    have hlt : (ℓ : ℝ) * t < (r : ℝ) + 1 := by
      have hfive_lt : 5 * (p ^ ℓ * n) / 8 < p * n := by
        have hPnonneg : 0 ≤ p ^ ℓ * n := by positivity
        nlinarith
      nlinarith
    have hnat : ℓ * t < r + 1 := by exact_mod_cast hlt
    simpa only [r, r', t] using (Nat.lt_succ_iff.mp hnat)
  · let r := Nat.floor (p * n)
    let r' := Nat.floor (aglBoostedRadius ℓ p * n)
    let t := r' - r
    have htcast : (t : ℝ) = (r' : ℝ) - r := Nat.cast_sub hrle
    have hr'le : (r' : ℝ) ≤ aglBoostedRadius ℓ p * n :=
      Nat.floor_le (mul_nonneg hboostPos.le hnR.le)
    have hr'le' : (r' : ℝ) ≤ p * n + p ^ ℓ * n / (2 * ℓ) := by
      calc
        (r' : ℝ) ≤ aglBoostedRadius ℓ p * n := hr'le
        _ = p * n + p ^ ℓ * n / (2 * ℓ) := by
          unfold aglBoostedRadius
          ring
    have hrlt : p * n < (r : ℝ) + 1 := Nat.lt_floor_add_one _
    have ht : (t : ℝ) ≤ p ^ ℓ * n / (2 * ℓ) + 1 := by
      rw [htcast]
      linarith
    have hmul_t : (ℓ : ℝ) * t ≤ p ^ ℓ * n / 2 + ℓ := by
      have h := mul_le_mul_of_nonneg_left ht hℓR.le
      calc
        (ℓ : ℝ) * t ≤ (ℓ : ℝ) * (p ^ ℓ * n / (2 * ℓ) + 1) := h
        _ = p ^ ℓ * n / 2 + ℓ := by
          field_simp [ne_of_gt hℓR]
    have hthree : (ℓ : ℝ) * t ≤ 3 * (p ^ ℓ * n) / 4 := by
      nlinarith
    have hceil : 3 * (p ^ ℓ * n) / 4 ≤
        (Nat.ceil ((3 * p ^ ℓ / 4) * n) : ℝ) := by
      calc
        3 * (p ^ ℓ * n) / 4 = (3 * p ^ ℓ / 4) * n := by ring
        _ ≤ (Nat.ceil ((3 * p ^ ℓ / 4) * n) : ℝ) :=
          Nat.le_ceil ((3 * p ^ ℓ / 4) * n)
    have hcast : ((ℓ * t : ℕ) : ℝ) ≤
        (Nat.ceil ((3 * p ^ ℓ / 4) * n) : ℝ) := by
      norm_num only [Nat.cast_mul]
      exact hthree.trans hceil
    exact_mod_cast hcast

theorem aglBoostedRadius_gt (ℓ : ℕ) (hℓ_pos : 0 < ℓ)
    (p : ℝ) (hp_pos : 0 < p) : p < aglBoostedRadius ℓ p := by
  unfold aglBoostedRadius
  have hpow : 0 < p ^ ℓ := pow_pos hp_pos ℓ
  have hden : (0 : ℝ) < 2 * ℓ := by positivity
  have hquot : 0 < p ^ ℓ / (2 * ℓ) := div_pos hpow hden
  linarith

theorem aglCeilLinearBound
    (K η : ℝ) (n : ℕ) (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hone : 1 ≤ η * n) :
    (Nat.ceil (K * η * n) : ℝ) < (K + 1) * η * n := by
  have hnonneg : 0 ≤ K * η * (n : ℝ) := by positivity
  have hceil := Nat.ceil_lt_add_one hnonneg
  have hunit : K * η * (n : ℝ) + 1 ≤ (K + 1) * η * n := by
    nlinarith
  exact hceil.trans_le hunit

theorem aglChooseDistinctImages
    {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (s : Finset X) (f : X → Y) (k : ℕ)
    (hcard : k ≤ (s.image f).card) :
    ∃ sel : Fin k → X, (∀ j, sel j ∈ s) ∧
      Function.Injective (fun j => f (sel j)) := by
  classical
  obtain ⟨t, htsub, htcard⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin k ≃ t := (Finset.equivFinOfCardEq htcard).symm
  have hpre : ∀ y : t, ∃ x ∈ s, f x = y.1 := by
    intro y
    exact Finset.mem_image.mp (htsub y.2)
  let pre : t → X := fun y => Classical.choose (hpre y)
  have hpre_mem : ∀ y : t, pre y ∈ s := by
    intro y
    exact (Classical.choose_spec (hpre y)).1
  have hpre_eq : ∀ y : t, f (pre y) = y.1 := by
    intro y
    exact (Classical.choose_spec (hpre y)).2
  let sel : Fin k → X := fun j => pre (e j)
  refine ⟨sel, ?_, ?_⟩
  · intro j
    exact hpre_mem (e j)
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    have hi := hpre_eq (e i)
    have hj := hpre_eq (e j)
    dsimp only [sel] at hij
    exact hi.symm.trans (hij.trans hj)

/-- The families whose sets at the indices in `J` all sit inside `U` — the shape a bad family's
witness puts it into. -/
noncomputable def aglConstrainedIndexedFamilies
    (m a T : ℕ) (J : Finset (Fin T)) (U : Finset (Fin m)) :
    Finset (Fin T → {S : Finset (Fin m) // S.card = a}) := by
  classical
  exact Finset.univ.filter fun A => ∀ j ∈ J, (A j).1 ⊆ U

/-- Every bad family lies in one of the constrained classes, indexed by its witness `(J, U)`. -/
def AGLBadIndexedFamiliesSubsetCover : Prop :=
  ∀ (m a T W b : ℕ), 0 < b → b ≤ m →
    aglBadIndexedFamilies m a T W b ⊆
      (Finset.univ.powersetCard W).biUnion fun J =>
        (Finset.univ.powersetCard (b - 1)).biUnion fun U =>
          aglConstrainedIndexedFamilies m a T J U

/-- The exact size of a constrained class: `C(b−1, a)^W · C(m, a)^(T−W)`. -/
def AGLConstrainedIndexedFamiliesCard : Prop :=
  ∀ (m a T W b : ℕ) (J : Finset (Fin T)) (U : Finset (Fin m)),
    J.card = W → U.card = b - 1 →
    (aglConstrainedIndexedFamilies m a T J U).card =
      Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W)

theorem aglBadIndexedFamiliesSubsetCover :
    AGLBadIndexedFamiliesSubsetCover := by
  classical
  intro m a T W b hb hbm A hA
  obtain ⟨J, U, hJcard, hUcard, hconstrained⟩ :=
    aglBadIndexedFamiliesWitnessCover m a T W b hb hbm A hA
  apply Finset.mem_biUnion.mpr
  refine ⟨J, ?_, ?_⟩
  · exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ J, hJcard⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨U, ?_, ?_⟩
    · exact Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ U, hUcard⟩
    · simp only [aglConstrainedIndexedFamilies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hconstrained

theorem aglCoordinateBlocksExists : AGLCoordinateBlocksExistence := by
  classical
  intro ℓ dZero dOne ι _ _ htotal
  let total := dZero + ℓ * dOne
  let e : Fin total ↪ ι := Classical.choice
    (Function.Embedding.nonempty_of_card_le (α := Fin total) (β := ι) (by
      simpa only [Fintype.card_fin] using htotal))
  let z : Fin dZero ↪ Fin total :=
    ⟨fun k => ⟨k, by dsimp only [total]; omega⟩,
      fun a b hab => Fin.ext (congrArg (fun x : Fin total => x.val) hab)⟩
  let o : Fin ℓ → Fin dOne ↪ Fin total := fun j =>
    ⟨fun k => ⟨dZero + j * dOne + k, by
        have hj := j.isLt
        have hk := k.isLt
        dsimp only [total]
        have hmul : (j.val + 1) * dOne ≤ ℓ * dOne :=
          Nat.mul_le_mul_right dOne (Nat.succ_le_iff.mpr hj)
        rw [Nat.add_mul] at hmul
        omega⟩,
      fun a b hab => Fin.ext (by
        have hv := congrArg (fun x : Fin total => x.val) hab
        simpa using hv)⟩
  let zero : Finset ι := Finset.univ.map (z.trans e)
  let other : Fin ℓ → Finset ι := fun j => Finset.univ.map ((o j).trans e)
  refine ⟨{
    zero := zero
    other := other
    card_zero := ?_
    card_other := ?_
    zero_disjoint := ?_
    other_disjoint := ?_ }, trivial⟩
  · simp only [zero, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · intro j
    simp only [other, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · intro j
    rw [Finset.disjoint_left]
    intro x hxz hxo
    rcases Finset.mem_map.mp hxz with ⟨a, ha, hax⟩
    rcases Finset.mem_map.mp hxo with ⟨b, hb, hbx⟩
    have heq : z a = o j b := e.injective (hax.trans hbx.symm)
    have hv := congrArg Fin.val heq
    change a.val = dZero + j.val * dOne + b.val at hv
    have ha_lt := a.isLt
    omega
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rcases Finset.mem_map.mp hxi with ⟨a, ha, hax⟩
    rcases Finset.mem_map.mp hxj with ⟨b, hb, hbx⟩
    have heq : o i a = o j b := e.injective (hax.trans hbx.symm)
    have hv := congrArg Fin.val heq
    change dZero + i.val * dOne + a.val = dZero + j.val * dOne + b.val at hv
    have hvne : i.val ≠ j.val := by
      intro h
      apply hij
      exact Fin.ext h
    rcases lt_or_gt_of_ne hvne with hijlt | hjilt
    · have hmul : (i.val + 1) * dOne ≤ j.val * dOne :=
        Nat.mul_le_mul_right dOne (Nat.succ_le_iff.mpr hijlt)
      have hia : i.val * dOne + a.val < (i.val + 1) * dOne := by
        calc
          i.val * dOne + a.val < i.val * dOne + dOne :=
            Nat.add_lt_add_left a.isLt _
          _ = (i.val + 1) * dOne := by rw [Nat.add_mul, one_mul]
      have hcore : i.val * dOne + a.val < j.val * dOne + b.val :=
        hia.trans_le (hmul.trans (Nat.le_add_right _ _))
      have hlt := Nat.add_lt_add_left hcore dZero
      have hv' : dZero + (i.val * dOne + a.val) =
          dZero + (j.val * dOne + b.val) := by
        simpa only [Nat.add_assoc] using hv
      exact (Nat.ne_of_lt hlt) hv'
    · have hmul : (j.val + 1) * dOne ≤ i.val * dOne :=
        Nat.mul_le_mul_right dOne (Nat.succ_le_iff.mpr hjilt)
      have hjb : j.val * dOne + b.val < (j.val + 1) * dOne := by
        calc
          j.val * dOne + b.val < j.val * dOne + dOne :=
            Nat.add_lt_add_left b.isLt _
          _ = (j.val + 1) * dOne := by rw [Nat.add_mul, one_mul]
      have hcore : j.val * dOne + b.val < i.val * dOne + a.val :=
        hjb.trans_le (hmul.trans (Nat.le_add_right _ _))
      have hlt := Nat.add_lt_add_left hcore dZero
      have hv' : dZero + (j.val * dOne + b.val) =
          dZero + (i.val * dOne + a.val) := by
        simpa only [Nat.add_assoc] using hv.symm
      exact (Nat.ne_of_lt hlt) hv'

theorem aglCoordinateBlocksUsedCard : AGLCoordinateBlocksUsedCard := by
  classical
  intro ℓ dZero dOne ι _ _ blocks
  dsimp
  have hpair :
      ((Finset.univ : Finset (Fin ℓ)) : Set (Fin ℓ)).PairwiseDisjoint blocks.other := by
    intro i hi j hj hij
    exact blocks.other_disjoint i j hij
  have hzero : Disjoint blocks.zero (Finset.univ.biUnion blocks.other) := by
    rw [Finset.disjoint_left]
    intro x hx hxu
    simp only [Finset.mem_biUnion] at hxu
    obtain ⟨j, hj, hxj⟩ := hxu
    exact (Finset.disjoint_left.mp (blocks.zero_disjoint j)) hx hxj
  rw [Finset.card_union_of_disjoint hzero, Finset.card_biUnion hpair]
  simp only [blocks.card_zero, blocks.card_other, Finset.sum_const_nat,
    Finset.card_univ, Fintype.card_fin]

theorem aglDisjointEqualBlocks : AGLDisjointEqualBlocks := by
  classical
  intro ι _ _ S k t hcard
  have htotal : 0 + k * t ≤ Fintype.card S := by
    simpa only [zero_add, Fintype.card_coe] using hcard
  obtain ⟨base, hbase⟩ :=
    aglCoordinateBlocksExists k 0 t (ι := S) htotal
  let incl : S ↪ ι := Function.Embedding.subtype (fun x => x ∈ S)
  let blocks : Fin k → Finset ι := fun j => (base.other j).map incl
  refine ⟨blocks, ?_, ?_, ?_⟩
  · intro j x hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.property
  · intro j
    simp only [blocks, Finset.card_map, base.card_other]
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rcases Finset.mem_map.mp hxi with ⟨a, ha, hax⟩
    rcases Finset.mem_map.mp hxj with ⟨b, hb, hbx⟩
    have hab : a = b := incl.injective (hax.trans hbx.symm)
    subst b
    exact (Finset.disjoint_left.mp (base.other_disjoint i j hij)) ha hb

theorem aglDistinctAlternativesOfBoundedFibers :
    AGLDistinctAlternativesOfBoundedFibers := by
  intro α β _ _ s f W ℓ hW hcard hfiber
  have hsle : s.card ≤ W * (s.image f).card := by
    apply Finset.card_le_mul_card_image s W
    intro y hy
    exact (hfiber y).le
  have hmul : W * ℓ ≤ W * (s.image f).card := hcard.trans hsle
  exact le_of_mul_le_mul_left hmul hW

theorem aglEtaTimesLengthOne
    (η : ℝ) (n : ℕ) (hη : 0 < η) (hlen : 1 / η ≤ (n : ℝ)) :
    1 ≤ η * n := by
  have h := (div_le_iff₀ hη).mp hlen
  simpa only [one_mul, mul_comm] using h

theorem aglExactSubsetTypeCard (m a : ℕ) :
    Fintype.card {S : Finset (Fin m) // S.card = a} = Nat.choose m a := by
  simpa only [Fintype.card_fin] using
    (Fintype.card_finset_len (α := Fin m) a)

theorem aglFixedFactorRpowAbsorb
    (K : ℕ) (_hK : 0 < K) (γ : ℝ) (hγ : 0 < γ) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (K : ℝ) * (2 : ℝ) ^ ((γ / 2) * m) ≤
        (2 : ℝ) ^ (γ * m) := by
  obtain ⟨m₀, hm₀⟩ := exists_nat_gt (2 * (K : ℝ) / γ)
  refine ⟨m₀, ?_⟩
  intro m hm
  have hmReal : 2 * (K : ℝ) / γ < (m : ℝ) :=
    hm₀.trans_le (by exact_mod_cast hm)
  have hKm : (K : ℝ) ≤ (γ / 2) * m := by
    have hcross := (div_lt_iff₀ hγ).mp hmReal
    nlinarith
  have hKpowNat : K ≤ 2 ^ K := by
    calc
      K = Nat.choose K 1 := (Nat.choose_one_right K).symm
      _ ≤ 2 ^ K := Nat.choose_le_two_pow K 1
  have hKpow : (K : ℝ) ≤ (2 : ℝ) ^ (K : ℝ) := by
    calc
      (K : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast hKpowNat
      _ = (2 : ℝ) ^ (K : ℕ) := by norm_num
      _ = (2 : ℝ) ^ (K : ℝ) := (Real.rpow_natCast _ _).symm
  have hsum : (K : ℝ) + (γ / 2) * m ≤ γ * m := by
    nlinarith
  calc
    (K : ℝ) * (2 : ℝ) ^ ((γ / 2) * m) ≤
        (2 : ℝ) ^ (K : ℝ) * (2 : ℝ) ^ ((γ / 2) * m) :=
      mul_le_mul_of_nonneg_right hKpow (by positivity)
    _ = (2 : ℝ) ^ ((K : ℝ) + (γ / 2) * m) :=
      (Real.rpow_add (by norm_num) _ _).symm
    _ ≤ (2 : ℝ) ^ (γ * m) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hsum

theorem aglFixedSubsetInsideCard (m a : ℕ) (U : Finset (Fin m)) :
    Fintype.card {S : Finset (Fin m) // S.card = a ∧ S ⊆ U} =
      Nat.choose U.card a := by
  classical
  calc
    Fintype.card {S : Finset (Fin m) // S.card = a ∧ S ⊆ U} =
        (U.powersetCard a).card := by
      apply Fintype.card_of_subtype
      intro S
      simp only [Finset.mem_powersetCard]
      aesop
    _ = Nat.choose U.card a := Finset.card_powersetCard a U

theorem aglConstrainedIndexedFamiliesCard :
    AGLConstrainedIndexedFamiliesCard := by
  classical
  intro m a T W b J U hJ hU
  let inside : Finset {S : Finset (Fin m) // S.card = a} :=
    Finset.univ.filter fun S => S.val ⊆ U
  have hinside : inside.card = Nat.choose U.card a := by
    let e : inside ≃ {S : Finset (Fin m) // S.card = a ∧ S ⊆ U} :=
      { toFun := fun S =>
          ⟨((S.val : {S : Finset (Fin m) // S.card = a}).val),
            ⟨(S.val : {S : Finset (Fin m) // S.card = a}).property,
              (Finset.mem_filter.mp S.property).2⟩⟩
        invFun := fun S =>
          ⟨⟨S.val, S.property.1⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.property.2⟩⟩
        left_inv := by intro S; apply Subtype.ext; rfl
        right_inv := by intro S; apply Subtype.ext; rfl }
    calc
      inside.card = Fintype.card inside := (Fintype.card_coe inside).symm
      _ = Fintype.card {S : Finset (Fin m) // S.card = a ∧ S ⊆ U} :=
        Fintype.card_congr e
      _ = Nat.choose U.card a := aglFixedSubsetInsideCard m a U
  let allowed : Fin T → Finset {S : Finset (Fin m) // S.card = a} :=
    fun j => if j ∈ J then inside else Finset.univ
  have heq : aglConstrainedIndexedFamilies m a T J U =
      Fintype.piFinset allowed := by
    ext A
    simp only [aglConstrainedIndexedFamilies, Finset.mem_filter,
      Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases hj : j ∈ J
      · simpa only [allowed, hj, if_pos, inside, Finset.mem_filter,
          Finset.mem_univ, true_and] using h j hj
      · simp [allowed, hj]
    · intro h j hj
      have hjmem := h j
      simpa only [allowed, hj, if_pos, inside, Finset.mem_filter,
        Finset.mem_univ, true_and] using hjmem
  have hallowed : ∀ j, (allowed j).card =
      if j ∈ J then Nat.choose U.card a else Nat.choose m a := by
    intro j
    by_cases hj : j ∈ J
    · simp only [allowed, hj, if_pos, hinside]
    · simp only [allowed, hj]
      exact aglExactSubsetTypeCard m a
  rw [heq, Fintype.card_piFinset]
  calc
    (∏ j, (allowed j).card) =
        ∏ j, if j ∈ J then Nat.choose U.card a else Nat.choose m a := by
      apply Fintype.prod_congr
      intro j
      exact hallowed j
    _ = Nat.choose U.card a ^ J.card *
        Nat.choose m a ^ (T - J.card) := by
      rw [Finset.prod_ite]
      have hfilter : (Finset.univ.filter fun j : Fin T => j ∈ J) = J := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hfilterCompl :
          (Finset.univ.filter fun j : Fin T => ¬j ∈ J) = Jᶜ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_compl]
      rw [hfilter, hfilterCompl]
      simp only [Finset.prod_const, Finset.card_compl, Fintype.card_fin]
    _ = Nat.choose (b - 1) a ^ W *
        Nat.choose m a ^ (T - W) := by
      rw [hJ, hU]

theorem aglBadIndexedFamiliesCardBound :
    AGLBadIndexedFamiliesCardBound := by
  classical
  intro m a T W b hW hWT hb hbm hab
  let Js : Finset (Finset (Fin T)) := Finset.univ.powersetCard W
  let Us : Finset (Finset (Fin m)) := Finset.univ.powersetCard (b - 1)
  let cover : Finset (Fin T → {S : Finset (Fin m) // S.card = a}) :=
    Js.biUnion fun J =>
      Us.biUnion fun U => aglConstrainedIndexedFamilies m a T J U
  have hsub : aglBadIndexedFamilies m a T W b ⊆ cover := by
    simpa only [Js, Us, cover] using
      (aglBadIndexedFamiliesSubsetCover m a T W b hb hbm)
  let K : ℕ :=
    Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W)
  have hsum :
      (∑ J ∈ Js, ∑ U ∈ Us,
        (aglConstrainedIndexedFamilies m a T J U).card) =
        Js.card * (Us.card * K) := by
    calc
      (∑ J ∈ Js, ∑ U ∈ Us,
          (aglConstrainedIndexedFamilies m a T J U).card) =
          ∑ J ∈ Js, ∑ U ∈ Us, K := by
        apply Finset.sum_congr rfl
        intro J hJ
        have hJcard : J.card = W :=
          (Finset.mem_powersetCard.mp hJ).2
        apply Finset.sum_congr rfl
        intro U hU
        have hUcard : U.card = b - 1 :=
          (Finset.mem_powersetCard.mp hU).2
        simpa only [K] using
          aglConstrainedIndexedFamiliesCard
            m a T W b J U hJcard hUcard
      _ = ∑ J ∈ Js, Us.card * K := by
        apply Finset.sum_congr rfl
        intro J hJ
        exact Finset.sum_const_nat fun _ _ => rfl
      _ = Js.card * (Us.card * K) :=
        Finset.sum_const_nat fun _ _ => rfl
  calc
    (aglBadIndexedFamilies m a T W b).card ≤ cover.card :=
      Finset.card_le_card hsub
    _ ≤ ∑ J ∈ Js, (Us.biUnion fun U =>
        aglConstrainedIndexedFamilies m a T J U).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ J ∈ Js, ∑ U ∈ Us,
        (aglConstrainedIndexedFamilies m a T J U).card := by
      apply Finset.sum_le_sum
      intro J hJ
      exact Finset.card_biUnion_le
    _ = Js.card * (Us.card * K) := hsum
    _ = Nat.choose T W * Nat.choose m (b - 1) *
        Nat.choose (b - 1) a ^ W * Nat.choose m a ^ (T - W) := by
      have hJs : Js.card = Nat.choose T W := by
        simp only [Js, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin]
      have hUs : Us.card = Nat.choose m (b - 1) := by
        simp only [Us, Finset.card_powersetCard, Finset.card_univ,
          Fintype.card_fin]
      rw [hJs, hUs]
      dsimp only [K]
      ring

theorem aglFloorDivMulSelf (radius n : ℕ) (hn : 0 < n) :
    Nat.floor (((radius : ℝ) / n) * n) = radius := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  rw [div_mul_cancel₀ _ hn0, Nat.floor_natCast]

theorem aglFloorRadiusRatioLe
    (p : ℝ) (n : ℕ) (hp : 0 ≤ p) (hn : 0 < n) :
    (Nat.floor (p * n) : ℝ) / n ≤ p := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_iff₀ hnR]
  exact Nat.floor_le (mul_nonneg hp (Nat.cast_nonneg n))

theorem aglGoodBaseByDoubleCount
    {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (s : Finset X) (t : Finset Y) (P : X → Y → Prop) [DecidableRel P]
    (hs : s.Nonempty)
    (hcol : ∀ y ∈ t, s.card ≤
      2 * (s.filter fun x => P x y).card) :
    ∃ x ∈ s, t.card ≤ 2 * (t.filter fun y => P x y).card := by
  by_contra hno
  have hrow : ∀ x ∈ s,
      2 * (t.filter fun y => P x y).card < t.card := by
    intro x hx
    exact Nat.lt_of_not_ge fun hge => hno ⟨x, hx, hge⟩
  have hdouble :
      (∑ y ∈ t, (s.filter fun x => P x y).card) =
        ∑ x ∈ s, (t.filter fun y => P x y).card := by
    calc
      (∑ y ∈ t, (s.filter fun x => P x y).card) =
          ∑ y ∈ t, ∑ x ∈ s, if P x y then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.card_filter]
      _ = ∑ x ∈ s, ∑ y ∈ t, if P x y then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ x ∈ s, (t.filter fun y => P x y).card := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.card_filter]
  have hlower : t.card * s.card ≤
      2 * ∑ x ∈ s, (t.filter fun y => P x y).card := by
    calc
      t.card * s.card = ∑ y ∈ t, s.card := by
        exact (Finset.sum_const_nat fun _ _ => rfl).symm
      _ ≤ ∑ y ∈ t, 2 * (s.filter fun x => P x y).card :=
        Finset.sum_le_sum fun y hy => hcol y hy
      _ = 2 * ∑ y ∈ t, (s.filter fun x => P x y).card := by
        rw [Finset.mul_sum]
      _ = 2 * ∑ x ∈ s, (t.filter fun y => P x y).card := by
        rw [hdouble]
  have hupper :
      2 * ∑ x ∈ s, (t.filter fun y => P x y).card <
        s.card * t.card := by
    calc
      2 * ∑ x ∈ s, (t.filter fun y => P x y).card =
          ∑ x ∈ s, 2 * (t.filter fun y => P x y).card := by
        rw [Finset.mul_sum]
      _ < ∑ x ∈ s, t.card :=
        Finset.sum_lt_sum_of_nonempty hs hrow
      _ = s.card * t.card :=
        Finset.sum_const_nat fun _ _ => rfl
  have hcontra : t.card * s.card < t.card * s.card :=
    hlower.trans_lt (by simpa only [Nat.mul_comm] using hupper)
  exact (Nat.lt_irrefl _ hcontra)

theorem aglGoodIndexedFamilyToLargeUnionFamily :
    AGLGoodIndexedFamilyToLargeUnionFamily := by
  classical
  intro m a T W b hW hab A hgood
  let f : Fin T → Finset (Fin m) := fun j => (A j).1
  have hlarge : ∀ Q : Finset (Finset (Fin m)),
      Q ⊆ Finset.univ.image f → Q.card = W →
        b ≤ (Q.biUnion id).card := by
    intro Q hQsub hQcard
    have hsurj : Set.SurjOn f
        ((Finset.univ : Finset (Fin T)) : Set (Fin T))
        (Q : Set (Finset (Fin m))) := by
      intro S hSQ
      have hSimage := hQsub hSQ
      rcases Finset.mem_image.mp hSimage with ⟨j, hj, hjS⟩
      exact ⟨j, hj, hjS⟩
    obtain ⟨J, hJuniv, hJinj, hJimage⟩ :=
      Finset.exists_subset_injOn_image_eq_of_surjOn
        ((Finset.univ : Finset (Fin T)) : Set (Fin T)) Q hsurj
    have hJcard : J.card = W := by
      calc
        J.card = (J.image f).card :=
          (Finset.card_image_of_injOn hJinj).symm
        _ = Q.card := congrArg Finset.card hJimage
        _ = W := hQcard
    apply Nat.le_of_not_gt
    intro hsmall
    apply hgood
    simp only [aglBadIndexedFamilies, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨J, hJcard, ?_⟩
    have hunion : Q.biUnion id = J.biUnion f := by
      rw [← hJimage, Finset.image_biUnion]
      simp only [id_eq]
    rw [hunion] at hsmall
    exact hsmall
  have hfiber : ∀ S ∈ Finset.univ.image f,
      (Finset.univ.filter fun j => f j = S).card ≤ W := by
    intro S hS
    by_contra hnot
    have hWle : W ≤ (Finset.univ.filter fun j => f j = S).card := by
      exact (Nat.lt_of_not_ge hnot).le
    obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hWle
    apply hgood
    simp only [aglBadIndexedFamilies, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨J, hJcard, ?_⟩
    have hUnionSub : J.biUnion f ⊆ S := by
      intro x hx
      rcases Finset.mem_biUnion.mp hx with ⟨j, hjJ, hxj⟩
      have hj := Finset.mem_filter.mp (hJsub hjJ)
      rw [hj.2] at hxj
      exact hxj
    have hScard : S.card = a := by
      rcases Finset.mem_image.mp hS with ⟨j, hj, hjS⟩
      rw [← hjS]
      exact (A j).property
    calc
      (J.biUnion f).card ≤ S.card := Finset.card_le_card hUnionSub
      _ = a := hScard
      _ < b := hab
  let family : AGLLargeUnionFamily (Fin m) W a b :=
    { sets := Finset.univ.image f
      card_each := by
        intro S hS
        rcases Finset.mem_image.mp hS with ⟨j, hj, hjS⟩
        rw [← hjS]
        exact (A j).property
      large_union := hlarge }
  refine ⟨family, ?_⟩
  change T ≤ W * (Finset.univ.image f).card
  have hcard := Finset.card_le_mul_card_image
    (Finset.univ : Finset (Fin T)) W hfiber
  simpa only [Finset.card_univ, Fintype.card_fin] using hcard

end LargeAlphabetBarrier

end CodingTheory
