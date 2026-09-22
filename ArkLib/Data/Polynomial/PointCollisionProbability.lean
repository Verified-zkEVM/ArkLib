/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.PointCollision
public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Probability that sampled points fail to separate polynomial tuples

The counting bound `Polynomial.card_le_of_not_injOn_evalTuple` divided by the size of a uniform
sample space. The counting lemmas live in `ArkLib.Data.Polynomial.PointCollision`, which does not
import VCVio; keeping them apart keeps VCVio's `DecidableEq` instances out of their classical
decidability searches.

## Main statements

* `Polynomial.prob_not_injOn_evalTuple_le`: for points sampled uniformly from a finite type `Ω`
  through an injective map, the probability of not separating a finite family `S` is at most
  `choose |S| 2 * d ^ |ι| / |Ω|`.
* `Polynomial.prob_not_injOn_evalTuple_le_of_encard_le`: the same for a set `S` with
  `S.encard ≤ L`, with bound `choose L 2 * d ^ |ι| / |Ω|`.
-/

@[expose] public section

namespace Polynomial

open scoped ProbabilityTheory

variable {R ι κ : Type*} [CommRing R] [IsDomain R] [Fintype ι]

/-- **Probability of not separating a finite family.** Sample `ω` uniformly from a finite
nonempty type `Ω` and use the point tuple `pt ω`. If `pt` is injective and every coordinate of
every tuple in `S` has natural degree at most `d`, the points fail to separate `S` with
probability at most `choose |S| 2 * d ^ |ι| / |Ω|`.

Injectivity of `pt` is needed to count sample points by point tuples: a constant `pt` at a
colliding point tuple fails with probability `1`. -/
theorem prob_not_injOn_evalTuple_le {Ω : Type} [Fintype Ω] [SampleableType Ω] {pt : Ω → ι → R}
    (hpt : Function.Injective pt) (S : Finset (κ → R[X])) {d : ℕ}
    (hdeg : ∀ f ∈ S, ∀ j, (f j).natDegree ≤ d) :
    Pr{let ω ← $ᵗ Ω}[¬ Set.InjOn (evalTuple (pt ω)) (S : Set (κ → R[X]))] ≤
      ENNReal.ofReal ((S.card.choose 2 * d ^ Fintype.card ι : ℕ) / (Fintype.card Ω : ℝ)) := by
  classical
  rw [SampleableType.prEvent_uniformSample_eq_ofReal]
  refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (by positivity))
  let bad := Finset.univ.filter fun ω : Ω ↦ ¬ Set.InjOn (evalTuple (pt ω)) (S : Set (κ → R[X]))
  have hcard := card_le_of_not_injOn_evalTuple S hdeg (bad.image pt) fun x hx ↦ by
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hω).2
  rw [Finset.card_image_of_injective _ hpt] at hcard
  exact_mod_cast hcard

/-- **Probability of not separating a set of bounded size.** The form of
`prob_not_injOn_evalTuple_le` for a set `S` with `S.encard ≤ L`, as supplied by a list-size bound
such as `Code.Lambda`. The bound is `choose L 2 * d ^ |ι| / |Ω|`. -/
theorem prob_not_injOn_evalTuple_le_of_encard_le {Ω : Type} [Fintype Ω] [SampleableType Ω]
    {pt : Ω → ι → R} (hpt : Function.Injective pt) {S : Set (κ → R[X])} {L d : ℕ}
    (hS : S.encard ≤ L) (hdeg : ∀ f ∈ S, ∀ j, (f j).natDegree ≤ d) :
    Pr{let ω ← $ᵗ Ω}[¬ Set.InjOn (evalTuple (pt ω)) S] ≤
      ENNReal.ofReal ((L.choose 2 * d ^ Fintype.card ι : ℕ) / (Fintype.card Ω : ℝ)) := by
  have hfin : S.Finite := Set.finite_of_encard_le_coe hS
  have hcard : hfin.toFinset.card ≤ L := by
    rw [← Set.ncard_eq_toFinset_card S hfin]
    exact Nat.cast_le.mp (hfin.cast_ncard_eq ▸ hS)
  have h := prob_not_injOn_evalTuple_le hpt hfin.toFinset fun f hf ↦
    hdeg f (hfin.mem_toFinset.mp hf)
  rw [Set.Finite.coe_toFinset] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right ?_ (by positivity)))
  exact_mod_cast Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hcard)

end Polynomial
