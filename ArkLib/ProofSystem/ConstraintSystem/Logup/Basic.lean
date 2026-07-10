/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/

import ArkLib.Data.MvPolynomial.Multilinear
import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Nat.Bitwise

/-!
# The LogUp rational identity

This file defines bus interactions, their multilinear fingerprints, and the
LogUp rational identity from leanVM §5.3.3:

```
∑ k, m_k / (γ − π_β(σ_k)) = 0.
```

It also connects natural push and pull counts over the base field to signed
multiplicities over an extension field. The `NoWrap` hypothesis is essential:
without it, unequal natural counts may become equal after reduction modulo the
base-field characteristic. Sampled bounds are in `Logup.Soundness`.

## References

* [Haböck, U., *Multivariate lookups based on logarithmic derivatives*][Hab22]
-/

open scoped BigOperators NNReal ENNReal

noncomputable section

namespace Logup

variable {F : Type*} [Field F]

/-- The big-endian bit decomposition of an integer into a fixed number of bits. -/
def bitsBE (n i : ℕ) : Vector Bool n :=
  Vector.ofFn fun k : Fin n ↦ i.testBit (n - 1 - k)

/-- The big-endian Boolean cube point corresponding to an integer index. -/
def cubePointBE {R : Type*} [Zero R] [One R] (n : ℕ) (i : Fin (2 ^ n)) : Vector R n :=
  (bitsBE n i).map fun b ↦ if b then 1 else 0

/-- ArkLib's canonical equality-kernel value, presented on vectors. -/
def eqTildeVector {n : ℕ} (x y : Vector F n) : F :=
  ∏ i : Fin n, ((1 - x.get i) * (1 - y.get i) + x.get i * y.get i)

/-- The vector presentation agrees with `MvPolynomial.eqTilde`. -/
theorem eqTildeVector_eq_eqTilde {n : ℕ} (x y : Vector F n) :
    eqTildeVector x y = MvPolynomial.eqTilde x.get y.get := by
  simp only [eqTildeVector, MvPolynomial.eqTilde, MvPolynomial.eqPolynomial,
    MvPolynomial.singleEqPolynomial, MvPolynomial.eval_prod, MvPolynomial.eval_add,
    MvPolynomial.eval_mul, MvPolynomial.eval_sub, map_one,
    MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- On big-endian Boolean points, the equality kernel is the Kronecker delta. -/
theorem eqTildeVector_cubePointBE_delta {n : ℕ} (i j : Fin (2 ^ n)) :
    eqTildeVector (cubePointBE (R := F) n i) (cubePointBE n j) =
      if i = j then (1 : F) else 0 := by
  classical
  simp only [eqTildeVector]
  split_ifs with h
  · subst j
    apply Finset.prod_eq_one
    intro k _
    by_cases hk : i.val.testBit (n - 1 - k.val) <;>
      simp [cubePointBE, bitsBE, Vector.get_eq_getElem, Vector.getElem_ofFn, hk]
  · obtain ⟨k, hk⟩ : ∃ k : Fin n, i.val.testBit k.val ≠ j.val.testBit k.val := by
      contrapose! h
      refine Fin.ext (Nat.eq_of_testBit_eq fun k ↦ ?_)
      by_cases hk : k < n
      · exact h ⟨k, hk⟩
      · have hkn : n ≤ k := Nat.le_of_not_gt hk
        have hipow : i.val < 2 ^ k :=
          i.isLt.trans_le (Nat.pow_le_pow_right two_pos hkn)
        have hjpow : j.val < 2 ^ k :=
          j.isLt.trans_le (Nat.pow_le_pow_right two_pos hkn)
        rw [Nat.testBit_eq_false_of_lt hipow, Nat.testBit_eq_false_of_lt hjpow]
    let rk : Fin n := ⟨n - 1 - k.val, by omega⟩
    have hrk : n - 1 - rk.val = k.val := by
      simp only [rk]
      omega
    refine Finset.prod_eq_zero (Finset.mem_univ rk) ?_
    cases hi : i.val.testBit k.val <;>
      cases hj : j.val.testBit k.val <;>
      simp_all [cubePointBE, bitsBE, Vector.get_eq_getElem, Vector.getElem_ofFn]

/-- A single bus interaction.

`sigma` is the interaction tuple of width `w`, and `m` is its signed
multiplicity. -/
structure Interaction (F : Type*) (w : ℕ) where
  /-- The interaction tuple of width `w`. -/
  sigma : Fin w → F
  /-- The signed multiplicity of this interaction. -/
  m : F

/-- The multilinear equality-kernel fingerprint of a tuple:

```
π_β(σ) = ∑ i, σ i * eqHat β (bits_BE i),
```

where `bits_BE i = bitsBE ell i` is the fixed big-endian bit
encoding of `i` (mapped `false ↦ 0`, `true ↦ 1`). -/
def fingerprint {w ell : ℕ} (β : Vector F ell) (σ : Fin w → F) : F :=
  ∑ i : Fin w,
    σ i * eqTildeVector β ((bitsBE ell i).map (fun b ↦ if b then (1 : F) else 0))

open Classical in
/-- For every tuple value `t`, the signed multiplicities of all
interactions carrying that tuple sum to zero. -/
noncomputable def Balanced {w K : ℕ} (I : Fin K → Interaction F w) : Prop :=
  ∀ t : Fin w → F, ∑ k, (if (I k).sigma = t then (I k).m else 0) = 0

/-! A polynomial identity is used below because a challenge-quantified
biconditional can be vacuous over a finite field. -/

/-- If the bus is balanced, then for every fingerprint parameter `β` and
challenge `γ`, the rational sum

```
∑ k, m_k / (γ − π_β(σ_k)) = 0.
```

No collision-freeness hypothesis is needed. Over the fiber of a tuple `t`, the
numerator
`M_t = ∑_{σ_k = t} m_k` already vanishes, so the group contributes `0` regardless
(using Lean's `x / 0 = 0` convention at poles). Protocol acceptance separately
requires every denominator to be nonzero. -/
theorem balanced_rational_sum_eq_zero {w K ell : ℕ} (I : Fin K → Interaction F w)
    (hbal : Balanced I) (β : Vector F ell) (γ : F) :
    ∑ k, (I k).m / (γ - fingerprint β (I k).sigma) = 0 := by
  classical
  unfold Balanced at hbal
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun k ↦ (I k).sigma)
      (t := Finset.image (fun k ↦ (I k).sigma) Finset.univ)
      (by intro k _; exact Finset.mem_image_of_mem _ (Finset.mem_univ k))]
  apply Finset.sum_eq_zero
  intro t _
  have hden' : ∀ k ∈ Finset.univ.filter (fun k ↦ (I k).sigma = t),
      (I k).m / (γ - fingerprint β (I k).sigma) = (I k).m / (γ - fingerprint β t) := by
    intro k hk
    rw [(Finset.mem_filter.mp hk).2]
  rw [Finset.sum_congr rfl hden']
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have hnum : ∑ k ∈ Finset.univ.filter (fun k ↦ (I k).sigma = t), (I k).m
      = ∑ k, (if (I k).sigma = t then (I k).m else 0) := by
    rw [Finset.sum_filter]
  rw [hnum, hbal t, zero_mul]

open Classical in
/-- The set of fingerprint values `π_β(σ_k)` occurring among the interactions.
These are the poles of the rational sum. -/
noncomputable def poleSet {w K ell : ℕ} (I : Fin K → Interaction F w)
    (β : Vector F ell) : Finset F :=
  Finset.image (fun k ↦ fingerprint β (I k).sigma) Finset.univ

open Classical in
/-- The grouped multiplicity of a fingerprint value `p`: the sum of the signed
multiplicities of all interactions whose tuple fingerprints to `p`. -/
noncomputable def groupedMult {w K ell : ℕ} (I : Fin K → Interaction F w)
    (β : Vector F ell) (p : F) : F :=
  ∑ k, (if fingerprint β (I k).sigma = p then (I k).m else 0)

open Classical in
/-- The cleared numerator polynomial of the LogUp rational sum, in the
indeterminate `Γ = X`:

```
N_{I,β}(Γ) = ∑_{p ∈ poleSet} M_p · ∏_{q ∈ poleSet, q ≠ p} (Γ − q),
```

where `M_p = groupedMult I β p`.  This is `∏_{p} (Γ − p)` times the rational sum
`∑_p M_p / (Γ − p)`, i.e. the rational identity with denominators cleared. -/
noncomputable def numeratorPoly {w K ell : ℕ} (I : Fin K → Interaction F w)
    (β : Vector F ell) : Polynomial F :=
  ∑ p ∈ poleSet I β,
    Polynomial.C (groupedMult I β p) *
      ∏ q ∈ (poleSet I β).erase p, (Polynomial.X - Polynomial.C q)

open Classical in
/-- The product `∏_{q ≠ p} (p − q)` over the (distinct) other poles is nonzero. -/
theorem poleSet_prod_erase_ne_zero {w K ell : ℕ} (I : Fin K → Interaction F w)
    (β : Vector F ell) {p : F} :
    (∏ q ∈ (poleSet I β).erase p, (p - q)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro q hq
  have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
  intro h
  exact hqp (sub_eq_zero.mp h).symm

open Classical in
/-- Evaluating the numerator polynomial at a pole `p0 ∈ poleSet` isolates the
single coefficient `M_{p0}`: `N(p0) = M_{p0} · ∏_{q ≠ p0} (p0 − q)`. -/
theorem numeratorPoly_eval {w K ell : ℕ} (I : Fin K → Interaction F w)
    (β : Vector F ell) {p0 : F} (hp0 : p0 ∈ poleSet I β) :
    (numeratorPoly I β).eval p0
      = groupedMult I β p0 * ∏ q ∈ (poleSet I β).erase p0, (p0 - q) := by
  unfold numeratorPoly
  rw [Polynomial.eval_finsetSum, Finset.sum_eq_single p0]
  · simp [Polynomial.eval_prod]
  · intro p hp hpp0
    have hmem : p0 ∈ (poleSet I β).erase p :=
      Finset.mem_erase.mpr ⟨fun h ↦ hpp0 h.symm, hp0⟩
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    have hz : ∏ q ∈ (poleSet I β).erase p, (Polynomial.X - Polynomial.C q).eval p0 = 0 :=
      Finset.prod_eq_zero hmem (by simp)
    rw [hz, mul_zero]
  · intro h; exact absurd hp0 h

open Classical in
/-- The numerator polynomial vanishes identically iff every grouped multiplicity
over an occurring pole vanishes.  This is the partial-fraction / distinct-poles
core: distinct poles make the numerator basis `∏_{q ≠ p}(X − q)` linearly
independent, so no accidental cancellation can hide a nonzero `M_p`. -/
theorem numeratorPoly_eq_zero_iff {w K ell : ℕ} (I : Fin K → Interaction F w)
    (β : Vector F ell) :
    numeratorPoly I β = 0 ↔ ∀ p ∈ poleSet I β, groupedMult I β p = 0 := by
  constructor
  · intro h p hp
    have hev : (numeratorPoly I β).eval p = 0 := by rw [h]; simp
    rw [numeratorPoly_eval I β hp] at hev
    exact (mul_eq_zero.mp hev).resolve_right (poleSet_prod_erase_ne_zero I β)
  · intro h
    unfold numeratorPoly
    apply Finset.sum_eq_zero
    intro p hp
    rw [h p hp]
    simp

open Classical in
/-- Under collision-freeness of `β` on the occurring tuples, the grouped
multiplicities (indexed by fingerprint value) all vanish iff the bus is balanced
(the tuple-indexed condition).  Collision-freeness makes grouping by fingerprint
value identical to grouping by tuple. -/
theorem groupedMult_eq_zero_iff_balanced {w K ell : ℕ} (I : Fin K → Interaction F w)
    (β : Vector F ell)
    (hcoll : ∀ k k', fingerprint β (I k).sigma = fingerprint β (I k').sigma →
      (I k).sigma = (I k').sigma) :
    (∀ p ∈ poleSet I β, groupedMult I β p = 0) ↔ Balanced I := by
  unfold groupedMult poleSet Balanced
  have key : ∀ (k k0 : Fin K),
      (fingerprint β (I k).sigma = fingerprint β (I k0).sigma) ↔ (I k).sigma = (I k0).sigma :=
    fun k k0 ↦ ⟨fun h ↦ hcoll k k0 h, fun h ↦ by rw [h]⟩
  constructor
  · intro H t
    by_cases hex : ∃ k0, (I k0).sigma = t
    · obtain ⟨k0, hk0⟩ := hex
      have hp : fingerprint β (I k0).sigma ∈
          Finset.image (fun k ↦ fingerprint β (I k).sigma) Finset.univ :=
        Finset.mem_image_of_mem _ (Finset.mem_univ k0)
      have hsum := H (fingerprint β (I k0).sigma) hp
      have hconv : (∑ k, if (I k).sigma = t then (I k).m else 0)
          = ∑ k, (if fingerprint β (I k).sigma = fingerprint β (I k0).sigma then
            (I k).m else 0) := by
        apply Finset.sum_congr rfl
        intro k _
        have hiff : ((I k).sigma = t) ↔
            (fingerprint β (I k).sigma = fingerprint β (I k0).sigma) := by rw [key k k0, ← hk0]
        by_cases h : (I k).sigma = t
        · rw [if_pos h, if_pos (hiff.mp h)]
        · rw [if_neg h, if_neg (fun hh ↦ h (hiff.mpr hh))]
      rw [hconv]; exact hsum
    · push Not at hex
      apply Finset.sum_eq_zero
      intro k _
      exact if_neg (hex k)
  · intro Hb p hp
    obtain ⟨k0, _, hk0⟩ := Finset.mem_image.mp hp
    have hsum := Hb (I k0).sigma
    have hconv : (∑ k, if fingerprint β (I k).sigma = p then (I k).m else 0)
        = ∑ k, (if (I k).sigma = (I k0).sigma then (I k).m else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      have hiff : (fingerprint β (I k).sigma = p) ↔ ((I k).sigma = (I k0).sigma) := by
        rw [← hk0, key k k0]
      by_cases h : fingerprint β (I k).sigma = p
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun hh ↦ h (hiff.mpr hh))]
    rw [hconv]; exact hsum

/-- Under collision-freeness of the fingerprint `β` on the occurring tuples, bus
balance is equivalent to the cleared numerator polynomial `numeratorPoly I β`
vanishing identically. The polynomial formulation is non-vacuous over finite
fields. -/
theorem balanced_iff_numerator_eq_zero {w K ell : ℕ} (I : Fin K → Interaction F w)
    (β : Vector F ell)
    (hcoll : ∀ k k', fingerprint β (I k).sigma = fingerprint β (I k').sigma →
      (I k).sigma = (I k').sigma) :
    Balanced I ↔ numeratorPoly I β = 0 := by
  rw [numeratorPoly_eq_zero_iff, groupedMult_eq_zero_iff_balanced I β hcoll]

/-!
## Base-field and extension-field interactions

Tuple coordinates and signed multiplicities are in `Fp`. Fingerprint parameters and the rational
challenge are sampled in the extension field `Fq`. The following declarations
make the embedding `ι : Fp →+* Fq` explicit.
-/

section Protocol

variable {Fp Fq : Type*} [Field Fp] [Field Fq]

/-- A protocol interaction before reduction modulo the base-field
characteristic. `pushes` and `pulls` are actual natural counts; their difference
is the signed multiplicity encoded in the field. -/
structure ProtocolInteraction (Fp : Type*) (w : ℕ) where
  /-- The interaction tuple, with coordinates in the base field. -/
  sigma : Fin w → Fp
  /-- The number of pushes represented by this interaction. -/
  pushes : ℕ
  /-- The number of pulls represented by this interaction. -/
  pulls : ℕ

open Classical in
/-- Total pushes of the base-field tuple `t`. -/
noncomputable def pushTotal {w K : ℕ} (I : Fin K → ProtocolInteraction Fp w)
    (t : Fin w → Fp) : ℕ :=
  ∑ k, if (I k).sigma = t then (I k).pushes else 0

open Classical in
/-- Total pulls of the base-field tuple `t`. -/
noncomputable def pullTotal {w K : ℕ} (I : Fin K → ProtocolInteraction Fp w)
    (t : Fin w → Fp) : ℕ :=
  ∑ k, if (I k).sigma = t then (I k).pulls else 0

/-- Actual bus balance, before reducing counts modulo the field characteristic. -/
def CountBalanced {w K : ℕ} (I : Fin K → ProtocolInteraction Fp w) : Prop :=
  ∀ t, pushTotal I t = pullTotal I t

/-- The no-wrap hypothesis: for every tuple, both total pushes and total
pulls are strictly smaller than the base-field characteristic `p`. -/
def NoWrap (p : ℕ) {w K : ℕ} (I : Fin K → ProtocolInteraction Fp w) : Prop :=
  ∀ t, pushTotal I t < p ∧ pullTotal I t < p

omit [Field Fp] in
/-- A common upper bound on every per-tuple push and pull total implies
`NoWrap` when the bound is below the characteristic. -/
theorem noWrap_of_totals_le {p bound w K : ℕ}
    (I : Fin K → ProtocolInteraction Fp w)
    (htotals : ∀ t, pushTotal I t ≤ bound ∧ pullTotal I t ≤ bound)
    (hbound : bound < p) : NoWrap p I := by
  intro t
  exact ⟨(htotals t).1.trans_lt hbound, (htotals t).2.trans_lt hbound⟩

/-- Encode actual push/pull counts as a signed base-field multiplicity. -/
def toBaseInteraction {w : ℕ} (x : ProtocolInteraction Fp w) : Interaction Fp w where
  sigma := x.sigma
  m := (x.pushes : Fp) - (x.pulls : Fp)

/-- Map an interaction along a field embedding. -/
def mapInteraction {w : ℕ} (ι : Fp →+* Fq) (x : Interaction Fp w) : Interaction Fq w where
  sigma := fun i ↦ ι (x.sigma i)
  m := ι x.m

open Classical in
/-- Balance is preserved and reflected by an injective field embedding. -/
theorem balanced_map_iff {w K : ℕ} (ι : Fp →+* Fq) (hι : Function.Injective ι)
    (I : Fin K → Interaction Fp w) :
    Balanced (fun k ↦ mapInteraction ι (I k)) ↔ Balanced I := by
  constructor
  · intro h t
    have hmapped := h (fun i ↦ ι (t i))
    apply hι
    rw [map_zero]
    rw [← hmapped]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hiff : (fun i ↦ ι ((I k).sigma i)) = (fun i ↦ ι (t i)) ↔
        (I k).sigma = t := by
      constructor
      · intro heq
        funext i
        exact hι (congrFun heq i)
      · intro heq
        rw [heq]
    change ι (if (I k).sigma = t then (I k).m else 0) =
      if (fun i ↦ ι ((I k).sigma i)) = (fun i ↦ ι (t i)) then ι (I k).m else 0
    by_cases hk : (I k).sigma = t
    · rw [if_pos hk, if_pos (hiff.mpr hk)]
    · rw [if_neg hk, if_neg (fun heq ↦ hk (hiff.mp heq)), map_zero]
  · intro h t
    by_cases hex : ∃ k, (mapInteraction ι (I k)).sigma = t
    · obtain ⟨k0, hk0⟩ := hex
      have hbase := h (I k0).sigma
      calc
        (∑ k, if (mapInteraction ι (I k)).sigma = t then (mapInteraction ι (I k)).m else 0) =
            ι (∑ k, if (I k).sigma = (I k0).sigma then (I k).m else 0) := by
              rw [map_sum]
              apply Finset.sum_congr rfl
              intro k _
              have hiff : (mapInteraction ι (I k)).sigma = t ↔
                  (I k).sigma = (I k0).sigma := by
                rw [← hk0]
                constructor
                · intro heq
                  funext i
                  exact hι (congrFun heq i)
                · intro heq
                  simp [mapInteraction, heq]
              change (if (fun i ↦ ι ((I k).sigma i)) = t then ι (I k).m else 0) =
                ι (if (I k).sigma = (I k0).sigma then (I k).m else 0)
              have hmapiff : (fun i ↦ ι ((I k).sigma i)) = t ↔
                  (I k).sigma = (I k0).sigma := by
                simpa [mapInteraction] using hiff
              by_cases hk : (I k).sigma = (I k0).sigma
              · rw [if_pos hk, if_pos (hmapiff.mpr hk)]
              · rw [if_neg hk, if_neg (fun heq ↦ hk (hmapiff.mp heq)), map_zero]
        _ = 0 := by rw [hbase, map_zero]
    · push Not at hex
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (hex k)]

open Classical in
/-- The grouped field multiplicity is the cast push total minus the cast pull
total. This is the algebraic core of the no-wrap bridge. -/
theorem groupedMultiplicity_eq_cast_sub {w K : ℕ}
    (I : Fin K → ProtocolInteraction Fp w) (t : Fin w → Fp) :
    (∑ k, if (toBaseInteraction (I k)).sigma = t then (toBaseInteraction (I k)).m else 0) =
      (pushTotal I t : Fp) - (pullTotal I t : Fp) := by
  change (∑ k, if (I k).sigma = t then ((I k).pushes : Fp) - (I k).pulls else 0) = _
  simp only [pushTotal, pullTotal]
  rw [Nat.cast_sum, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_zero]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (I k).sigma = t <;> simp [hk]

/-- Base-field balance is equivalent to actual count balance when neither
per-tuple total wraps modulo `p`. -/
theorem countBalanced_iff_baseBalanced {p w K : ℕ} [CharP Fp p]
    (I : Fin K → ProtocolInteraction Fp w) (hcap : NoWrap p I) :
    CountBalanced I ↔ Balanced (fun k ↦ toBaseInteraction (I k)) := by
  classical
  constructor
  · intro h t
    rw [groupedMultiplicity_eq_cast_sub (Fp := Fp)]
    rw [h t, sub_self]
  · intro h t
    have hz := h t
    rw [groupedMultiplicity_eq_cast_sub (Fp := Fp)] at hz
    have heq : (pushTotal I t : Fp) = (pullTotal I t : Fp) := sub_eq_zero.mp hz
    exact CharP.natCast_injOn_Iio Fp p (hcap t).1 (hcap t).2 heq

/-- Embed a protocol interaction from the base field into the extension field. -/
def embeddedInteraction {w : ℕ} (ι : Fp →+* Fq) (x : ProtocolInteraction Fp w) :
    Interaction Fq w :=
  mapInteraction ι (toBaseInteraction x)

/-- Under the per-tuple no-wrap hypothesis, equality of push and pull
counts is equivalent to field balance after the tuple coordinates and signed
multiplicities are mapped from `Fp` to `Fq` by the explicit embedding `ι`. -/
theorem countBalanced_iff_embeddedBalanced
    {p w K : ℕ} [CharP Fp p] (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) (hcap : NoWrap p I) :
    CountBalanced I ↔ Balanced (fun k ↦ embeddedInteraction ι (I k)) := by
  rw [show (fun k ↦ embeddedInteraction ι (I k)) =
      (fun k ↦ mapInteraction ι (toBaseInteraction (I k))) from rfl]
  rw [balanced_map_iff ι ι.injective]
  exact countBalanced_iff_baseBalanced I hcap

/-- Under no-wrap and collision-freeness, count balance is equivalent to the
cleared numerator vanishing. This theorem does not assert that a collision-free
challenge exists. -/
theorem countBalanced_iff_numerator_eq_zero {p w K ell : ℕ} [CharP Fp p]
    (ι : Fp →+* Fq) (I : Fin K → ProtocolInteraction Fp w) (hcap : NoWrap p I)
    (β : Vector Fq ell)
    (hcoll : ∀ k k',
      fingerprint β (embeddedInteraction ι (I k)).sigma =
          fingerprint β (embeddedInteraction ι (I k')).sigma →
        (embeddedInteraction ι (I k)).sigma = (embeddedInteraction ι (I k')).sigma) :
    CountBalanced I ↔ numeratorPoly (fun k ↦ embeddedInteraction ι (I k)) β = 0 := by
  rw [countBalanced_iff_embeddedBalanced ι I hcap]
  exact balanced_iff_numerator_eq_zero _ β hcoll

/-!
## Sampled protocol events and bounds

These definitions use the exact finite uniform distribution: the probability of
an event is its cardinality divided by the cardinality of the sample space.
-/

/-- A LogUp challenge consists of `ell` extension-field fingerprint parameters
and one extension-field rational challenge. -/
abbrev Challenge (Fq : Type*) (ell : ℕ) := (Fin ell → Fq) × Fq

/-- The fingerprint after explicitly embedding a base-field tuple into `Fq`. -/
def protocolFingerprint {w ell : ℕ} (ι : Fp →+* Fq) (β : Fin ell → Fq)
    (x : ProtocolInteraction Fp w) : Fq :=
  fingerprint (Vector.ofFn β) (embeddedInteraction ι x).sigma

/-- Every rational denominator is nonzero at the sampled challenge. -/
def DenominatorsNonzero {w K ell : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) (c : Challenge Fq ell) : Prop :=
  ∀ k, c.2 - protocolFingerprint ι c.1 (I k) ≠ 0

/-- The LogUp rational identity at an extension-field challenge. -/
def RationalIdentity {w K ell : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) (c : Challenge Fq ell) : Prop :=
  ∑ k, (embeddedInteraction ι (I k)).m /
    (c.2 - protocolFingerprint ι c.1 (I k)) = 0

/-- Protocol acceptance requires nonzero denominators and the rational identity.
This avoids Lean's totalized division convention turning a pole into acceptance. -/
def Accepts {w K ell : ℕ} (ι : Fp →+* Fq)
    (I : Fin K → ProtocolInteraction Fp w) (c : Challenge Fq ell) : Prop :=
  DenominatorsNonzero ι I c ∧ RationalIdentity ι I c

/-- A balanced bus accepts every pole-free challenge. Together with
the pole bound in `Logup.Soundness`, this is the completeness side of
the sampled LogUp claim. -/
theorem accepts_of_countBalanced {p w K ell : ℕ} [CharP Fp p]
    (ι : Fp →+* Fq) (I : Fin K → ProtocolInteraction Fp w)
    (hcap : NoWrap p I) (hbalanced : CountBalanced I) (c : Challenge Fq ell)
    (hden : DenominatorsNonzero ι I c) : Accepts ι I c := by
  refine ⟨hden, ?_⟩
  have hfieldBalanced := (countBalanced_iff_embeddedBalanced ι I hcap).mp hbalanced
  simpa [RationalIdentity, protocolFingerprint] using
    balanced_rational_sum_eq_zero (fun k ↦ embeddedInteraction ι (I k))
      hfieldBalanced (Vector.ofFn c.1) c.2


end Protocol

end Logup

end
