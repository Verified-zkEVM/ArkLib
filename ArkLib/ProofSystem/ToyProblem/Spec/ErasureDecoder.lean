/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.ToyProblem.Spec.General
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.ToCompPoly.Univariate.Lagrange

/-!
# Executable scalar Reed--Solomon erasure decoding for the toy problem

This file implements the scalar Reed--Solomon erasure decoder used by the concrete
round-by-round extractor for ABF26 Lemma 6.8.  The known-good coordinates are computed
*after* the combination challenge `γ` from the equality
`encode g j = f₁ j + γ • f₂ j`; the decoder interpolates on that dynamic finset.

## Scope

The concrete result is for alphabet `A = F`, an injective evaluation domain
`domain : ι ↪ F`, and coefficient messages `Fin k → F`.  It is not a generic additive-
code or folded-RS decoder.  Berlekamp--Welch, Gao, and Guruswami--Sudan are raw-error
decoders and are neither needed nor used on this known-erasure path.

## Cost (aspirational; unclocked per library convention)

ArkLib has no cost harness. The executable path uses CompPoly's pinned v4.32.2
`CPolynomial` interpolation and a finite re-encoding check.  No formal field-operation
bound, and in particular no generic `O((s n)^3)` claim, is made here.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26] (§6, App A.1).
-/

namespace ToyProblem.Spec

open CompPoly.CPolynomial
open Code InterleavedCode ProximityGap
open Probability
open scoped NNReal ENNReal ProbabilityTheory

variable {ι F : Type} [DecidableEq ι] [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]

/-- Degree-`< k` polynomial whose coefficient vector is `m`.  This proof-side bridge
uses Mathlib's explicit finite-sum linear equivalence, not `Classical.choose`.  It is
noncomputable only because Mathlib's `Polynomial` semiring instance is noncomputable;
the executable encoder and decoder below do not call it. -/
noncomputable def rsPolynomial (k : ℕ) (m : Fin k → F) : Polynomial F :=
  ((Polynomial.degreeLTEquiv F k).symm m).1

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
@[simp]
theorem rsPolynomial_coeff (k : ℕ) (m : Fin k → F) (j : Fin k) :
    (rsPolynomial k m).coeff j = m j := by
  exact congrFun ((Polynomial.degreeLTEquiv F k).apply_symm_apply m) j

omit [DecidableEq F] [BEq F] [LawfulBEq F] in
theorem rsPolynomial_degree_lt (k : ℕ) (m : Fin k → F) :
    (rsPolynomial k m).degree < k := by
  exact Polynomial.mem_degreeLT.mp ((Polynomial.degreeLTEquiv F k).symm m).2

/-- Scalar Reed--Solomon evaluation encoder on an arbitrary finite injective domain. -/
def rsEncoder (k : ℕ) (domain : ι ↪ F) : (Fin k → F) →ₗ[F] (ι → F) :=
  { toFun := fun m j ↦ ∑ i, m i * domain j ^ i.val
    map_add' := by
      intro m₁ m₂
      ext j
      simp only [Pi.add_apply, _root_.add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro c m
      ext j
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [_root_.mul_assoc] }

omit [DecidableEq ι] [DecidableEq F] [BEq F] [LawfulBEq F] in
@[simp]
theorem rsEncoder_apply (k : ℕ) (domain : ι ↪ F) (m : Fin k → F) (j : ι) :
    rsEncoder k domain m j = (rsPolynomial k m).eval (domain j) := by
  have hp : rsPolynomial k m ∈ Polynomial.degreeLT F k := by
    exact Polynomial.mem_degreeLT.mpr (rsPolynomial_degree_lt k m)
  change (∑ i, m i * domain j ^ i.val) = _
  rw [Polynomial.eval_eq_sum_degreeLTEquiv hp]
  apply Finset.sum_congr rfl
  intro i _
  change m i * domain j ^ i.val = (rsPolynomial k m).coeff i * domain j ^ i.val
  rw [rsPolynomial_coeff]

omit [DecidableEq ι] [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- The executable coefficient encoder has exactly the usual degree-`< k`
Reed--Solomon code as its range. -/
theorem rsEncoder_range (k : ℕ) (domain : ι ↪ F) :
    Set.range (rsEncoder k domain) =
      (ReedSolomon.code domain k : Set (ι → F)) := by
  ext w
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨rsPolynomial k m, Polynomial.mem_degreeLT.mpr (rsPolynomial_degree_lt k m), ?_⟩
    ext j
    simp [ReedSolomon.evalOnPoints]
  · rintro ⟨p, hp, rfl⟩
    let m : Fin k → F := Polynomial.degreeLTEquiv F k ⟨p, hp⟩
    refine ⟨m, ?_⟩
    have hpoly : rsPolynomial k m = p := by
      exact congrArg Subtype.val ((Polynomial.degreeLTEquiv F k).symm_apply_apply ⟨p, hp⟩)
    ext j
    rw [rsEncoder_apply, hpoly]
    rfl

omit [DecidableEq ι] [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- Evaluation on at least `k` distinct nodes is injective on coefficient messages. -/
theorem rsEncoder_injective [Fintype ι] {k : ℕ} {domain : ι ↪ F}
    (hcard : k ≤ Fintype.card ι) : Function.Injective (rsEncoder k domain) := by
  intro m₁ m₂ h
  have hp : rsPolynomial k m₁ = rsPolynomial k m₂ := by
    by_cases hk : k = 0
    · subst k
      have hm : m₁ = m₂ := by
        funext j
        exact Fin.elim0 j
      exact congrArg (rsPolynomial (F := F) 0) hm
    · apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ domain.injective
      · intro j
        rw [← rsEncoder_apply, ← rsEncoder_apply]
        exact congrFun h j
      · apply max_lt
        · by_cases hp : rsPolynomial k m₁ = 0
          · simpa [hp] using lt_of_lt_of_le (Nat.pos_of_ne_zero hk) hcard
          · exact (Polynomial.natDegree_lt_iff_degree_lt hp).2
              (rsPolynomial_degree_lt k m₁) |>.trans_le hcard
        · by_cases hp : rsPolynomial k m₂ = 0
          · simpa [hp] using lt_of_lt_of_le (Nat.pos_of_ne_zero hk) hcard
          · exact (Polynomial.natDegree_lt_iff_degree_lt hp).2
              (rsPolynomial_degree_lt k m₂) |>.trans_le hcard
  funext j
  rw [← rsPolynomial_coeff k m₁ j, hp, rsPolynomial_coeff]

omit [DecidableEq ι] [BEq F] [LawfulBEq F] in
/-- The full RS minimum-distance hypothesis supplies at least `k` retained coordinates.
This is the erasure-radius step: no half-distance error-decoding bound is used. -/
theorem rs_large_agreement_card [Fintype ι] [Nonempty ι] {k : ℕ} [NeZero k]
    (domain : ι ↪ F) (hk : k ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain k : Set (ι → F)) : ℝ≥0))
    {S : Finset ι} (hS : (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card) :
    k ≤ S.card := by
  have hdmin :
      (((minRelHammingDistCode
        (ReedSolomon.code domain k : Set (ι → F)) : ℚ≥0) : ℝ)) =
        ((Fintype.card ι - k + 1 : ℕ) : ℝ) / Fintype.card ι := by
    letI : Inhabited ι := Classical.inhabited_of_nonempty ‹Nonempty ι›
    have h := minDist_div_card_eq_minRelHammingDistCode
      (ReedSolomon.code domain k : Set (ι → F))
    rw [ReedSolomon.minDist_eq_card_sub_min_add_1, min_eq_left hk] at h
    have hr := congrArg (fun q : ℚ => (q : ℝ)) h.symm
    norm_num at hr
    rw [Nat.cast_add, Nat.cast_one]
    exact hr
  have hδR : (δ : ℝ) <
      ((minRelHammingDistCode
        (ReedSolomon.code domain k : Set (ι → F)) : ℚ≥0) : ℝ) := by
    exact_mod_cast hδ
  rw [hdmin] at hδR
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hδmul : (δ : ℝ) * Fintype.card ι <
      (Fintype.card ι - k + 1 : ℕ) := (lt_div_iff₀ hnpos).mp hδR
  by_contra hnot
  have hcard : S.card ≤ k - 1 := by omega
  have hdecomp : Fintype.card ι - k + 1 + (k - 1) = Fintype.card ι := by omega
  have hcardR : (S.card : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast hcard
  have hdecompR : ((Fintype.card ι - k + 1 : ℕ) : ℝ) + (k - 1 : ℕ) =
      Fintype.card ι := by exact_mod_cast hdecomp
  push_cast at hS hδmul hcardR hdecompR
  nlinarith

/-- **Computable interpolation erasure decoder** (scalar `A = F`). Given a set of `k`
non-erased node coordinates `nodes` and the evaluation domain `domain`, decode a
received word `w : ι → F` by Lagrange-interpolating through the nodes and reading off
the first `k` coefficients of the (unique, degree-`< #nodes`) interpolant.

A computable `def` (Lean accepts it without `noncomputable`), though
`#print axioms interpolationDecoder` reports `[propext, Classical.choice, Quot.sound]`
inherited via `CLagrange.interpolate` (`cinterpolate_eq_interpolate` bridges it to the
Mathlib `Lagrange.interpolate` used in the correctness proof). **NB the caller must supply
uncorrupted nodes** — this decoder does not itself find or verify an agreement set. -/
def interpolationDecoder (k : ℕ) (nodes : Finset ι) (domain : ι → F)
    (w : ι → F) : Fin k → F :=
  fun j ↦ (CLagrange.interpolate nodes domain w).coeff j.val

omit [DecidableEq F] in
/-- **Correctness / left-inverse of `interpolationDecoder`.** If `p : F[X]` has degree
`< #nodes`, the `domain` is injective on `nodes`, and `w` equals `p`'s evaluations on
`nodes` (an erasure pattern: only the non-erased `nodes` coordinates matter), then the
decoder returns exactly `p`'s coefficients. This is the erasure-decoding guarantee: the
degree-`< #nodes` interpolant is unique, so decoding recovers the true message. It
discharges the `hli` hypothesis of `Spec/General.lean :: erasureExtractor_mem_of_leftInverse`
whenever the Reed–Solomon `encode` is evaluation of a degree-`< k` message over a domain
containing `≥ k` agreement coordinates. -/
theorem interpolationDecoder_eq_coeff {k : ℕ} {nodes : Finset ι} {domain : ι → F}
    {w : ι → F} {p : Polynomial F} (hinj : Set.InjOn domain nodes)
    (hdeg : p.degree < nodes.card) (hval : ∀ j ∈ nodes, p.eval (domain j) = w j)
    (j : Fin k) : interpolationDecoder k nodes domain w j = p.coeff j.val := by
  -- Bridge the computable coefficient to the underlying `Polynomial` coefficient.
  have hbridge : (CLagrange.interpolate nodes domain w).coeff j.val
      = ((CLagrange.interpolate nodes domain w).toPoly).coeff j.val := by
    rw [CompPoly.CPolynomial.toPoly, CompPoly.CPolynomial.Raw.coeff_toPoly]
  -- Identify the computable interpolant's `toPoly` with the Mathlib Lagrange interpolant,
  -- which equals `p` by uniqueness of low-degree interpolation.
  rw [interpolationDecoder, hbridge, CLagrange.cinterpolate_eq_interpolate,
    ← Lagrange.eq_interpolate_of_eval_eq w hinj hdeg hval]

/-- Executable known-erasure Reed--Solomon decoder.  It interpolates on the actual
non-erased finset, reads the first `k` coefficients, and accepts only if re-encoding
agrees with every retained coordinate. -/
def rsErasureDecoder [Fintype ι] (k : ℕ) (domain : ι ↪ F)
    (nodes : Finset ι) (w : ι → F) : Option (Fin k → F) :=
  if k ≤ nodes.card then
    let m := interpolationDecoder k nodes domain w
    if ∀ j ∈ nodes, rsEncoder k domain m j = w j then some m else none
  else none

/-- Deterministic totalization used by the RBR extractor.  Correctness shows that the
zero fallback is unreachable on the good transition event. -/
def rsErasureDecodeOrZero [Fintype ι] (k : ℕ) (domain : ι ↪ F)
    (nodes : Finset ι) (w : ι → F) : Fin k → F :=
  (rsErasureDecoder k domain nodes w).getD 0

/-- Full recovery contract for `rsErasureDecoder`: at least `k` retained distinct nodes
whose values agree with a degree-`< k` RS word recover that word's coefficient message. -/
theorem rsErasureDecoder_eq_some [Fintype ι] {k : ℕ} {domain : ι ↪ F}
    {nodes : Finset ι} {w : ι → F} {m : Fin k → F}
    (hcard : k ≤ nodes.card)
    (hval : ∀ j ∈ nodes, rsEncoder k domain m j = w j) :
    rsErasureDecoder k domain nodes w = some m := by
  have hdecode : interpolationDecoder k nodes domain w = m := by
    funext j
    rw [interpolationDecoder_eq_coeff domain.injective.injOn
      ((rsPolynomial_degree_lt k m).trans_le (WithBot.coe_le_coe.mpr hcard))
      (fun i hi ↦ by simpa using hval i hi) j]
    exact rsPolynomial_coeff k m j
  rw [rsErasureDecoder, if_pos hcard, hdecode, if_pos hval]

theorem rsErasureDecodeOrZero_eq [Fintype ι] {k : ℕ} {domain : ι ↪ F}
    {nodes : Finset ι} {w : ι → F} {m : Fin k → F}
    (hcard : k ≤ nodes.card)
    (hval : ∀ j ∈ nodes, rsEncoder k domain m j = w j) :
    rsErasureDecodeOrZero k domain nodes w = m := by
  rw [rsErasureDecodeOrZero, rsErasureDecoder_eq_some hcard hval]
  rfl

/-- The source-faithful maximal agreement set computed after `γ` and `g` are known. -/
def gammaAgreementSet [Fintype ι] {k : ℕ} (encode : (Fin k → F) → (ι → F))
    (f₁ f₂ : ι → F) (γ : F) (g : Fin k → F) : Finset ι :=
  Finset.univ.filter (fun j ↦ encode g j = f₁ j + γ • f₂ j)

omit [DecidableEq ι] [BEq F] [LawfulBEq F] in
@[simp]
theorem mem_gammaAgreementSet [Fintype ι] {k : ℕ}
    {encode : (Fin k → F) → (ι → F)}
    {f₁ f₂ : ι → F} {γ : F} {g : Fin k → F} {j : ι} :
    j ∈ gammaAgreementSet encode f₁ f₂ γ g ↔
      encode g j = f₁ j + γ • f₂ j := by
  simp [gammaAgreementSet]

/-- Concrete scalar-RS transition extractor from ABF26 Lemma 6.8.  It consumes both
the fresh challenge `γ` and the post-transition witness `g`, computes `S(γ,g)`, and
erasure-decodes both input rows on that same set. -/
def rsTransitionExtractor [Fintype ι] (k : ℕ) (domain : ι ↪ F)
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i))
    (γ : F) (g : Fin k → F) : Witness (F := F) k :=
  let S := gammaAgreementSet (rsEncoder k domain) (stmtIn.2 0) (stmtIn.2 1) γ g
  fun i ↦ rsErasureDecodeOrZero k domain S (stmtIn.2 i)

omit [DecidableEq ι] [BEq F] [LawfulBEq F] in
/-- A `GammaState` witness makes the computed maximal agreement set large. -/
theorem gammaAgreementSet_card_of_gammaState [Fintype ι] {k : ℕ}
    {encode : (Fin k → F) → (ι → F)} {δ : ℝ≥0} {v : Fin k → F} {μ₁ μ₂ γ : F}
    {f₁ f₂ : ι → F} {g : Fin k → F}
    (hstate : GammaState k encode δ v μ₁ μ₂ f₁ f₂ γ g) :
    (1 - (δ : ℝ)) * Fintype.card ι ≤
      (gammaAgreementSet encode f₁ f₂ γ g).card := by
  obtain ⟨-, S, hScard, hagree⟩ := hstate
  have hsub : S ⊆ gammaAgreementSet encode f₁ f₂ γ g := by
    intro j hj
    exact mem_gammaAgreementSet.mpr (hagree j hj).symm
  have hcard := Finset.card_le_card hsub
  exact hScard.trans (by exact_mod_cast hcard)

end ToyProblem.Spec
