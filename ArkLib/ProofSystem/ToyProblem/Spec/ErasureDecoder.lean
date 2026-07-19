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

ArkLib has no cost harness.  The executable path uses CompPoly's pinned v4.30.0
`CPolynomial` interpolation and a finite re-encoding check.  No formal field-operation
bound, and in particular no generic `O((s n)^3)` claim, is made here.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated
  Agreement*][ABF26] (§6, App A.1).
-/

namespace ToyProblem.Spec

open CompPoly.CPolynomial
open Code InterleavedCode ListDecodable ProximityGap
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
  let p₁ : Polynomial.degreeLT F k :=
    ⟨rsPolynomial k m₁, Polynomial.mem_degreeLT.mpr (rsPolynomial_degree_lt k m₁)⟩
  let p₂ : Polynomial.degreeLT F k :=
    ⟨rsPolynomial k m₂, Polynomial.mem_degreeLT.mpr (rsPolynomial_degree_lt k m₂)⟩
  have hp : rsPolynomial k m₁ = rsPolynomial k m₂ := by
    have heval : (ReedSolomon.evalOnPoints domain).domRestrict
        (Polynomial.degreeLT F k) p₁ =
        (ReedSolomon.evalOnPoints domain).domRestrict (Polynomial.degreeLT F k) p₂ := by
      ext j
      change (rsPolynomial k m₁).eval (domain j) = (rsPolynomial k m₂).eval (domain j)
      rw [← rsEncoder_apply, ← rsEncoder_apply]
      exact congrFun h j
    exact congrArg Subtype.val
      (ReedSolomon.evalOnPoints_domRestrict_injective hcard heval)
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
    have h := minDist_div_card_eq_minRelHammingDistCode
      (ReedSolomon.code domain k : Set (ι → F))
    rw [ReedSolomon.minDist_eq' hk] at h
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
containing `≥ k` agreement coordinates. Proven `sorry`-free. -/
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
/-- A `gammaState` witness makes the computed maximal agreement set large. -/
theorem gammaAgreementSet_card_of_gammaState [Fintype ι] {k : ℕ}
    {encode : (Fin k → F) → (ι → F)} {δ : ℝ≥0} {v : Fin k → F} {μ₁ μ₂ γ : F}
    {f₁ f₂ : ι → F} {g : Fin k → F}
    (hstate : gammaState k encode δ v μ₁ μ₂ f₁ f₂ γ g) :
    (1 - (δ : ℝ)) * Fintype.card ι ≤
      (gammaAgreementSet encode f₁ f₂ γ g).card := by
  obtain ⟨-, S, hScard, hagree⟩ := hstate
  have hsub : S ⊆ gammaAgreementSet encode f₁ f₂ γ g := by
    intro j hj
    exact mem_gammaAgreementSet.mpr (hagree j hj).symm
  have hcard := Finset.card_le_card hsub
  exact hScard.trans (by exact_mod_cast hcard)

set_option linter.unusedFintypeInType false in
/-- Outside the MCA event, the concrete extractor recovers a jointly close RS message
pair whose affine folded constraint holds at `γ`.  This is the decoder-specific bridge
needed for the transition probability proof. -/
theorem rsTransitionExtractor_data_of_not_mca [Fintype ι] [Nonempty ι] [Fintype F]
    {k : ℕ} [NeZero k] (domain : ι ↪ F) (hk : k ≤ Fintype.card ι)
    {δ : ℝ≥0}
    (hδ : δ < (minRelHammingDistCode
      (ReedSolomon.code domain k : Set (ι → F)) : ℝ≥0))
    {v : Fin k → F} {μ₁ μ₂ γ : F} {f₁ f₂ : ι → F} {g : Fin k → F}
    (hstate : gammaState k (rsEncoder k domain) δ v μ₁ μ₂ f₁ f₂ γ g)
    (hmca : ¬ mcaEvent (F := F)
      (ReedSolomon.code domain k : Set (ι → F)) δ f₁ f₂ γ) :
    ∃ p : (Fin k → F) × (Fin k → F),
      rsTransitionExtractor k domain ((v, μ₁, μ₂), ![f₁, f₂]) γ g = ![p.1, p.2] ∧
      encStack (rsEncoder k domain) p ∈
        closeCodewordsRel
          (interleavedCodeSet (κ := Fin 2)
            (ReedSolomon.code domain k : Set (ι → F)))
          (fun i ↦ ![f₁ i, f₂ i]) (δ : ℝ) ∧
      (∑ j, p.1 j * v j) + γ * (∑ j, p.2 j * v j) = μ₁ + γ * μ₂ := by
  classical
  let C : Set (ι → F) := ReedSolomon.code domain k
  let enc : (Fin k → F) →ₗ[F] (ι → F) := rsEncoder k domain
  let S : Finset ι := gammaAgreementSet enc f₁ f₂ γ g
  have hScard : (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card :=
    gammaAgreementSet_card_of_gammaState hstate
  have hδ1 : δ < 1 :=
    lt_of_lt_of_le hδ (by exact_mod_cast minRelHammingDistCode_le_one C)
  have hSnn : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι := by
    have e : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by
      rw [NNReal.coe_sub hδ1.le]
      simp
    rw [ge_iff_le, ← NNReal.coe_le_coe, NNReal.coe_mul, e]
    push_cast
    linarith [hScard]
  have hencg : enc g ∈ C := by
    change rsEncoder k domain g ∈ (ReedSolomon.code domain k : Set (ι → F))
    rw [← rsEncoder_range k domain]
    exact Set.mem_range_self g
  have hpair : pairJointAgreesOn C S f₁ f₂ := by
    by_contra hno
    apply hmca
    refine ⟨S, hSnn, ⟨enc g, hencg, ?_⟩, hno⟩
    intro i hi
    exact mem_gammaAgreementSet.mp hi
  obtain ⟨u₁, hu₁, u₂, hu₂, hagree⟩ := hpair
  obtain ⟨m₁, hm₁⟩ : ∃ m₁, enc m₁ = u₁ := by
    change u₁ ∈ (ReedSolomon.code domain k : Set (ι → F)) at hu₁
    rw [← rsEncoder_range k domain] at hu₁
    obtain ⟨m₁, hm₁⟩ := hu₁
    exact ⟨m₁, hm₁⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m₂, enc m₂ = u₂ := by
    change u₂ ∈ (ReedSolomon.code domain k : Set (ι → F)) at hu₂
    rw [← rsEncoder_range k domain] at hu₂
    obtain ⟨m₂, hm₂⟩ := hu₂
    exact ⟨m₂, hm₂⟩
  have hcard : k ≤ S.card := rs_large_agreement_card domain hk hδ hScard
  have hdec₁ : rsErasureDecodeOrZero k domain S f₁ = m₁ := by
    apply rsErasureDecodeOrZero_eq hcard
    intro j hj
    rw [show rsEncoder k domain m₁ = enc m₁ from rfl, hm₁]
    exact (hagree j hj).1
  have hdec₂ : rsErasureDecodeOrZero k domain S f₂ = m₂ := by
    apply rsErasureDecodeOrZero_eq hcard
    intro j hj
    rw [show rsEncoder k domain m₂ = enc m₂ from rfl, hm₂]
    exact (hagree j hj).2
  have hextract :
      rsTransitionExtractor k domain ((v, μ₁, μ₂), ![f₁, f₂]) γ g = ![m₁, m₂] := by
    unfold rsTransitionExtractor
    change (fun i : Fin 2 ↦ rsErasureDecodeOrZero k domain
      (gammaAgreementSet (rsEncoder k domain) f₁ f₂ γ g) (![f₁, f₂] i)) = ![m₁, m₂]
    rw [show gammaAgreementSet (rsEncoder k domain) f₁ f₂ γ g = S from rfl]
    funext i
    fin_cases i
    · exact hdec₁
    · exact hdec₂
  have hclose : encStack enc (m₁, m₂) ∈
      closeCodewordsRel (interleavedCodeSet (κ := Fin 2) C)
        (fun i ↦ ![f₁ i, f₂ i]) (δ : ℝ) := by
    rw [encStack_mem_closeCodewordsRel_iff enc (rsEncoder_range k domain) hδ1]
    exact ⟨S, hScard, fun i hi ↦ by
      rw [hm₁, hm₂]
      exact ⟨(hagree i hi).1.symm, (hagree i hi).2.symm⟩⟩
  have hagreeCombined : ∀ j ∈ S, enc g j = enc (m₁ + γ • m₂) j := by
    intro j hj
    rw [map_add, map_smul]
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [hm₁, hm₂, (hagree j hj).1, (hagree j hj).2]
    exact mem_gammaAgreementSet.mp hj
  have heq : enc g = enc (m₁ + γ • m₂) :=
    codeword_eq_of_agree_on_large_set hδ hencg
      (by rw [← rsEncoder_range k domain]; exact Set.mem_range_self _)
      hScard hagreeCombined
  have hg : g = m₁ + γ • m₂ := rsEncoder_injective hk heq
  have hsum : (∑ j, (m₁ + γ • m₂) j * v j) =
      (∑ j, m₁ j * v j) + γ * (∑ j, m₂ j * v j) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, _root_.add_mul]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [_root_.mul_assoc]
  refine ⟨(m₁, m₂), hextract, hclose, ?_⟩
  rw [← hsum, ← hg]
  exact hstate.1

/-- Decoder-specific `γ`-transition bound for scalar RS.  Unlike the classical
`extractZero` proof, this bounds failure of the actual dynamic-erasure extractor.
Outside MCA, decoder recovery identifies a close message pair; if the extracted prior
state is invalid, that pair violates the two individual constraints and therefore pins
down at most one `γ`. -/
theorem rs_gamma_transition_prob_le [Fintype ι] [Nonempty ι] [Fintype F]
    {k : ℕ} [NeZero k] (domain : ι ↪ F) (hk : k ≤ Fintype.card ι)
    (δ : ℝ≥0)
    (_hδ_pos : 0 < δ)
    (hδ_lt : δ < (minRelHammingDistCode
      (ReedSolomon.code domain k : Set (ι → F)) : ℝ≥0))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i)) :
    Pr_{let γ ← $ᵖ F}[∃ g : Fin k → F,
        (stmtIn, rsTransitionExtractor k domain stmtIn γ g) ∉
          outputRelationFor k (rsEncoder k domain) δ ∧
        gammaState k (rsEncoder k domain) δ stmtIn.1.1 stmtIn.1.2.1
          stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) γ g]
      ≤ epsMCA (F := F) (A := F)
          (ReedSolomon.code domain k : Set (ι → F)) δ +
        ((Lambda (interleavedCodeSet (κ := Fin 2)
          (ReedSolomon.code domain k : Set (ι → F))) (δ : ℝ)).toNat : ℝ≥0∞)
          / (Fintype.card F : ℝ≥0∞) := by
  classical
  let C : Set (ι → F) := ReedSolomon.code domain k
  let enc : (Fin k → F) →ₗ[F] (ι → F) := rsEncoder k domain
  let fStar : ι → Fin 2 → F := fun i ↦ ![stmtIn.2 0 i, stmtIn.2 1 i]
  let Cint : Set (Matrix ι (Fin 2) F) := interleavedCodeSet (κ := Fin 2) C
  let Smsg : Finset ((Fin k → F) × (Fin k → F)) := Finset.univ.filter
    (fun p ↦ encStack enc p ∈ closeCodewordsRel Cint fStar (δ : ℝ))
  let violates : ((Fin k → F) × (Fin k → F)) → Prop := fun p ↦
    ¬ ((∑ j, p.1 j * stmtIn.1.1 j) = stmtIn.1.2.1 ∧
      (∑ j, p.2 j * stmtIn.1.1 j) = stmtIn.1.2.2)
  let Sbad : Finset ((Fin k → F) × (Fin k → F)) := Smsg.filter violates
  have hSmsg_le : Smsg.card ≤ (Lambda Cint (δ : ℝ)).toNat := by
    have hsub : encStack enc '' (Smsg : Set ((Fin k → F) × (Fin k → F))) ⊆
        closeCodewordsRel Cint fStar (δ : ℝ) := by
      rintro V ⟨p, hp, rfl⟩
      exact (Finset.mem_filter.mp hp).2
    have h1 : Smsg.card ≤ (closeCodewordsRel Cint fStar (δ : ℝ)).ncard :=
      calc Smsg.card
          = ((Smsg : Set ((Fin k → F) × (Fin k → F)))).ncard :=
              (Set.ncard_coe_finset _).symm
        _ = (encStack enc '' (Smsg : Set ((Fin k → F) × (Fin k → F)))).ncard :=
              (Set.ncard_image_of_injective _
                (encStack_injective (rsEncoder_injective hk))).symm
        _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ((closeCodewordsRel Cint fStar (δ : ℝ)).ncard : ℕ∞) ≤
        Lambda Cint (δ : ℝ) := by
      rw [Lambda]
      exact le_iSup (fun f : ι → Fin 2 → F ↦
        ((closeCodewordsRel Cint f (δ : ℝ)).ncard : ℕ∞)) fStar
    have h3 : (Smsg.card : ℕ∞) ≤ Lambda Cint (δ : ℝ) :=
      le_trans (by exact_mod_cast h1) h2
    rwa [← ENat.coe_toNat (Lambda_ne_top (C := Cint) (δ : ℝ)), Nat.cast_le] at h3
  have hcards : (Finset.univ.filter (fun γ : F ↦
      ∃ p ∈ Sbad,
        (∑ j, p.1 j * stmtIn.1.1 j) + γ * (∑ j, p.2 j * stmtIn.1.1 j) =
          stmtIn.1.2.1 + γ * stmtIn.1.2.2)).card
      ≤ (Lambda Cint (δ : ℝ)).toNat := by
    have hsub : Finset.univ.filter (fun γ : F ↦
        ∃ p ∈ Sbad,
          (∑ j, p.1 j * stmtIn.1.1 j) + γ * (∑ j, p.2 j * stmtIn.1.1 j) =
            stmtIn.1.2.1 + γ * stmtIn.1.2.2) ⊆
        Sbad.biUnion (fun p ↦ Finset.univ.filter (fun γ : F ↦
          (∑ j, p.1 j * stmtIn.1.1 j) + γ * (∑ j, p.2 j * stmtIn.1.1 j) =
            stmtIn.1.2.1 + γ * stmtIn.1.2.2)) := by
      intro γ hγ
      rw [Finset.mem_filter] at hγ
      obtain ⟨p, hp, heq⟩ := hγ.2
      rw [Finset.mem_biUnion]
      exact ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    calc ∑ p ∈ Sbad, (Finset.univ.filter (fun γ : F ↦
            (∑ j, p.1 j * stmtIn.1.1 j) + γ * (∑ j, p.2 j * stmtIn.1.1 j) =
              stmtIn.1.2.1 + γ * stmtIn.1.2.2)).card
        ≤ ∑ _p ∈ Sbad, 1 := Finset.sum_le_sum (fun p hp ↦
          affine_solution_card_le_one (Finset.mem_filter.mp hp).2)
      _ = Sbad.card := by rw [Finset.sum_const, smul_eq_mul, _root_.mul_one]
      _ ≤ Smsg.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ (Lambda Cint (δ : ℝ)).toNat := hSmsg_le
  let badAffine : F → Prop := fun γ ↦ ∃ p ∈ Sbad,
    (∑ j, p.1 j * stmtIn.1.1 j) + γ * (∑ j, p.2 j * stmtIn.1.1 j) =
      stmtIn.1.2.1 + γ * stmtIn.1.2.2
  refine le_trans (Pr_le_Pr_of_implies ($ᵖ F) _
      (fun γ ↦ mcaEvent C δ (stmtIn.2 0) (stmtIn.2 1) γ ∨ badAffine γ) ?_)
    (le_trans (Pr_or_le _ _) (add_le_add ?_ ?_))
  · rintro γ ⟨g, hbad, hstate⟩
    by_cases hmca : mcaEvent C δ (stmtIn.2 0) (stmtIn.2 1) γ
    · exact Or.inl hmca
    · right
      obtain ⟨p, hextract, hclose, haff⟩ :=
        rsTransitionExtractor_data_of_not_mca domain hk hδ_lt hstate hmca
      have hstmtEq :
          ((stmtIn.1.1, stmtIn.1.2.1, stmtIn.1.2.2), ![stmtIn.2 0, stmtIn.2 1]) =
            stmtIn := by
        apply Prod.ext
        · rfl
        · funext i
          fin_cases i <;> rfl
      have hextract' : rsTransitionExtractor k domain stmtIn γ g = ![p.1, p.2] := by
        rw [← hstmtEq]
        exact hextract
      have hδ1 : δ < 1 :=
        lt_of_lt_of_le hδ_lt (by exact_mod_cast minRelHammingDistCode_le_one C)
      have hviol : violates p := by
        intro hconstraints
        apply hbad
        rw [hextract']
        refine ⟨?_, ?_⟩
        · intro i
          fin_cases i
          · exact hconstraints.1
          · exact hconstraints.2
        · obtain ⟨S, hScard, hagree⟩ :=
            (encStack_mem_closeCodewordsRel_iff enc (rsEncoder_range k domain)
              hδ1 p).mp hclose
          refine ⟨S, hScard, fun i j hj ↦ ?_⟩
          fin_cases i
          · exact (hagree j hj).1
          · exact (hagree j hj).2
      refine ⟨p, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclose⟩, hviol⟩, haff⟩
  · unfold epsMCA
    exact le_iSup (fun u : WordStack F (Fin 2) ι ↦
      Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]) ![stmtIn.2 0, stmtIn.2 1]
  · rw [prob_uniform_eq_card_filter_div_card]
    change ((Finset.univ.filter badAffine).card : ℝ≥0∞) /
      (Fintype.card F : ℝ≥0∞) ≤ _
    exact ENNReal.div_le_div_right (by exact_mod_cast hcards) _

/-- The decoder-specific bound in the exact `UniformSample`/`ℝ≥0`-coerced shape
consumed by `rbrKnowledgeSoundnessWorstCase`. -/
theorem rs_gamma_round_game_bound [Fintype ι] [Nonempty ι] [Fintype F]
    [SampleableType F] {k : ℕ} [NeZero k]
    (domain : ι ↪ F) (hk : k ≤ Fintype.card ι) (δ : ℝ≥0)
    (hδ_pos : 0 < δ)
    (hδ_lt : δ < (minRelHammingDistCode
      (ReedSolomon.code domain k : Set (ι → F)) : ℝ≥0))
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i)) :
    Pr[fun γ : F ↦ ∃ g : Fin k → F,
        (stmtIn, rsTransitionExtractor k domain stmtIn γ g) ∉
          outputRelationFor k (rsEncoder k domain) δ ∧
        gammaState k (rsEncoder k domain) δ stmtIn.1.1 stmtIn.1.2.1
          stmtIn.1.2.2 (stmtIn.2 0) (stmtIn.2 1) γ g
      | $ᵗ F] ≤
      (((epsMCA (F := F) (A := F)
          (ReedSolomon.code domain k : Set (ι → F)) δ).toNNReal +
        ((Lambda (interleavedCodeSet (κ := Fin 2)
          (ReedSolomon.code domain k : Set (ι → F))) (δ : ℝ)).toNat : ℝ≥0)
          / (Fintype.card F : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
  rw [probEvent_uniformSample_eq_prob_uniformOfFintype]
  refine le_trans (rs_gamma_transition_prob_le domain hk δ hδ_pos hδ_lt stmtIn)
    (le_of_eq ?_)
  rw [ENNReal.coe_add,
    ENNReal.coe_toNNReal
      (epsMCA_ne_top (F := F) (A := F)
        (ReedSolomon.code domain k : Set (ι → F)) δ),
    ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
    ENNReal.coe_natCast, ENNReal.coe_natCast]

/-! ### Concrete worst-case-per-prefix RBR assembly -/

/-- Intermediate witness types for the concrete scalar-RS extractor. -/
def rsRbrWitMid (F : Type) (k : ℕ) : Fin 4 → Type
  | ⟨0, _⟩ => Witness (F := F) k
  | ⟨1, _⟩ => Fin k → F
  | ⟨2, _⟩ => Fin k → F
  | ⟨3, _⟩ => PUnit

/-- Source-faithful RBR extractor.  At challenge index zero it reads `γ` from the
length-one transcript and consumes the supplied post-`γ` witness `g`; its output is the
dynamic-set RS erasure extraction, never `extractZero`. -/
def rsRbrExtractor [Fintype ι] (k t : ℕ) (domain : ι ↪ F) :
    Extractor.RoundByRound []ₒ
      (Statement (F := F) k × (∀ i, OracleStatement ι F i))
      (Witness (F := F) k) OutputWitness
      (pSpec (ι := ι) (F := F) k t) (rsRbrWitMid F k) where
  eqIn := rfl
  extractMid
  | ⟨0, _⟩ => fun stmtIn tr g ↦
      rsTransitionExtractor k domain stmtIn (tr ⟨0, Nat.zero_lt_succ _⟩) g
  | ⟨1, _⟩ => fun _ _ w ↦ w
  | ⟨2, _⟩ => fun _ tr _ ↦ tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩
  extractOut := fun _ _ _ ↦ PUnit.unit

/-- Knowledge-state function paired with `rsRbrExtractor`. -/
noncomputable def rsRbrKSF [Fintype ι] (k t : ℕ) (domain : ι ↪ F) (δ : ℝ≥0)
    {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    ((oracleVerifier (k := k) (t := t) (rsEncoder k domain)).toVerifier).KnowledgeStateFunction
      init impl (outputRelationFor k (rsEncoder k domain) δ)
      (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness))
      (rsRbrExtractor k t domain) where
  toFun
  | ⟨0, _⟩ => fun stmtIn _ w ↦
      (stmtIn, w) ∈ outputRelationFor k (rsEncoder k domain) δ
  | ⟨1, _⟩ => fun stmtIn tr w ↦
      gammaState k (rsEncoder k domain) δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) (tr ⟨0, Nat.zero_lt_succ _⟩) w
  | ⟨2, _⟩ => fun stmtIn tr w ↦
      gammaState k (rsEncoder k domain) δ stmtIn.1.1 stmtIn.1.2.1 stmtIn.1.2.2
        (stmtIn.2 0) (stmtIn.2 1) (tr ⟨0, Nat.zero_lt_succ _⟩) w
  | ⟨3, _⟩ => fun stmtIn tr _ ↦
      accepts (k := k) (t := t) (rsEncoder k domain) stmtIn.1 stmtIn.2
        (tr ⟨0, Nat.zero_lt_succ _⟩)
        (tr ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
        (tr ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))⟩)
  toFun_empty := fun _ _ ↦ Iff.rfl
  toFun_next := fun m ↦ match m with
    | ⟨0, _⟩ => fun hDir ↦ absurd hDir (fun h ↦ Direction.noConfusion h)
    | ⟨1, _⟩ => fun _ _ _ _ _ h ↦ h
    | ⟨2, _⟩ => fun hDir ↦ absurd hDir (fun h ↦ Direction.noConfusion h)
  toFun_full := fun stmtIn tr witOut h ↦
    accepts_of_probEvent_pos_verifier_run (k := k) (t := t) init impl
      (rsEncoder k domain) stmtIn tr witOut _ h

omit [DecidableEq ι] in
/-- Scalar Reed--Solomon instance of ABF26 Lemma 6.8 with the paper-strength
worst-case-per-fixed-prefix RBR type and the executable dynamic-erasure extractor. -/
theorem protocol62_rbrKnowledgeSoundWorstCaseRS
    [Fintype ι] [Nonempty ι] [Fintype F]
    [SampleableType F] [SampleableType ι]
    {k t : ℕ} [NeZero k]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (domain : ι ↪ F) (hk : k ≤ Fintype.card ι)
    (δ : ℝ≥0) (hδ_pos : 0 < δ)
    (hδ_lt : δ < (minRelHammingDistCode
      (ReedSolomon.code domain k : Set (ι → F)) : ℝ≥0)) :
    ((oracleVerifier (k := k) (t := t)
      (rsEncoder k domain)).toVerifier).rbrKnowledgeSoundnessWorstCase
        (WitIn := Witness (F := F) k) (WitOut := OutputWitness)
        init impl (outputRelationFor k (rsEncoder k domain) δ)
        (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness))
        (fun i ↦
          if i.1 = 0 then
            (epsMCA (F := F) (A := F)
              (ReedSolomon.code domain k : Set (ι → F)) δ).toNNReal +
              ((Lambda (interleavedCodeSet (κ := Fin 2)
                (ReedSolomon.code domain k : Set (ι → F))) (δ : ℝ)).toNat : ℝ≥0) /
                (Fintype.card F : ℝ≥0)
          else (1 - δ) ^ t) := by
  classical
  unfold Verifier.rbrKnowledgeSoundnessWorstCase
  refine ⟨rsRbrWitMid F k, rsRbrExtractor k t domain,
    rsRbrKSF k t domain δ init impl, ?_⟩
  intro stmtIn i transcript
  obtain ⟨⟨iv, hi⟩, hdir⟩ := i
  rcases iv with _ | _ | _ | iv
  · exact rs_gamma_round_game_bound domain hk δ hδ_pos hδ_lt stmtIn
  · exact absurd hdir (fun h ↦ Direction.noConfusion h)
  · exact spotcheck_round_game_bound k t (rsEncoder k domain) δ stmtIn
      (transcript ⟨0, Nat.zero_lt_succ _⟩)
      (transcript ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩)
  · exact absurd hi (by omega)

omit [DecidableEq ι] in
/-- Averaged scalar-RS API, derived solely from the worst-case theorem with the same
error function. -/
theorem protocol62_rbrKnowledgeSoundRS
    [Fintype ι] [Nonempty ι] [Fintype F]
    [SampleableType F] [SampleableType ι]
    {k t : ℕ} [NeZero k]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (domain : ι ↪ F) (hk : k ≤ Fintype.card ι)
    (δ : ℝ≥0) (hδ_pos : 0 < δ)
    (hδ_lt : δ < (minRelHammingDistCode
      (ReedSolomon.code domain k : Set (ι → F)) : ℝ≥0)) :
    (oracleVerifier (k := k) (t := t) (rsEncoder k domain)).rbrKnowledgeSoundness
      (WitOut := OutputWitness) init impl
      (outputRelationFor k (rsEncoder k domain) δ)
      (Set.univ : Set ((OutputStatement × ∀ i, OutputOracleStatement i) × OutputWitness))
      (fun i ↦
        if i.1 = 0 then
          (epsMCA (F := F) (A := F)
            (ReedSolomon.code domain k : Set (ι → F)) δ).toNNReal +
            ((Lambda (interleavedCodeSet (κ := Fin 2)
              (ReedSolomon.code domain k : Set (ι → F))) (δ : ℝ)).toNat : ℝ≥0) /
              (Fintype.card F : ℝ≥0)
        else (1 - δ) ^ t) := by
  classical
  unfold OracleVerifier.rbrKnowledgeSoundness
  exact Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
    init impl (protocol62_rbrKnowledgeSoundWorstCaseRS init impl domain hk δ hδ_pos hδ_lt)

/-- Legacy fixed-node wrapper around `interpolationDecoder`.  Its node set is chosen by
the caller, so its correctness remains conditional on those coordinates being uncorrupted.
The source-faithful end-to-end path above instead uses `rsTransitionExtractor`: after
receiving `γ` and `g`, it computes `gammaAgreementSet`, decodes both rows on that dynamic
set, and is wired into `protocol62_rbrKnowledgeSoundWorstCaseRS`. -/
def interpolationExtractor (k : ℕ) (nodes : Finset ι) (domain : ι → F)
    (stmtIn : Statement (F := F) k × (∀ i, OracleStatement ι F i)) :
    Witness (F := F) k :=
  erasureExtractor k (interpolationDecoder k nodes domain) stmtIn

end ToyProblem.Spec
