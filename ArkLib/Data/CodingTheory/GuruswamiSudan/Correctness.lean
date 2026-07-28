/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/

import ArkLib.Data.CodingTheory.GuruswamiSudan.Executable
import ArkLib.Data.CodingTheory.GuruswamiSudan.GuruswamiSudan

/-!
# Executable Guruswami-Sudan Correctness

Correctness statements connecting the executable CompPoly-backed
Guruswami-Sudan decoder with the ArkLib Reed-Solomon specification.
-/

namespace GuruswamiSudan

open Polynomial ReedSolomon

variable {F : Type} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
variable {k n e r D : Nat}
variable {w : CompPoly.GuruswamiSudan.GSReceivedWord F} {ωs : Fin n ↪ F} {f : Fin n → F}

/-- Packed runtime input represents the ArkLib `(ωs, f)` specification input. -/
def RepresentsArkInput
    (w : CompPoly.GuruswamiSudan.GSReceivedWord F) (ωs : Fin n ↪ F) (f : Fin n → F) : Prop :=
  w.points = Array.ofFn fun i : Fin n => (ωs i, f i)

/-- Semantic Reed-Solomon list-decoding specification for GS. -/
def GSSpecSet (k e : Nat) (ωs : Fin n ↪ F) (f : Fin n → F) : Set F[X] :=
  {p | p.degree < (k : WithBot Nat) ∧ Δ₀(f, p.eval ∘ ωs) ≤ e}

/-! ### Parameter certificates

A `GSParamCert` carries no interpolation-witness obligation: that obligation is
discharged generically by `interpolationWitnessExists_of_capacity`. A certificate is
therefore *exactly* the decidable integer check `paramsPassIntegerChecks`, and is
constructible by `decide`. -/

/-- The decidable check `paramsPassIntegerChecks` is equivalent to `GSParamCert`;
certificates are therefore constructible by `decide`. -/
theorem paramsPassIntegerChecks_iff
    (k n e : Nat) (params : CompPoly.GuruswamiSudan.GSExecParams) :
    paramsPassIntegerChecks k n e params = true ↔ GSParamCert k n e params := by
  unfold paramsPassIntegerChecks
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨hk, he⟩, hm⟩, hcap⟩, hagree⟩
    exact ⟨hk, he, hm, hcap, hagree⟩
  · rintro ⟨hk, he, hm, hcap, hagree⟩
    exact ⟨⟨⟨⟨hk, he⟩, hm⟩, hcap⟩, hagree⟩

/-- A concrete, fully discharged `GSParamCert` with message degree `k = 2` (so the
interpolation step is genuinely non-degenerate): length `n = 5`, decoding radius
`e = 1`, multiplicity `1`, and weighted-degree bound `3`. The whole certificate —
including the interpolation-witness existence — is settled by `decide`. -/
example : GSParamCert 2 5 1 (execParamsOfMultiplicityAndDegree 2 1 1 3) :=
  (paramsPassIntegerChecks_iff 2 5 1 _).mp (by decide)

open CompPoly.GuruswamiSudan in
/-- Whatever the bounded integer search returns is a valid certificate: the search
only emits parameters that pass `paramsPassIntegerChecks`, which is exactly a
`GSParamCert`. This provides the `sound` field of `boundedSearchParamSelector`
unconditionally. -/
theorem searchParamsUpTo_sound {maxM maxW k n e : Nat} {params : GSExecParams}
    (h : searchParamsUpTo maxM maxW k n e = some params) :
    GSParamCert k n e params := by
  refine (paramsPassIntegerChecks_iff k n e params).mp ?_
  unfold searchParamsUpTo at h
  obtain ⟨l₁, mult, l₂, -, hf, -⟩ := List.findSome?_eq_some_iff.mp h
  split at hf
  · next wdb hfind =>
      obtain rfl := Option.some.inj hf
      exact (List.find?_eq_some_iff_getElem.mp hfind).1
  · next => exact absurd hf (by simp)

/-- The bounded integer search as a `GSParamSelector`, with soundness supplied by
`searchParamsUpTo_sound`. The completeness obligation is passed explicitly: it holds
when the search bounds are large enough to contain valid parameters (see
`searchParamsUpTo_complete`); the required multiplicity grows without bound as the
decoding radius approaches the Johnson bound. -/
def boundedSearchParamSelector {maxM maxW : Nat}
    (complete : ∀ {k n e}, JohnsonSpecCondition k n e →
        ∃ params, searchParamsUpTo maxM maxW k n e = some params ∧ GSParamCert k n e params) :
    GSParamSelector where
  toCompPolySelector := { choose := searchParamsUpTo maxM maxW }
  sound := fun h => searchParamsUpTo_sound h
  complete := complete

open CompPoly.GuruswamiSudan in
/-- Completeness of the bounded search relative to its box: if some parameter pair
`(m, D)` within the search bounds passes the integer checks, the search returns a valid
certificate. Combined with `paramsCert_of_johnson` this discharges completeness whenever
the box is large enough to contain the Johnson-radius parameters. -/
theorem searchParamsUpTo_complete {maxM maxW k n e : Nat}
    (hex : ∃ m D, 0 < m ∧ m ≤ maxM ∧ D ≤ maxW ∧
        paramsPassIntegerChecks k n e (execParamsOfMultiplicityAndDegree k e m D) = true) :
    ∃ params, searchParamsUpTo maxM maxW k n e = some params ∧ GSParamCert k n e params := by
  obtain ⟨m, D, hm, hmM, hDW, hpass⟩ := hex
  have hisSome : (searchParamsUpTo maxM maxW k n e).isSome := by
    rw [Option.isSome_iff_ne_none]
    intro hnone
    unfold searchParamsUpTo at hnone
    rw [List.findSome?_eq_none_iff] at hnone
    have hmmem : m ∈ List.range' 1 maxM := by rw [List.mem_range'_1]; omega
    have hinner := hnone m hmmem
    have hDmem : D ∈ List.range (maxW + 1) := by rw [List.mem_range]; omega
    have hfindNe : (List.range (maxW + 1)).find?
        (fun wdb => paramsPassIntegerChecks k n e
          (execParamsOfMultiplicityAndDegree k e m wdb)) ≠ none := by
      intro hfn
      exact absurd hpass (List.find?_eq_none.mp hfn D hDmem)
    revert hinner
    cases hfc : (List.range (maxW + 1)).find?
        (fun wdb => paramsPassIntegerChecks k n e
          (execParamsOfMultiplicityAndDegree k e m wdb)) with
    | none => intro _; exact hfindNe hfc
    | some wdb => intro h; simp at h
  obtain ⟨params, hsome⟩ := Option.isSome_iff_exists.mp hisSome
  exact ⟨params, hsome, searchParamsUpTo_sound hsome⟩

/-- **Johnson-bound parameter existence.** Within the Johnson radius there exist valid
Guruswami–Sudan parameters: a multiplicity `m > 0` whose canonical degree bound yields
a full `GSParamCert`. This is the backend- and search-independent completeness content
of the decoder — it says the `GSParamCert` hypotheses are *reachable for every input
inside the radius*, with `m` chosen via `exists_multiplicity_of_johnson`. -/
theorem paramsCert_of_johnson {k n e : Nat} (hjohnson : JohnsonSpecCondition k n e) :
    ∃ m, 0 < m ∧
      GSParamCert k n e
        (execParamsOfMultiplicityAndDegree k e m (proximity_gap_degree_bound k n m)) := by
  unfold JohnsonSpecCondition at hjohnson
  have heNonneg : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  have hsqrtNonneg := Real.sqrt_nonneg (((k : ℝ) + 1) * (n : ℝ))
  have hnPos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp only [Nat.cast_zero, mul_zero, Real.sqrt_zero, sub_zero] at hjohnson
      linarith
    · exact h
  have hnPosR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hk : k + 1 ≤ n := by
    by_contra hc
    have hnk : (n : ℝ) ≤ ↑k + 1 := by
      have : n ≤ k := by omega
      exact_mod_cast Nat.le_succ_of_le this
    have hle : (↑n : ℝ) * ↑n ≤ (↑k + 1) * ↑n := by nlinarith
    have hge : Real.sqrt ((↑k + 1) * ↑n) ≥ ↑n :=
      calc Real.sqrt ((↑k + 1) * ↑n) ≥ Real.sqrt (↑n * ↑n) := Real.sqrt_le_sqrt hle
        _ = ↑n := Real.sqrt_mul_self (le_of_lt hnPosR)
    linarith
  have he : e ≤ n := by
    have : (e : ℝ) < n := by linarith
    exact_mod_cast le_of_lt this
  obtain ⟨m, hm, hgap⟩ := exists_multiplicity_of_johnson hjohnson
  refine ⟨m, hm, rfl, rfl, hm, ?_, ?_⟩
  · change numVars k (proximity_gap_degree_bound k n m) > numConstraints n m
    exact numVars_gt_numConstraints k n m
  · change proximity_gap_degree_bound k n m < m * (n - e)
    have hreal := sufficient_multiplicity_bound hk hm hgap
    have hcast : (proximity_gap_degree_bound k n m : ℝ) < ((m * (n - e) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub he]; exact hreal
    exact_mod_cast hcast

open Classical in
/-- A noncomputable `GSParamSelector` that returns a valid certificate exactly when one
exists: soundness is immediate and completeness follows from `paramsCert_of_johnson`. It
inhabits the `GSParamSelector` abstraction with both soundness and unconditional
completeness, so the selector-backed decode theorems (`decode_sound`, `decode_complete`,
`mem_decode_iff_spec`) are not vacuous. `boundedSearchParamSelector` is the computable
variant, with completeness conditional on the search bounds. -/
noncomputable def johnsonParamSelector : GSParamSelector where
  toCompPolySelector :=
    { choose := fun k n e =>
        if h : ∃ params, GSParamCert k n e params then some h.choose else none }
  sound := by
    intro k n e params h
    dsimp only at h
    split at h
    · next hex => obtain rfl := Option.some.inj h; exact hex.choose_spec
    · next => simp at h
  complete := by
    intro k n e hjohnson
    have hcert : ∃ params, GSParamCert k n e params := by
      obtain ⟨m, _, hm⟩ := paramsCert_of_johnson hjohnson
      exact ⟨_, hm⟩
    exact ⟨hcert.choose, dif_pos hcert, hcert.choose_spec⟩

/-! ### Backend-agnostic interpolation-witness existence

The CompPoly decoder takes the existence of an interpolation witness as a hypothesis
(`GSInterpContext.complete`, `GSFilteredCoreContext.complete`). It is discharged here
from the combinatorial capacity condition `numVars > numConstraints`. The statement
mentions only CompPoly's semantic `ValidInterpolationWitness`, so it is independent of
any concrete interpolation backend; the proof uses the dense backend as a constructive
existence proof. -/

open CompPoly.CBivariate in
/-- Membership in the finite monomial grid. -/
private lemma mem_monomialGrid {D : Nat} {mm : Monomial} :
    mm ∈ monomialGrid D ↔ mm.xDegree ≤ D ∧ mm.yDegree ≤ D := by
  obtain ⟨x, y⟩ := mm
  simp only [monomialGrid, List.mem_flatMap, List.mem_map, List.mem_range, Monomial.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, rfl⟩; omega
  · rintro ⟨hx, hy⟩; exact ⟨y, by omega, x, by omega, rfl, rfl⟩

open CompPoly.GuruswamiSudan CompPoly.CBivariate in
/-- The dense interpolation monomial basis has exactly `numVars` elements. -/
theorem interpolationMonomials_size (params : GSInterpParams) :
    (interpolationMonomials params).size =
      numVars params.messageDegree params.weightedDegreeBound := by
  have hsize :
      (interpolationMonomials params).size =
        ((monomialGrid params.weightedDegreeBound).filter
          (fun mm => 1 * mm.xDegree +
            (params.messageDegree - 1) * mm.yDegree ≤ params.weightedDegreeBound)).length := by
    simp [interpolationMonomials, monomialsWeightedDegreeLE, yWeight]
  rw [hsize, ← List.toFinset_card_of_nodup ((monomialGrid_nodup _).filter _),
    numVars, weigthBoundIndices]
  have einj : Function.Injective (fun mm : Monomial => (mm.xDegree, mm.yDegree)) := by
    intro a b h; cases a; cases b; simpa using h
  rw [← Finset.card_image_of_injective _ einj]
  congr 1
  ext p
  obtain ⟨i, j⟩ := p
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_filter, Finset.mem_filter,
    Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range, mem_monomialGrid,
    Prod.mk.injEq, Nat.lt_succ_iff, one_mul, decide_eq_true_eq]
  constructor
  · rintro ⟨mm, ⟨⟨hx, hy⟩, hbound⟩, rfl, rfl⟩
    exact ⟨⟨hx, hy⟩, hbound⟩
  · rintro ⟨⟨hx, hy⟩, hbound⟩
    exact ⟨⟨i, j⟩, ⟨⟨hx, hy⟩, hbound⟩, rfl, rfl⟩

/-- Sum of a constant over a list. -/
private lemma sum_map_const {α : Type*} (l : List α) (c : Nat) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- Each fold step pushes one element, so the size grows by the list length. -/
private lemma foldl_push_size {α β : Type*} (g : Array β → α → β)
    (xs : List α) (acc : Array β) :
    (xs.foldl (fun c x => c.push (g c x)) acc).size = acc.size + xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih, Array.size_push, List.length_cons]; omega

/-- Size of a fold whose every step grows the accumulator by `d x`. -/
private lemma foldl_size_add {α β : Type*} (step : Array β → α → Array β) (d : α → Nat)
    (hstep : ∀ c x, (step c x).size = c.size + d x) (xs : List α) (acc : Array β) :
    (xs.foldl step acc).size = acc.size + (xs.map d).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih, hstep, List.map_cons, List.sum_cons]; omega

/-- The per-point constraint count: `∑_{a<m} (m - a) = m(m+1)/2` (doubled form). -/
private lemma sum_range'_sub_two (m : Nat) :
    2 * ((List.range' 0 m).map (fun a => m - a)).sum = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range'_concat, List.map_append, List.sum_append,
        show ((List.range' 0 m).map (fun a => (m + 1) - a))
            = (List.range' 0 m).map (fun a => (m - a) + 1) from
          List.map_congr_left (fun a ha => by
            have h := List.mem_range'_1.mp ha; omega)]
      have hsucc : ∀ (l : List Nat) (f : Nat → Nat),
          (l.map (fun a => f a + 1)).sum = (l.map f).sum + l.length := by
        intro l f
        induction l with
        | nil => simp
        | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
      rw [hsucc, List.length_range']
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add,
        Nat.one_mul, Nat.add_sub_cancel_left, Nat.add_zero]
      rw [show (List.map (HSub.hSub m) (List.range' 0 m))
            = (List.map (fun a => m - a) (List.range' 0 m)) from rfl]
      nlinarith [ih]

open CompPoly.GuruswamiSudan in
/-- Explicit `foldl` form of the constraint enumeration loop. -/
private def constraintsFold {F : Type*} (points : Array (F × F)) (m : Nat) :
    Array (InterpolationConstraint F) :=
  points.toList.foldl
    (fun cs point =>
      (List.range' 0 m).foldl
        (fun cs a =>
          (List.range' 0 (m - a)).foldl
            (fun cs b => cs.push ⟨point.1, point.2, a, b⟩) cs) cs) #[]

open CompPoly.GuruswamiSudan in
private lemma interpolationConstraints_eq_fold {F : Type*}
    (points : Array (F × F)) (m : Nat) :
    interpolationConstraints points m = constraintsFold points m := by
  unfold interpolationConstraints constraintsFold
  simp

open CompPoly.GuruswamiSudan in
/-- The dense interpolation constraint system has exactly `numConstraints` rows. -/
theorem interpolationConstraints_size {F : Type*}
    (points : Array (F × F)) (m : Nat) :
    (interpolationConstraints points m).size = numConstraints points.size m := by
  have inner : ∀ (point : F × F) (a : Nat) (cs : Array (InterpolationConstraint F)),
      ((List.range' 0 (m - a)).foldl
        (fun cs b => cs.push ⟨point.1, point.2, a, b⟩) cs).size = cs.size + (m - a) := by
    intro point a cs
    rw [foldl_push_size, List.length_range']
  have middle : ∀ (point : F × F) (cs : Array (InterpolationConstraint F)),
      ((List.range' 0 m).foldl
        (fun cs a => (List.range' 0 (m - a)).foldl
          (fun cs b => cs.push ⟨point.1, point.2, a, b⟩) cs) cs).size
        = cs.size + ((List.range' 0 m).map (fun a => m - a)).sum :=
    fun point cs =>
      foldl_size_add _ (fun a => m - a) (fun cs a => inner point a cs) (List.range' 0 m) cs
  have hS : ((List.range' 0 m).map (fun a => m - a)).sum = m * (m + 1) / 2 := by
    have h2 := sum_range'_sub_two m
    omega
  rw [interpolationConstraints_eq_fold, constraintsFold,
    foldl_size_add _ (fun _ => ((List.range' 0 m).map (fun a => m - a)).sum)
      (fun cs point => middle point cs) points.toList #[],
    sum_map_const, Array.size_empty, Array.length_toList, hS, numConstraints,
    card_constraintIndices, Nat.zero_add]

open CompPoly.GuruswamiSudan in
/-- The capacity condition `numVars > numConstraints` forces a nonzero interpolation
witness to exist. This is the mathematical content behind the GS interpolation step and
is independent of any concrete interpolation backend: the existence of `Q` is a property
of `CBivariate` polynomials, and the proof uses the dense backend as a constructive
witness. -/
theorem interpolationWitnessExists_of_capacity
    {F : Type} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (params : GSInterpParams) (points : Array (F × F))
    (hcap : numVars params.messageDegree params.weightedDegreeBound >
              numConstraints points.size params.multiplicity) :
    ∃ Q, ValidInterpolationWitness points params Q := by
  have hSlack : HasInterpolationDimensionSlack points params := by
    unfold HasInterpolationDimensionSlack HasInterpolationDimensionSlackOnBasis
    rw [interpolationConstraints_size, interpolationMonomials_size]
    exact hcap
  obtain ⟨Q, hQ⟩ := denseInterpolate_exists_of_dimension_slack points params hSlack
  exact ⟨Q, denseInterpolate_sound (kernelContext := denseLinearKernelContext F) hQ⟩

private lemma list_foldl_count_false {α : Type*}
    (xs : List α) (p : α → Bool) (acc : Nat) :
    xs.foldl (fun count x => if p x then count else count + 1) acc =
      acc + (xs.filter fun x => p x = false).length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : p x
      · simp [hx, ih]
      · simp [hx, ih]
        omega

private lemma list_foldl_count_true {α : Type*}
    (xs : List α) (p : α → Bool) (acc : Nat) :
    xs.foldl (fun count x => if p x then count + 1 else count) acc =
      acc + (xs.filter fun x => p x = true).length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : p x
      · simp [hx, ih]
        omega
      · simp [hx, ih]

private lemma length_filter_ofFn_eq_card {α : Type*} {n : Nat}
    (g : Fin n → α) (p : α → Prop) [DecidablePred p] :
    ((List.ofFn g).filter p).length =
      (Finset.univ.filter fun i => p (g i)).card := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ]
      rw [show
          (Finset.univ.filter fun i : Fin (n + 1) => p (g i)).card =
            ∑ i : Fin (n + 1), if p (g i) then 1 else 0 by
        rw [Finset.card_filter]]
      rw [Fin.sum_univ_succ]
      by_cases h0 : p (g 0)
      · simp [h0, ih]
        omega
      · simp [h0, ih]

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private def cPolynomialOfPoly (p : F[X]) : CompPoly.CPolynomial F :=
  ⟨p.toImpl, CompPoly.CPolynomial.Raw.isCanonical_toImpl p⟩

omit [BEq F] [LawfulBEq F] [DecidableEq F] in
private theorem cPolynomialOfPoly_toPoly (p : F[X]) :
    (cPolynomialOfPoly p).toPoly = p := by
  change p.toImpl.toPoly = p
  exact CompPoly.CPolynomial.Raw.toPoly_toImpl

omit [DecidableEq F] in
private theorem degreeLt_cPolynomialOfPoly_of_degree_lt {p : F[X]}
    (hp : p.degree < (k : WithBot Nat)) :
    CompPoly.GuruswamiSudan.degreeLt (cPolynomialOfPoly p) k := by
  unfold CompPoly.GuruswamiSudan.degreeLt
  rw [CompPoly.CPolynomial.degree_toPoly, cPolynomialOfPoly_toPoly]
  exact hp

/-- Packed CompPoly mismatch count agrees with ArkLib Hamming distance. -/
theorem candidateMismatchCount_represents_hammingDist
    {cp : CompPoly.CPolynomial F}
    (hrep : RepresentsArkInput w ωs f) :
    CompPoly.GuruswamiSudan.candidateMismatchCount w.points cp =
      Δ₀(f, cp.toPoly.eval ∘ ωs) := by
  rw [hrep]
  unfold CompPoly.GuruswamiSudan.candidateMismatchCount
  rw [← Array.foldl_toList]
  simp only [Array.toList_ofFn]
  rw [list_foldl_count_false, Nat.zero_add, length_filter_ofFn_eq_card]
  rw [hammingDist]
  simp only [CompPoly.CPolynomial.eval_toPoly, Function.comp_apply,
    beq_eq_false_iff_ne, ne_eq]
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_comm

/-- Packed CompPoly distance filtering agrees with ArkLib Hamming distance. -/
theorem passesCandidateDistance_represents_hammingDist
    {cp : CompPoly.CPolynomial F}
    (hrep : RepresentsArkInput w ωs f) :
    CompPoly.GuruswamiSudan.passesCandidateDistance w.points e cp = true ↔
      Δ₀(f, cp.toPoly.eval ∘ ωs) ≤ e := by
  rw [CompPoly.GuruswamiSudan.passesCandidateDistance_iff,
    candidateMismatchCount_represents_hammingDist hrep]

omit [Field F] [BEq F] [LawfulBEq F] [DecidableEq F] in
/-- Runtime words representing an ArkLib embedding have distinct `x` coordinates. -/
theorem distinctXCoordinates_of_represents
    (hrep : RepresentsArkInput w ωs f) :
    CompPoly.GuruswamiSudan.DistinctXCoordinates w.points := by
  rw [hrep]
  unfold CompPoly.GuruswamiSudan.DistinctXCoordinates
  simpa [Function.comp_def] using (List.nodup_ofFn.2 ωs.injective)

/-- Packed CompPoly agreement count is the ArkLib agreement-set cardinality. -/
theorem matchingPointCount_represents_card
    {cp : CompPoly.CPolynomial F}
    (hrep : RepresentsArkInput w ωs f) :
    CompPoly.GuruswamiSudan.matchingPointCount w.points cp =
      (Finset.univ.filter fun i : Fin n => f i = cp.toPoly.eval (ωs i)).card := by
  rw [hrep]
  unfold CompPoly.GuruswamiSudan.matchingPointCount
  rw [← Array.foldl_toList]
  simp only [Array.toList_ofFn]
  rw [list_foldl_count_true, Nat.zero_add, length_filter_ofFn_eq_card]
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [CompPoly.CPolynomial.eval_toPoly]
  simp only [beq_iff_eq]
  exact eq_comm

omit [BEq F] [LawfulBEq F] in
/-- Agreement and Hamming-distance positions partition the block. -/
theorem agreement_card_add_hammingDist
    (p : F[X]) :
    (Finset.univ.filter fun i : Fin n => f i = p.eval (ωs i)).card +
      Δ₀(f, p.eval ∘ ωs) = n := by
  rw [hammingDist]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n)))
    (p := fun i : Fin n => f i = p.eval (ωs i))
  simpa [Finset.card_univ, Function.comp_apply] using hcard

omit [Field F] [BEq F] [LawfulBEq F] [DecidableEq F] in
/-- Runtime word length agrees with the represented ArkLib block length. -/
theorem length_of_represents
    (hrep : RepresentsArkInput w ωs f) :
    w.length = n := by
  rw [CompPoly.GuruswamiSudan.GSReceivedWord.length, hrep]
  simp

omit [DecidableEq F] in
/-- CompPoly bounded degree transfers to mathlib polynomial degree. -/
theorem toPoly_degree_lt_of_degreeLt
    {cp : CompPoly.CPolynomial F} {k : Nat}
    (h : CompPoly.GuruswamiSudan.degreeLt cp k) :
    cp.toPoly.degree < (k : WithBot Nat) := by
  simpa [CompPoly.GuruswamiSudan.degreeLt, CompPoly.CPolynomial.degree_toPoly] using h

omit [DecidableEq F] in
/-- Nat-degree form of `toPoly_degree_lt_of_degreeLt` for positive bounds. -/
theorem toPoly_natDegree_lt_of_degreeLt
    {cp : CompPoly.CPolynomial F} {k : Nat}
    (hk : 0 < k)
    (h : CompPoly.GuruswamiSudan.degreeLt cp k) :
    cp.toPoly.natDegree < k := by
  by_cases hzero : cp.toPoly = 0
  · simpa [hzero] using hk
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).2
      (toPoly_degree_lt_of_degreeLt h)

/-- Degree-and-distance characterization for the explicit-parameter decoder. -/
theorem mem_decodeWithParams_iff_degree_and_distance
    (ctx : CompPoly.GuruswamiSudan.GSFilteredCoreContext F)
    (params : CompPoly.GuruswamiSudan.GSExecParams)
    (hparams : GSParamCert k n e params)
    (hrep : RepresentsArkInput w ωs f)
    {p : F[X]} :
    (∃ cp,
      cp ∈ (CompPoly.GuruswamiSudan.decodeWithParams ctx params w).toList ∧
        cp.toPoly = p) ↔
      p.degree < (k : WithBot Nat) ∧
        Δ₀(f, p.eval ∘ ωs) ≤ e := by
  constructor
  · rintro ⟨cp, hcp, rfl⟩
    have hsound := ctx.sound
      (points := w.points) (params := params.interp) (radius := params.radius)
      (p := cp) (by simpa [CompPoly.GuruswamiSudan.decodeWithParams] using hcp)
    rcases hsound with ⟨_Q, _hvalid, hdeg, _hroot, hdist⟩
    constructor
    · have hdegPoly := toPoly_degree_lt_of_degreeLt hdeg
      simpa [hparams.messageDegree_eq] using hdegPoly
    · rw [← candidateMismatchCount_represents_hammingDist (cp := cp) hrep]
      simpa [hparams.radius_eq] using hdist
  · intro hp
    let cp : CompPoly.CPolynomial F := cPolynomialOfPoly p
    have hcp_toPoly : cp.toPoly = p := cPolynomialOfPoly_toPoly p
    have hpoints_size : w.points.size = n := by
      simpa [CompPoly.GuruswamiSudan.GSReceivedWord.length] using length_of_represents hrep
    have hInterpExists :
        ∃ Q,
          CompPoly.GuruswamiSudan.ValidInterpolationWitness w.points params.interp Q :=
      interpolationWitnessExists_of_capacity params.interp w.points
        (by rw [hparams.messageDegree_eq, hpoints_size]; exact hparams.interpolation_capacity)
    have hdistinct := distinctXCoordinates_of_represents hrep
    have hcpdeg :
        CompPoly.GuruswamiSudan.degreeLt cp params.interp.messageDegree := by
      have hdegK := degreeLt_cPolynomialOfPoly_of_degree_lt (k := k) hp.1
      simpa [cp, hparams.messageDegree_eq] using hdegK
    have hmatchLower :
        n - e ≤ CompPoly.GuruswamiSudan.matchingPointCount w.points cp := by
      rw [matchingPointCount_represents_card (cp := cp) hrep, hcp_toPoly]
      have hsum := agreement_card_add_hammingDist (f := f) (ωs := ωs) p
      omega
    have hmatches :
        params.interp.weightedDegreeBound <
          params.interp.multiplicity *
            CompPoly.GuruswamiSudan.matchingPointCount w.points cp := by
      exact lt_of_lt_of_le hparams.enough_agreement_bound
        (Nat.mul_le_mul_left params.interp.multiplicity hmatchLower)
    have hpass :
        CompPoly.GuruswamiSudan.passesCandidateDistance w.points params.radius cp =
          true := by
      rw [passesCandidateDistance_represents_hammingDist
        (e := params.radius) (cp := cp) hrep]
      simpa [hparams.radius_eq, hcp_toPoly] using hp.2
    have hmem := ctx.complete
      (points := w.points) (params := params.interp) (radius := params.radius)
      (p := cp) hInterpExists hdistinct hcpdeg hmatches hpass
    exact ⟨cp, by simpa [CompPoly.GuruswamiSudan.decodeWithParams] using hmem, hcp_toPoly⟩

/-- Set-membership characterization for the explicit-parameter decoder. -/
theorem mem_decodeWithParams_iff_spec
    (ctx : CompPoly.GuruswamiSudan.GSFilteredCoreContext F)
    (params : CompPoly.GuruswamiSudan.GSExecParams)
    (hparams : GSParamCert k n e params)
    (hrep : RepresentsArkInput w ωs f)
    {p : F[X]} :
    (∃ cp,
      cp ∈ (CompPoly.GuruswamiSudan.decodeWithParams ctx params w).toList ∧
        cp.toPoly = p) ↔
      p ∈ GSSpecSet k e ωs f := by
  simpa [GSSpecSet] using
    (mem_decodeWithParams_iff_degree_and_distance
      (ctx := ctx) (params := params) (hparams := hparams) (hrep := hrep) (p := p))

/-- Set-membership characterization for the selector-backed decoder. -/
theorem mem_decode_iff_spec
    (ctx : CompPoly.GuruswamiSudan.GSFilteredCoreContext F)
    (selector : GSParamSelector)
    (hrep : RepresentsArkInput w ωs f)
    (hjohnson : JohnsonSpecCondition k n e)
    {p : F[X]} :
    (∃ cp,
      cp ∈ (CompPoly.GuruswamiSudan.decode ctx selector.toCompPolySelector k e w).toList ∧
        cp.toPoly = p) ↔
      p ∈ GSSpecSet k e ωs f := by
  constructor
  · intro hp
    unfold CompPoly.GuruswamiSudan.decode at hp
    cases hchoose : selector.toCompPolySelector.choose k w.length e with
    | none =>
        simp [hchoose] at hp
    | some params =>
        have hparamsLen := selector.sound hchoose
        have hlen := length_of_represents hrep
        have hparams : GSParamCert k n e params := by
          simpa [hlen] using hparamsLen
        have hp' :
            ∃ cp,
              cp ∈ (CompPoly.GuruswamiSudan.decodeWithParams ctx params w).toList ∧
                cp.toPoly = p := by
          simpa [hchoose] using hp
        exact (mem_decodeWithParams_iff_spec
          (ctx := ctx) (params := params) (hparams := hparams)
          (hrep := hrep) (p := p)).1 hp'
  · intro hp
    rcases selector.complete hjohnson with ⟨params, hchoose, hparams⟩
    have hlen := length_of_represents hrep
    have hp' := (mem_decodeWithParams_iff_spec
      (ctx := ctx) (params := params) (hparams := hparams)
      (hrep := hrep) (p := p)).2 hp
    simpa [CompPoly.GuruswamiSudan.decode, hlen, hchoose] using hp'

/-- Soundness corollary for the explicit-parameter executable decoder. -/
theorem decodeWithParams_sound
    (ctx : CompPoly.GuruswamiSudan.GSFilteredCoreContext F)
    (params : CompPoly.GuruswamiSudan.GSExecParams)
    (hparams : GSParamCert k n e params)
    (hrep : RepresentsArkInput w ωs f)
    {cp : CompPoly.CPolynomial F}
    (hcp : cp ∈ (CompPoly.GuruswamiSudan.decodeWithParams ctx params w).toList) :
    cp.toPoly.degree < (k : WithBot Nat) ∧
      Δ₀(f, cp.toPoly.eval ∘ ωs) ≤ e :=
  (mem_decodeWithParams_iff_degree_and_distance
    (ctx := ctx) (params := params) (hparams := hparams) (hrep := hrep)
    (p := cp.toPoly)).1 ⟨cp, hcp, rfl⟩

/-- Completeness corollary for the explicit-parameter executable decoder. -/
theorem decodeWithParams_complete
    (ctx : CompPoly.GuruswamiSudan.GSFilteredCoreContext F)
    (params : CompPoly.GuruswamiSudan.GSExecParams)
    (hparams : GSParamCert k n e params)
    (hrep : RepresentsArkInput w ωs f)
    {p : F[X]}
    (hp : p ∈ GSSpecSet k e ωs f) :
    ∃ cp,
      cp ∈ (CompPoly.GuruswamiSudan.decodeWithParams ctx params w).toList ∧
        cp.toPoly = p :=
  (mem_decodeWithParams_iff_spec
    (ctx := ctx) (params := params) (hparams := hparams) (hrep := hrep)
    (p := p)).2 hp

/-- Soundness corollary for the selector-backed executable decoder under selector completeness. -/
theorem decode_sound
    (ctx : CompPoly.GuruswamiSudan.GSFilteredCoreContext F)
    (selector : GSParamSelector)
    (hrep : RepresentsArkInput w ωs f)
    (hjohnson : JohnsonSpecCondition k n e)
    {cp : CompPoly.CPolynomial F}
    (hcp : cp ∈ (CompPoly.GuruswamiSudan.decode ctx selector.toCompPolySelector k e w).toList) :
    cp.toPoly.degree < (k : WithBot Nat) ∧
      Δ₀(f, cp.toPoly.eval ∘ ωs) ≤ e := by
  have hp := (mem_decode_iff_spec
    (ctx := ctx) (selector := selector) (hrep := hrep) (hjohnson := hjohnson)
    (p := cp.toPoly)).1 ⟨cp, hcp, rfl⟩
  simpa [GSSpecSet] using hp

/-- Completeness corollary for the selector-backed executable decoder under
selector completeness. -/
theorem decode_complete
    (ctx : CompPoly.GuruswamiSudan.GSFilteredCoreContext F)
    (selector : GSParamSelector)
    (hrep : RepresentsArkInput w ωs f)
    (hjohnson : JohnsonSpecCondition k n e)
    {p : F[X]}
    (hp : p ∈ GSSpecSet k e ωs f) :
    ∃ cp,
      cp ∈ (CompPoly.GuruswamiSudan.decode ctx selector.toCompPolySelector k e w).toList ∧
        cp.toPoly = p :=
  (mem_decode_iff_spec
    (ctx := ctx) (selector := selector) (hrep := hrep) (hjohnson := hjohnson)
    (p := p)).2 hp

/--
Compatibility with the specification `decoder`, under an explicit degree
hypothesis. The degree hypothesis supplies the bounded-degree premise needed to
compare with the specification decoder.
-/
theorem mem_decodeWithParams_iff_mem_decoder_of_degree_lt
    (ctx : CompPoly.GuruswamiSudan.GSFilteredCoreContext F)
    (params : CompPoly.GuruswamiSudan.GSExecParams)
    (hparams : GSParamCert k n e params)
    (hrep : RepresentsArkInput w ωs f)
    (he : (e : ℝ) < (n : ℝ) - Real.sqrt (((k : ℝ) + 1) * (n : ℝ)))
    {p : F[X]}
    (hdeg : p.natDegree < k) :
    (∃ cp,
      cp ∈ (CompPoly.GuruswamiSudan.decodeWithParams ctx params w).toList ∧
        cp.toPoly = p) ↔
      p ∈ decoder k r D e ωs f := by
  constructor
  · intro hp
    have hspec := (mem_decodeWithParams_iff_degree_and_distance
      (ctx := ctx) (params := params) (hparams := hparams) (hrep := hrep)
      (p := p)).1 hp
    exact mem_decoder_of_dist (n := n) (k := k) (r := r) (D := D) (e := e)
      he hdeg hspec.2
  · intro hp
    have hdist := dist_le_of_mem_decoder (n := n) (k := k) (r := r) (D := D)
      (e := e) he hp
    have hpdegree : p.degree < (k : WithBot Nat) :=
      lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hdeg)
    exact (mem_decodeWithParams_iff_degree_and_distance
      (ctx := ctx) (params := params) (hparams := hparams) (hrep := hrep)
      (p := p)).2 ⟨hpdegree, hdist⟩

/--
Selector-backed compatibility with the specification `decoder`, under an
explicit degree hypothesis. The proof factors through the shared
degree-and-distance specification and the selector completeness condition.
-/
theorem mem_decode_iff_mem_decoder_of_degree_lt
    (ctx : CompPoly.GuruswamiSudan.GSFilteredCoreContext F)
    (selector : GSParamSelector)
    (hrep : RepresentsArkInput w ωs f)
    (he : (e : ℝ) < (n : ℝ) - Real.sqrt (((k : ℝ) + 1) * (n : ℝ)))
    {p : F[X]}
    (hdeg : p.natDegree < k) :
    (∃ cp,
      cp ∈ (CompPoly.GuruswamiSudan.decode ctx selector.toCompPolySelector k e w).toList ∧
        cp.toPoly = p) ↔
      p ∈ decoder k r D e ωs f := by
  have hjohnson : JohnsonSpecCondition k n e := by
    simpa [JohnsonSpecCondition] using he
  constructor
  · intro hp
    have hspec := (mem_decode_iff_spec
      (ctx := ctx) (selector := selector) (hrep := hrep) (hjohnson := hjohnson)
      (p := p)).1 hp
    exact mem_decoder_of_dist (n := n) (k := k) (r := r) (D := D) (e := e)
      he hdeg hspec.2
  · intro hp
    have hdist := dist_le_of_mem_decoder (n := n) (k := k) (r := r) (D := D)
      (e := e) he hp
    have hpdegree : p.degree < (k : WithBot Nat) :=
      lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hdeg)
    exact (mem_decode_iff_spec
      (ctx := ctx) (selector := selector) (hrep := hrep) (hjohnson := hjohnson)
      (p := p)).2 ⟨hpdegree, hdist⟩

end GuruswamiSudan
