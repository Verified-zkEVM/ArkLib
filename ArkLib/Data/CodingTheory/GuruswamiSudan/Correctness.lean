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
  simpa using (List.nodup_ofFn.2 ωs.injective)

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
      hparams.interpolation_witness_exists w.points hpoints_size
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
