/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.Probability.Instances
import ArkLib.Data.Probability.Notation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Sym.Card

open Finset ListDecodable NNReal Polynomial ProbabilityTheory ReedSolomon
namespace OutOfDomSmpl

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [DecidableEq ι]

private lemma prob_exists_le_sum
    {α β : Type} [Fintype β] (D : PMF α) (P : β → α → Prop) :
    Pr_{let x ← D}[∃ b, P b x] ≤ ∑ b, Pr_{let x ← D}[P b x] := by
  classical
  rw [prob_tsum_form_singleton]
  simp_rw [prob_tsum_form_singleton]
  rw [← Summable.tsum_finsetSum (s := Finset.univ) (fun _ _ ↦ ENNReal.summable)]
  apply ENNReal.tsum_le_tsum
  intro x
  rw [← Finset.mul_sum]
  apply mul_le_mul_right
  by_cases h : ∃ b, P b x
  · simp only [h, if_true]
    obtain ⟨b, hb⟩ := h
    calc
      1 = if P b x then 1 else 0 := by simp [hb]
      _ ≤ ∑ b, if P b x then (1 : ENNReal) else 0 :=
        Finset.single_le_sum
          (s := Finset.univ) (f := fun b ↦ if P b x then (1 : ENNReal) else 0)
          (fun _ _ ↦ zero_le) (Finset.mem_univ b)
  · simp [h]

private lemma prob_uniform_fin_forall
    {A : Type} [Fintype A] [Nonempty A] (Q : A → Prop) [DecidablePred Q] (s : ℕ) :
    Pr_{let r ←$ᵖ (Fin s → A)}[∀ i, Q (r i)] =
      (((Finset.univ.filter Q).card : ENNReal) / Fintype.card A) ^ s := by
  classical
  rw [prob_uniform_eq_card_filter_div_card]
  have hfilter :
      (Finset.univ.filter (fun r : Fin s → A ↦ ∀ i, Q (r i))).card =
        (Finset.univ.filter Q).card ^ s := by
    rw [← Fintype.card_piFinset_const (Finset.univ.filter Q) s]
    congr 1
    ext r
    simp
  rw [hfilter, Fintype.card_pi_const]
  push_cast
  simp only [ENNReal.div_eq_inv_mul, ENNReal.inv_pow, mul_pow]

omit [Fintype F] in
private lemma card_eval_eq_le
    {degree : ℕ} (p q : Polynomial.degreeLT F degree) (hpq : p ≠ q) (S : Finset F) :
    (S.filter (fun x ↦ (p : F[X]).eval x = (q : F[X]).eval x)).card ≤ degree - 1 := by
  classical
  let d : F[X] := p - q
  have hd : d ≠ 0 := sub_ne_zero.mpr (Subtype.val_injective.ne hpq)
  have hd_degree : d.natDegree < degree := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hd]
    exact Polynomial.mem_degreeLT.mp (Submodule.sub_mem _ p.property q.property)
  calc
    (S.filter (fun x ↦ (p : F[X]).eval x = (q : F[X]).eval x)).card
        ≤ d.roots.toFinset.card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter] at hx
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hd, Polynomial.IsRoot.def]
          simpa [d, Polynomial.eval_sub, sub_eq_zero] using hx.2
    _ ≤ d.natDegree := by
      exact (Multiset.toFinset_card_le d.roots).trans (Polynomial.card_roots' d)
    _ ≤ degree - 1 := by omega

private lemma coe_choose_two_nnreal (n : ℕ) :
    (n.choose 2 : NNReal) = (n : NNReal) * ((n - 1 : ℕ) : NNReal) / 2 := by
  rw [Nat.choose_two_right,
    Nat.cast_div n.even_mul_pred_self.two_dvd (by norm_num)]
  norm_cast

/-! Section 4.3 [ACFY24stir]

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing with
    fewer queries*][ACFY24stir]
-/

/-- Returns the domain complement `F \ φ(ι)` of an injective map `φ : ι ↪ F` -/
def domainComplement (φ : ι ↪ F) : Finset F :=
  Finset.univ \ Finset.image φ.toFun Finset.univ

/-- Pr_{r₀, …, r_{s-1} ← (𝔽 \ φ(ι)) }
      [ ∃ distinct u, u′ ∈ List(C, f, δ) :
        ∀ i < s, u(r_i) = u′(r_i) ]
    here, List (C, f, δ) denotes the list of codewords of C δ-close to f,
    wrt the Relative Hamming distance. -/
noncomputable def listDecodingCollisionProbability
  (φ : ι ↪ F) (f : ι → F) (δ : ℝ) (s degree : ℕ)
  (h_nonempty : Nonempty (domainComplement φ)) : ENNReal :=
  Pr_{let r ←$ᵖ (Fin s → domainComplement φ)}[ ∃ (u u' : code φ degree),
                                    u.val ≠ u'.val ∧
                                    u.val ∈ closeCodewordsRel (code φ degree) f δ ∧
                                    u'.val ∈ closeCodewordsRel (code φ degree) f δ ∧
                                    ∀ i : Fin s,
                                    let uPoly := toPolynomialLT u
                                    let uPoly' := toPolynomialLT u'
                                    (uPoly : F[X]).eval (r i).1
                                      = (uPoly' : F[X]).eval (r i).1
                                    ]

set_option maxHeartbeats 1000000 in
-- The finite union and root-counting proof needs more elaboration budget than the project default.
/-- Lemma 4.5.1 -/
lemma out_of_dom_smpl_1
  {δ l : ℝ≥0} {s : ℕ} {f : ι → F} {degree : ℕ} {φ : ι ↪ F}
  (C : Set (ι → F)) (hC : C = code φ degree)
  (h_decodable : listDecodable C δ l)
  (h_nonempty : Nonempty (domainComplement φ)) :
  listDecodingCollisionProbability φ f δ s degree h_nonempty ≤
    ((l * (l-1) / 2)) * ((degree - 1) / (Fintype.card F - Fintype.card ι))^s
  := by
  classical
  subst C
  let L := {u : code φ degree //
    u.val ∈ closeCodewordsRel (code φ degree) f δ}
  let Pair := {z : Sym2 L // ¬z.IsDiag}
  let collision : Pair → (Fin s → domainComplement φ) → Prop := fun z r ↦
    Sym2.lift ⟨fun u v ↦
      ∀ i : Fin s, (toPolynomialLT u.val : F[X]).eval (r i).1 =
        (toPolynomialLT v.val : F[X]).eval (r i).1,
      fun u v ↦ propext <| by
        constructor <;> intro h i <;> exact (h i).symm⟩ z.val
  have hevent (r : Fin s → domainComplement φ) :
      (∃ (u u' : code φ degree),
        u.val ≠ u'.val ∧
        u.val ∈ closeCodewordsRel (code φ degree) f δ ∧
        u'.val ∈ closeCodewordsRel (code φ degree) f δ ∧
        ∀ i : Fin s,
          (toPolynomialLT u : F[X]).eval (r i).1 =
            (toPolynomialLT u' : F[X]).eval (r i).1) ↔
      ∃ z : Pair, collision z r := by
    constructor
    · rintro ⟨u, v, huv, hu, hv, hcollision⟩
      let uL : L := ⟨u, hu⟩
      let vL : L := ⟨v, hv⟩
      have huvL : uL ≠ vL := by
        intro h
        exact huv (congrArg (fun w : L ↦ w.val.val) h)
      refine ⟨⟨s(uL, vL), ?_⟩, ?_⟩
      · simpa [Sym2.mk_isDiag_iff] using huvL
      · exact hcollision
    · rintro ⟨⟨z, hz⟩, hcollision⟩
      induction z using Sym2.ind with
      | _ u v =>
          have huvL : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using hz
          refine ⟨u.val, v.val, ?_, u.property, v.property, ?_⟩
          · intro h
            exact huvL (Subtype.ext (Subtype.ext h))
          · exact hcollision
  unfold listDecodingCollisionProbability
  rw [Pr_congr hevent]
  have hcard_domain :
      Fintype.card (domainComplement φ) = Fintype.card F - Fintype.card ι := by
    rw [Fintype.card_coe]
    rw [domainComplement, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ]
    congr 1
    exact Finset.card_image_of_injective _ φ.injective
  have hcollision (z : Pair) :
      Pr_{let r ←$ᵖ (Fin s → domainComplement φ)}[collision z r] ≤
        ((degree - 1 : ℕ) / (Fintype.card F - Fintype.card ι : ℕ) : ENNReal) ^ s := by
    rcases z with ⟨z, hz⟩
    induction z using Sym2.ind with
    | _ u v =>
        have hne : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using hz
        have hpoly : toPolynomialLT u.val ≠ toPolynomialLT v.val := by
          intro hp
          apply hne
          apply Subtype.ext
          apply Subtype.ext
          funext i
          have heval := congrArg
            (fun q : Polynomial.degreeLT F degree ↦ (q : F[X]).eval (φ i)) hp
          simpa [toPolynomialLT, toPolynomial_eval_at_domain] using heval
        change Pr_{let r ←$ᵖ (Fin s → domainComplement φ)}[∀ i,
          (toPolynomialLT u.val : F[X]).eval (r i).1 =
            (toPolynomialLT v.val : F[X]).eval (r i).1] ≤ _
        rw [prob_uniform_fin_forall
          (fun x : domainComplement φ ↦
            (toPolynomialLT u.val : F[X]).eval x.1 =
              (toPolynomialLT v.val : F[X]).eval x.1) s]
        have hnum :
            (Finset.univ.filter (fun x : domainComplement φ ↦
              (toPolynomialLT u.val : F[X]).eval x.1 =
                (toPolynomialLT v.val : F[X]).eval x.1)).card ≤ degree - 1 := by
          rw [show (Finset.univ : Finset (domainComplement φ)) =
            (domainComplement φ).attach by rfl]
          rw [Finset.filter_attach
            (fun x : F ↦ (toPolynomialLT u.val : F[X]).eval x =
              (toPolynomialLT v.val : F[X]).eval x) (domainComplement φ),
            Finset.card_map, Finset.card_attach]
          exact card_eval_eq_le (toPolynomialLT u.val) (toPolynomialLT v.val)
            hpoly (domainComplement φ)
        rw [hcard_domain]
        gcongr
  have hL_real : (Fintype.card L : ℝ) ≤ l := by
    let e : L ≃ {w : ι → F // w ∈ closeCodewordsRel (code φ degree) f δ} := {
      toFun u := ⟨u.val.val, u.property⟩
      invFun w := ⟨⟨w.val, w.property.1⟩, w.property⟩
      left_inv u := by ext; rfl
      right_inv w := by ext; rfl
    }
    rw [Fintype.card_congr e, Set.fintypeCard_eq_ncard]
    exact h_decodable f
  have hL : (Fintype.card L : NNReal) ≤ l := by
    exact_mod_cast hL_real
  have hL_sub : ((Fintype.card L - 1 : ℕ) : NNReal) ≤ l - 1 := by
    cases hcard : Fintype.card L with
    | zero => simp
    | succ n =>
        rw [hcard] at hL
        simpa [Nat.cast_succ] using
          tsub_le_tsub_right hL (1 : NNReal)
  have hpair_nnreal :
      (Fintype.card Pair : NNReal) ≤ l * (l - 1) / 2 := by
    rw [show Fintype.card Pair = (Fintype.card L).choose 2 from
      Sym2.card_subtype_not_diag]
    rw [coe_choose_two_nnreal]
    gcongr
  have hpair :
      (Fintype.card Pair : ENNReal) ≤ (l : ENNReal) * ((l : ENNReal) - 1) / 2 := by
    exact_mod_cast hpair_nnreal
  have hfinal :
      Pr_{let r ←$ᵖ (Fin s → domainComplement φ)}[∃ z : Pair, collision z r] ≤
        ((l : ENNReal) * ((l : ENNReal) - 1) / 2) *
          (((degree - 1 : ℕ) : ENNReal) /
            ((Fintype.card F - Fintype.card ι : ℕ) : ENNReal)) ^ s := by
    calc
      Pr_{let r ←$ᵖ (Fin s → domainComplement φ)}[∃ z : Pair, collision z r]
          ≤ ∑ z : Pair,
            Pr_{let r ←$ᵖ (Fin s → domainComplement φ)}[collision z r] :=
        prob_exists_le_sum _ _
      _ ≤ ∑ _z : Pair,
          ((degree - 1 : ℕ) / (Fintype.card F - Fintype.card ι : ℕ) : ENNReal) ^ s := by
        exact Finset.sum_le_sum fun z _ ↦ hcollision z
      _ = (Fintype.card Pair : ENNReal) *
          ((degree - 1 : ℕ) / (Fintype.card F - Fintype.card ι : ℕ) : ENNReal) ^ s := by
        simp
      _ ≤ ((l : ENNReal) * ((l : ENNReal) - 1) / 2) *
          ((degree - 1 : ℕ) / (Fintype.card F - Fintype.card ι : ℕ) : ENNReal) ^ s :=
        mul_le_mul_left hpair _
  simpa only [ENNReal.natCast_sub, Nat.cast_one] using hfinal

/-- Lemma 4.5.2 -/
lemma out_of_dom_smpl_2
  {δ l : ℝ≥0} {s : ℕ} {f : ι → F} {degree : ℕ} {φ : ι ↪ F}
  (C : Set (ι → F)) (hC : C = code φ degree)
  (h_decodable : listDecodable C δ l)
  (h_nonempty : Nonempty (domainComplement φ)) :
  listDecodingCollisionProbability φ f δ s degree h_nonempty ≤
    ((l^2 / 2)) * (degree / (Fintype.card F - Fintype.card ι))^s
  := by
    transitivity
    · exact out_of_dom_smpl_1 C hC h_decodable h_nonempty
    · apply mul_le_mul'
      · apply ENNReal.div_le_div_right
        rw [pow_two]
        apply mul_le_mul' (by rfl)
        exact tsub_le_self
      · apply pow_le_pow_left'
        apply ENNReal.div_le_div_right
        exact tsub_le_self

set_option maxHeartbeats 1000000 in
-- This packages the theorem's full polymorphic interface for lightweight downstream consumers.
/-- Consumer-facing proposition corresponding exactly to STIR Lemma 4.5.2. -/
def outOfDomainSamplingBound : Prop :=
  ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {δ l : ℝ≥0} {s : ℕ} {f : ι → F} {degree : ℕ} {φ : ι ↪ F}
    (C : Set (ι → F)) (_hC : C = code φ degree)
    (_h_decodable : listDecodable C δ l)
    (h_nonempty : Nonempty (domainComplement φ)),
    listDecodingCollisionProbability φ f δ s degree h_nonempty ≤
      ((l ^ 2 / 2)) * (degree / (Fintype.card F - Fintype.card ι)) ^ s

set_option maxHeartbeats 5000000 in
-- Unfolding the packaged proposition requires a larger one-time elaboration budget.
/-- Kernel-checked bridge from `out_of_dom_smpl_2` to its compact consumer interface. -/
lemma out_of_dom_smpl_2_statement : outOfDomainSamplingBound := by
  simpa only [outOfDomainSamplingBound] using @out_of_dom_smpl_2

end OutOfDomSmpl
