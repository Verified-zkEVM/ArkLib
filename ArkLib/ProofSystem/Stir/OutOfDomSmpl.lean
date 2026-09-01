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

/-!
# ArkLib.ProofSystem.Stir.OutOfDomSmpl

Definitions and results for this component of ArkLib.
-/

open Finset Code NNReal Polynomial ProbabilityTheory ReedSolomon
open Probability
namespace OutOfDomSmpl

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [DecidableEq ι]

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

/-- **Single-point collision bound.** For two distinct codewords `u ≠ u'` of `code φ degree`, a
uniformly random out-of-domain point `x ∈ 𝔽 \ φ(ι)` makes their decoded polynomials agree with
probability at most `(degree - 1) / (|𝔽| - |ι|)`: the difference polynomial is nonzero of degree
`< degree`, so it has at most `degree - 1` roots among the `|𝔽| - |ι|` out-of-domain points. -/
lemma single_coord_bound (φ : ι ↪ F) {degree : ℕ} (u u' : code φ degree)
    [Nonempty ↥(domainComplement φ)] (hne : u.val ≠ u'.val) :
    Pr_{ let x ←$ᵖ ↥(domainComplement φ) }[
        (toPolynomial u).eval x.1 = (toPolynomial u').eval x.1 ]
      ≤ ((degree : ENNReal) - 1) / ((Fintype.card F : ENNReal) - Fintype.card ι) := by
  classical
  set p := toPolynomial u - toPolynomial u' with hp_def
  have hp_ne : p ≠ 0 := by
    intro h0
    have heq : toPolynomial u = toPolynomial u' := sub_eq_zero.mp h0
    apply hne
    funext i
    have h1 := toPolynomial_eval_at_domain (c := u) (i := i)
    have h2 := toPolynomial_eval_at_domain (c := u') (i := i)
    rw [heq] at h1
    exact h1.symm.trans h2
  have hp_deg : p.degree < (degree : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt (toPolynomial_lt_deg u) (toPolynomial_lt_deg u'))
  have hnat_lt : p.natDegree < degree := (Polynomial.natDegree_lt_iff_degree_lt hp_ne).mpr hp_deg
  have hdeg_pos : 1 ≤ degree := by omega
  have hnat_le : p.natDegree ≤ degree - 1 := by omega
  have h_filter_le :
      (Finset.univ.filter (fun x : ↥(domainComplement φ) =>
          (toPolynomial u).eval x.1 = (toPolynomial u').eval x.1)).card ≤ degree - 1 := by
    have hmap : (Finset.univ.filter (fun x : ↥(domainComplement φ) =>
          (toPolynomial u).eval x.1 = (toPolynomial u').eval x.1)).card
            ≤ p.roots.toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun x => x.1)
      · intro x hx
        have hx2 : (toPolynomial u).eval x.1 = (toPolynomial u').eval x.1 :=
          (Finset.mem_filter.mp hx).2
        simp only [Finset.mem_coe, Multiset.mem_toFinset]
        rw [Polynomial.mem_roots hp_ne, Polynomial.IsRoot.def, hp_def, Polynomial.eval_sub,
            sub_eq_zero]
        exact hx2
      · intro a _ b _ hab
        exact Subtype.ext hab
    calc _ ≤ p.roots.toFinset.card := hmap
      _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' p
      _ ≤ degree - 1 := hnat_le
  have hcard_cpl : Fintype.card ↥(domainComplement φ) = Fintype.card F - Fintype.card ι := by
    rw [Fintype.card_coe, domainComplement]
    simp only [Function.Embedding.toFun_eq_coe]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Finset.card_image_of_injective _ φ.injective, Finset.card_univ]
  have hb_ne : (Fintype.card F - Fintype.card ι : ℕ) ≠ 0 := by
    have hpos : 0 < Fintype.card ↥(domainComplement φ) := Fintype.card_pos
    rw [hcard_cpl] at hpos; omega
  rw [prob_uniform_eq_card_filter_div_card, hcard_cpl]
  simp only [ENNReal.coe_natCast]
  rw [ENNReal.natCast_sub]
  gcongr
  calc ((Finset.univ.filter (fun x : ↥(domainComplement φ) =>
          (toPolynomial u).eval x.1 = (toPolynomial u').eval x.1)).card : ENNReal)
        ≤ ((degree - 1 : ℕ) : ENNReal) := by exact_mod_cast h_filter_le
    _ = (degree : ENNReal) - 1 := by rw [ENNReal.natCast_sub, Nat.cast_one]

/-- **Per-pair collision bound.** Extending `single_coord_bound` over `s` independent out-of-domain
samples: two distinct codewords agree on *all* `s` points with probability at most
`((degree - 1) / (|𝔽| - |ι|)) ^ s`. -/
lemma pair_agree_bound (φ : ι ↪ F) {degree s : ℕ} (u u' : code φ degree)
    [Nonempty ↥(domainComplement φ)] (hne : u.val ≠ u'.val) :
    Pr_{ let r ←$ᵖ (Fin s → ↥(domainComplement φ)) }[
        ∀ i, (toPolynomial u).eval (r i).1 = (toPolynomial u').eval (r i).1 ]
      ≤ (((degree : ENNReal) - 1) / ((Fintype.card F : ENNReal) - Fintype.card ι)) ^ s := by
  classical
  -- The agreement event is membership in a fixed finset of out-of-domain points, so the `s`
  -- samples are handled by the generic uniform-product bound.
  have hsingle := single_coord_bound φ u u' hne
  rw [prob_uniform_eq_card_filter_div_card] at hsingle
  calc Pr_{ let r ←$ᵖ (Fin s → ↥(domainComplement φ)) }[
          ∀ i, (toPolynomial u).eval (r i).1 = (toPolynomial u').eval (r i).1 ]
      = Pr_{ let r ←$ᵖ (Fin s → ↥(domainComplement φ)) }[
          ∀ i, r i ∈ Finset.univ.filter (fun x : ↥(domainComplement φ) =>
            (toPolynomial u).eval x.1 = (toPolynomial u').eval x.1) ] :=
        Pr_congr (fun r => by simp)
    _ = _ := prob_uniform_pi_mem_finset_eq _ s
    _ ≤ _ := pow_le_pow_left' hsingle s

/-- **Out-of-domain sampling, first inequality** — the first of the two displayed bounds of
Lemma 4.5 of [ACFY24stir].

The paper states a single Lemma 4.5 with two displayed inequalities; ArkLib splits it into
`out_of_dom_smpl_1` and `out_of_dom_smpl_2`, so the suffixes `_1`/`_2` are this repository's
numbering rather than the paper's. -/
lemma out_of_dom_smpl_1
    {δ l : ℝ≥0} {s : ℕ} {f : ι → F} {degree : ℕ} {φ : ι ↪ F}
  (C : Set (ι → F)) (hC : C = code φ degree)
  (h_decodable : IsListDecodable C δ l)
  (h_nonempty : Nonempty (domainComplement φ)) :
  listDecodingCollisionProbability φ f δ s degree h_nonempty ≤
    ((l * (l-1) / 2)) * ((degree - 1) / (Fintype.card F - Fintype.card ι))^s := by
  classical
  have : Nonempty ↥(domainComplement φ) := h_nonempty
  have : Fintype ↥(code φ degree) := Fintype.ofFinite _
  subst hC
  set X : ENNReal :=
    ((degree : ENNReal) - 1) / ((Fintype.card F : ENNReal) - Fintype.card ι) with hX
  set ball : Finset ↥(code φ degree) :=
    Finset.univ.filter (fun u => u.val ∈ closeCodewordsRel (code φ degree) f δ) with hball
  set T : Finset (Finset ↥(code φ degree)) := ball.powersetCard 2 with hT
  set PT : Finset ↥(code φ degree) → (Fin s → ↥(domainComplement φ)) → Prop :=
    fun t r => ∃ a b : code φ degree, t = {a, b} ∧ a.val ≠ b.val ∧
      ∀ i, (toPolynomial a).eval (r i).1 = (toPolynomial b).eval (r i).1 with hPT
  unfold listDecodingCollisionProbability
  -- Every collision witness `(u, u')` yields the two-element subset `{u, u'} ⊆ ball`.
  refine le_trans (Pr_le_Pr_of_implies _ _ (fun r => ∃ t : ↥T, PT t.1 r) ?himpl) ?_
  case himpl =>
    rintro r ⟨u, u', hne, hu, hu', hagree⟩
    have hu_ball : u ∈ ball := by
      rw [hball]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
    have hu'_ball : u' ∈ ball := by
      rw [hball]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu'⟩
    have huu' : u ≠ u' := fun h => hne (by rw [h])
    have htmem : ({u, u'} : Finset ↥(code φ degree)) ∈ T := by
      rw [hT, Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · rw [Finset.card_pair huu']
    exact ⟨⟨{u, u'}, htmem⟩, u, u', rfl, hne, hagree⟩
  -- Union bound over the two-element subsets, then bound each term and count the subsets.
  refine le_trans (Pr_exists_le _ (fun t : ↥T => PT t.1)) ?_
  have hterm : ∀ t : ↥T,
      Pr_{ let r ←$ᵖ (Fin s → ↥(domainComplement φ)) }[ PT t.1 r ] ≤ X ^ s := by
    intro t
    obtain ⟨htsub, htcard⟩ := Finset.mem_powersetCard.mp t.2
    obtain ⟨a, b, hab, htab⟩ := Finset.card_eq_two.mp htcard
    have hne_ab : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    refine le_trans (Pr_le_Pr_of_implies _ _
      (fun r => ∀ i, (toPolynomial a).eval (r i).1 = (toPolynomial b).eval (r i).1) ?_)
      (hX ▸ pair_agree_bound φ a b hne_ab)
    rintro r ⟨a', b', heq', hne', hagree'⟩
    have heq : ({a, b} : Finset ↥(code φ degree)) = {a', b'} := htab ▸ heq'
    have ha' : a' ∈ ({a, b} : Finset ↥(code φ degree)) := by
      rw [heq]; exact Finset.mem_insert_self _ _
    have hb' : b' ∈ ({a, b} : Finset ↥(code φ degree)) := by
      rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
    rcases ha' with rfl | rfl
    · rcases hb' with rfl | rfl
      · exact absurd rfl hne'
      · exact hagree'
    · rcases hb' with rfl | rfl
      · exact fun i => (hagree' i).symm
      · exact absurd rfl hne'
  refine le_trans (Finset.sum_le_sum (fun t _ => hterm t)) ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe]
  -- The number of two-element subsets of the `δ`-ball is `binom(k, 2) ≤ l(l-1)/2`.
  have hcard_le : (T.card : ENNReal) ≤ (l : ENNReal) * ((l : ENNReal) - 1) / 2 := by
    -- The list-size bound comes straight from the list-decodability API; the only bridging
    -- needed is that `ball` is subtype-valued, so it is pushed through `Subtype.val`.
    have hr : (ball.card : ℝ) ≤ (l : ℝ) := by
      rw [← Finset.card_image_of_injective ball Subtype.val_injective]
      refine h_decodable.finset_card_le f _ ?_
      intro c hc
      simp only [Finset.mem_image] at hc
      obtain ⟨u, hu, rfl⟩ := hc
      exact (Finset.mem_filter.mp hu).2
    have hkl : (ball.card : ENNReal) ≤ (l : ENNReal) := by
      have hnn : (ball.card : ℝ≥0) ≤ l := by exact_mod_cast hr
      calc (ball.card : ENNReal) = ((ball.card : ℝ≥0) : ENNReal) := by rw [ENNReal.coe_natCast]
        _ ≤ (l : ENNReal) := by exact_mod_cast hnn
    have hdvd : 2 ∣ ball.card * (ball.card - 1) := by
      rcases Nat.even_or_odd ball.card with he | ho
      · exact Dvd.dvd.mul_right he.two_dvd _
      · exact Dvd.dvd.mul_left (Nat.Odd.sub_odd ho (by norm_num)).two_dvd _
    have h2T : 2 * T.card = ball.card * (ball.card - 1) := by
      rw [hT, Finset.card_powersetCard, Nat.choose_two_right, Nat.mul_div_cancel' hdvd]
    have hTeq : (T.card : ENNReal) = (ball.card : ENNReal) * ((ball.card : ENNReal) - 1) / 2 := by
      rw [ENNReal.eq_div_iff (by norm_num) (by norm_num), mul_comm]
      calc (T.card : ENNReal) * 2 = ((2 * T.card : ℕ) : ENNReal) := by push_cast; ring
        _ = ((ball.card * (ball.card - 1) : ℕ) : ENNReal) := by rw [h2T]
        _ = (ball.card : ENNReal) * ((ball.card : ENNReal) - 1) := by
              rw [Nat.cast_mul, ENNReal.natCast_sub, Nat.cast_one]
    rw [hTeq]
    gcongr
  gcongr

/-- **Out-of-domain sampling, second inequality** — the second of the two displayed bounds of
Lemma 4.5 of [ACFY24stir], weakening `out_of_dom_smpl_1` to the `l² / 2` shape used downstream.

As for `out_of_dom_smpl_1`, the `_2` suffix is ArkLib's split of the paper's single Lemma 4.5. -/
lemma out_of_dom_smpl_2
    {δ l : ℝ≥0} {s : ℕ} {f : ι → F} {degree : ℕ} {φ : ι ↪ F}
  (C : Set (ι → F)) (hC : C = code φ degree)
  (h_decodable : IsListDecodable C δ l)
  (h_nonempty : Nonempty (domainComplement φ)) :
  listDecodingCollisionProbability φ f δ s degree h_nonempty ≤
    ((l^2 / 2)) * (degree / (Fintype.card F - Fintype.card ι))^s := by
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

end OutOfDomSmpl
