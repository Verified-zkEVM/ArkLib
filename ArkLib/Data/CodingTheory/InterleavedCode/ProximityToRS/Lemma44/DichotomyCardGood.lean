/-
Dichotomy (cardinality form) for RS proximity along an affine line.
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Aux
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Lemma44.AffineParamOnG
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Lemma44.CardScalarsSmallWeightBound
import Mathlib.Tactic

noncomputable section

open Code

namespace ProximityToRS

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {deg : ℕ} {α : ι ↪ F} {e : ℕ}

-- Algebraic helper: distribute subtraction over an affine combination.
omit [DecidableEq F] [Fintype F] [Fintype ι] [DecidableEq ι] in
lemma sub_affine_distrib
  (u v c d : ι → F) (a : F) :
  (u + a • v) - (c + a • d) = (u - c) + a • (v - d) := by
  funext i
  simp [Pi.smul_apply, smul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

omit [Fintype F] in
/-- Case 1 (Appendix A): if `|supp(u) ∪ supp(v)| ≤ e`, then every point on the line is within
distance ≤ e from the code (since 0 ∈ L). -/
lemma all_points_close_when_union_support_le_e
  (L : LinearCode ι F) (u v : ι → F) {e : ℕ}
  (h_union : ((Finset.univ.filter fun i : ι => u i ≠ 0) ∪
              (Finset.univ.filter fun i : ι => v i ≠ 0)).card ≤ e) :
  ∀ a : F, distFromCode (u + a • v) (L : Set (ι → F)) ≤ e := by
  classical
  intro a
  let Su : Finset ι := Finset.univ.filter (fun i : ι => u i ≠ 0)
  let Sv : Finset ι := Finset.univ.filter (fun i : ι => v i ≠ 0)
  let Ssum : Finset ι := Finset.univ.filter (fun i : ι => u i + a * v i ≠ 0)
  have hsubset : Ssum ⊆ Su ∪ Sv := by
    intro i hi
    have hne : u i + a * v i ≠ 0 := (Finset.mem_filter.mp hi).2
    by_cases hu0 : u i = 0
    · have hv0 : v i ≠ 0 := by
        intro hv_eq; have : u i + a * v i = 0 := by simp [hu0, hv_eq]
        exact hne this
      have : i ∈ Sv := by simp [Sv, hv0]
      exact Finset.mem_union.mpr (Or.inr this)
    · have : i ∈ Su := by simp [Su, hu0]
      exact Finset.mem_union.mpr (Or.inl this)
  have hwt_le : Code.wt (u + a • v) ≤ (Su ∪ Sv).card := by
    have : Code.wt (u + a • v) = Ssum.card := by
      simp [Code.wt, Ssum, smul_eq_mul, Pi.smul_apply]
    have : Ssum.card ≤ (Su ∪ Sv).card := Finset.card_mono hsubset
    simp [Ssum] at this
    simpa [Code.wt, Ssum, smul_eq_mul, Pi.smul_apply] using this
  have hwt_le_e : Code.wt (u + a • v) ≤ e := le_trans hwt_le h_union
  have h0mem : (0 : ι → F) ∈ (L : Set (ι → F)) := by exact (Submodule.zero_mem L)
  have hham_le_nat : hammingDist (u + a • v) (0 : ι → F) ≤ e := by
    simpa [LinearCode.hammingDist_eq_wt_sub] using hwt_le_e
  have hmem : (e : ℕ∞) ∈ {d : ℕ∞ | ∃ z ∈ (L : Set (ι → F)), hammingDist (u + a • v) z ≤ d} := by
    refine ⟨0, h0mem, ?_⟩
    simpa using (by exact_mod_cast hham_le_nat : (hammingDist (u + a • v) (0 : ι → F) : ℕ∞) ≤ e)
  have hsInf_le := sInf_le hmem
  simpa [Code.distFromCode] using hsInf_le

/-- Far branch core (Appendix A): under `3*e < minDist(RS)`, along the line `u + a•v`,
either all scalars are good (every point is within `e` of `RS`) or the good scalars are
bounded by `minDist(RS)`. This is the RS‑specific “either all or ≤ d” statement.

Blueprint proof: unique witnesses within `e`, triple‑scalar identity forcing affine centers,
double counting to bound the bad coordinate set by `≤ e`, then globalize to all scalars. -/
private lemma far_branch_either_all_or_bound
  (RS : LinearCode ι F) {e : ℕ}
  (he : 3 * e < Code.minDist (RS : Set (ι → F)))
  (u v : ι → F) :
  (∀ a : F, distFromCode (u + a • v) (RS : Set (ι → F)) ≤ e)
  ∨ (Nat.card {a : F // distFromCode (u + a • v) (RS : Set (ι → F)) ≤ e}
        ≤ Code.minDist (RS : Set (ι → F))) := by
  classical
  -- Let G be the set of good scalars: those with distance ≤ e to RS.
  let fFintype : Fintype F := Fintype.ofFinite F
  let G : Finset F :=
    Finset.univ.filter (fun a : F => distFromCode (u + a • v) (RS : Set (ι → F)) ≤ e)
  -- If all scalars are good, we are done.
  by_cases hall : (∀ a : F, distFromCode (u + a • v) (RS : Set (ι → F)) ≤ e)
  · exact Or.inl hall
  -- Otherwise, we will bound the number of good scalars by minDist(RS),
  -- unless we can still conclude that all scalars are good after re-centering.
  -- If |G| ≤ 1, the bound is trivial since minDist ≥ 1 (from 3e < minDist).
  by_cases hLe1 : G.card ≤ 1
  · have hminpos : 1 ≤ Code.minDist (RS : Set (ι → F)) := by
      have : 0 < Code.minDist (RS : Set (ι → F)) := lt_of_le_of_lt (Nat.zero_le _) he
      exact Nat.succ_le_of_lt this
    -- Convert between the subtype cardinality and the filtered finset cardinality
    have hcard_eq :
        Nat.card {a : F // distFromCode (u + a • v) (RS : Set (ι → F)) ≤ e} = G.card := by
      classical
      -- standard equivalence between subtype over a decidable predicate and a filtered finset
      simpa [G] using Fintype.card_subtype
        (fun a : F => distFromCode (u + a • v) (RS : Set (ι → F)) ≤ e)
    have : Nat.card {a : F // distFromCode (u + a • v) (RS : Set (ι → F)) ≤ e} ≤ 1 := by
      rwa [hcard_eq]
    exact Or.inr (le_trans this hminpos)
  -- Now assume |G| ≥ 2. Pick two distinct good scalars a0, a1 in G.
  · -- There exist two distinct good scalars in G since ¬ (G.card ≤ 1).
    classical
    have h1lt : 1 < G.card := Nat.lt_of_not_ge hLe1
    -- Pick any element a0 ∈ G (nonempty since card > 0)
    have hpos : 0 < G.card := lt_trans (by decide) h1lt
    obtain ⟨a0, ha0G⟩ := Finset.card_pos.mp hpos
    -- From 1 < card, there exists a1 ∈ G with a1 ≠ a0
    have hex := Finset.exists_ne_of_one_lt_card (s := G) h1lt
    rcases hex a0 with ⟨a1, ha1G, hneq⟩
    -- For each a ∈ G, pick a witness codeword within distance ≤ e
    have hGdef : ∀ {a : F}, a ∈ G → distFromCode (u + a • v) (RS : Set (ι → F)) ≤ e := by
      intro a ha
      have : a ∈ Finset.univ.filter
        (fun a : F => distFromCode (u + a • v) (RS : Set (ι → F)) ≤ e) := ha
      simpa [G] using (Finset.mem_filter.mp this).2
    -- Package G as a subtype and choose witnesses
    let Gsub := {a : F // a ∈ G}
    -- For each a ∈ G, pick f a ∈ RS with Δ(u + a•v, f a) ≤ e
    choose f hf_mem hf_close using
      (fun (a : Gsub) =>
        ProximityToRS.exists_codeword_close_of_dist_le
          (u := u + a.1 • v) (C := (RS : Set (ι → F))) (e := e) (h := hGdef a.property))
    -- Apply the affine parametrization on G using the triple-combo zero identity
    have he3 : 3 * e < Code.minDist (RS : Set (ι → F)) := he
    -- Build the finset structure for G and provide two distinct anchors
    have ha0G' : a0 ∈ G := ha0G
    have ha1G' : a1 ∈ G := ha1G
    -- Prepare inputs for `affine_param_on_G`
    have hfRS : ∀ a : Gsub, f a ∈ (RS : Set (ι → F)) := fun a => (hf_mem a)
    have hfclose : ∀ a : Gsub, Δ₀(u + a.1 • v, f a) ≤ e := fun a => (hf_close a)
    -- Convert a0, a1 to subtype elements of G
    have ha0_sub : Gsub := ⟨a0, ha0G⟩
    have ha1_sub : Gsub := ⟨a1, ha1G⟩
    -- Run the affine parametrization
    obtain ⟨cstar, dstar, hc_in, hd_in, hfa_affine⟩ :=
      ProximityToRS.affine_param_on_G (RS := RS) (u := u) (v := v)
        (G := G) (a0 := a0) (a1 := a1) (ha0 := ha0G) (ha1 := ha1G) (hneq := hneq.symm)
        (he3 := he3) (f := f) (hfRS := hfRS) (hfclose := hfclose)
    -- Define shifted parameters u' and v'
    let u' : ι → F := u - cstar
    let v' : ι → F := v - dstar
    -- If the union support of u' and v' is small, then all scalars are good.
    let Su' : Finset ι := Finset.univ.filter fun i : ι => u' i ≠ 0
    let Sv' : Finset ι := Finset.univ.filter fun i : ι => v' i ≠ 0
    by_cases h_small : (Su' ∪ Sv').card ≤ e
    · -- Conclude all scalars are good using the general case-1 lemma on u', v', then translate.
      have hall' : ∀ a : F, distFromCode (u' + a • v') (RS : Set (ι → F)) ≤ e :=
        all_points_close_when_union_support_le_e (L := RS) (u := u') (v := v') h_small
      -- Show c* + a•d* ∈ RS for every a
      have hcode : ∀ a : F, (cstar + a • dstar) ∈ (RS : Set (ι → F)) := by
        intro a
        have hc' : cstar ∈ (RS : Submodule F (ι → F)) := by simpa using hc_in
        have hd' : dstar ∈ (RS : Submodule F (ι → F)) := by simpa using hd_in
        have : cstar + a • dstar ∈ (RS : Submodule F (ι → F)) :=
          Submodule.add_mem RS hc' (Submodule.smul_mem RS a hd')
        simpa using this
      -- Use translation invariance: Δ₀((u' + a•v') + (c* + a•d*), RS) = Δ₀(u' + a•v', RS)
      have hall_all : ∀ a : F, distFromCode (u + a • v) (RS : Set (ι → F)) ≤ e := by
        intro a
        have hdist_eq :=
          Code.distFromCode_add_codeword_eq (LC := RS) (w := u' + a • v')
            (c := cstar + a • dstar) (hc := hcode a)
        have hsum : (u' + a • v') + (cstar + a • dstar) = u + a • v := by
          simp [u', v', sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add]
        have hEq : distFromCode (u + a • v) (RS : Set (ι → F))
                  = distFromCode (u' + a • v') (RS : Set (ι → F)) := by
          -- Prefer `simp` rewriting over `simpa` for lint
          have := hdist_eq
          simp [hsum] at this
          exact this
        have hbound : distFromCode (u' + a • v') (RS : Set (ι → F)) ≤ e := hall' a
        simpa [hEq] using hbound
      exact Or.inl hall_all
    -- Large union support for u', v'. Use the affine witnesses to bound |G|.
    -- First, bound wt(v') by the sum of residual weights at two good scalars.
    have ha0_good : distFromCode (u + a0 • v) (RS : Set (ι → F)) ≤ e := hGdef ha0G
    have ha1_good : distFromCode (u + a1 • v) (RS : Set (ι → F)) ≤ e := hGdef ha1G
    have ha0_sub' : Gsub := ⟨a0, ha0G⟩
    have ha1_sub' : Gsub := ⟨a1, ha1G⟩
    have rwt_a0 : Code.wt (u' + a0 • v') ≤ e := by
      -- residual r(a0) equals u' + a0•v'
      have hdist : hammingDist (u + a0 • v) (f ⟨a0, ha0G⟩) ≤ e := by
        simpa using hfclose ⟨a0, ha0G⟩
      have hdist' : Code.wt ((u + a0 • v) - (f ⟨a0, ha0G⟩)) ≤ e := by
        simpa [LinearCode.hammingDist_eq_wt_sub] using hdist
      have hres : (u + a0 • v) - (cstar + a0 • dstar) = u' + a0 • v' := by
        simpa [u', v'] using ProximityToRS.sub_affine_distrib (u) (v) (cstar) (dstar) a0
      simpa [hfa_affine ⟨a0, ha0G⟩, hres] using hdist'
    have rwt_a1 : Code.wt (u' + a1 • v') ≤ e := by
      have hdist : hammingDist (u + a1 • v) (f ⟨a1, ha1G⟩) ≤ e := by
        simpa using hfclose ⟨a1, ha1G⟩
      have hdist' : Code.wt ((u + a1 • v) - (f ⟨a1, ha1G⟩)) ≤ e := by
        simpa [LinearCode.hammingDist_eq_wt_sub] using hdist
      have hres : (u + a1 • v) - (cstar + a1 • dstar) = u' + a1 • v' := by
        simpa [u', v'] using ProximityToRS.sub_affine_distrib (u) (v) (cstar) (dstar) a1
      simpa [hfa_affine ⟨a1, ha1G⟩, hres] using hdist'
    -- Deduce wt(v') ≤ 2e from the difference of residuals at a1 and a0.
    have h_v'_wt_le_2e : Code.wt v' ≤ 2 * e := by
      -- (u' + a1•v') - (u' + a0•v') = (a1 - a0) • v'
      have hdiff_eq' : (u' + a1 • v') - (u' + a0 • v') = a1 • v' - a0 • v' := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (add_sub_add_comm u' (a1 • v') u' (a0 • v'))
      -- wt((a1 - a0)•v') = wt(v') since (a1 - a0) ≠ 0
      have hcoeff_ne : (a1 - a0) ≠ 0 := sub_ne_zero.mpr hneq
      have hwt_smul : Code.wt ((a1 - a0) • v') = Code.wt v' :=
        ProximityToRS.wt_smul_eq_of_ne_zero (ι := ι) (a := (a1 - a0)) (x := v') hcoeff_ne
      -- wt((a1 - a0)•v') = wt((u' + a1•v') - (u' + a0•v')) ≤ wt(u' + a1•v') + wt(u' + a0•v') ≤ 2e
      have base : Code.wt ((u' + a1 • v') - (u' + a0 • v'))
                    ≤ Code.wt (u' + a1 • v') + Code.wt (-(u' + a0 • v')) := by
        simpa [sub_eq_add_neg] using
          (ProximityToRS.wt_add_le (x := (u' + a1 • v')) (y := -(u' + a0 • v')))
      have hneg : Code.wt (-u' + -(a0 • v')) = Code.wt (u' + a0 • v') := by
        have hne : (- (1 : F)) ≠ 0 := by exact (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0))
        have :=
          (ProximityToRS.wt_smul_eq_of_ne_zero (ι := ι) (a := (-1 : F)) (x := (u' + a0 • v')) hne)
        simpa [one_smul, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg, add_comm] using this
      have hstep :
          Code.wt (a1 • v' - a0 • v')
            ≤ Code.wt (u' + a1 • v') + Code.wt (u' + a0 • v') := by
        simpa [hdiff_eq', hneg, add_comm, add_assoc] using base
      have : Code.wt ((a1 - a0) • v') ≤ e + e := by
        -- rewrite the left side using sub_smul
        have :
            Code.wt ((a1 - a0) • v')
              ≤ Code.wt (u' + a1 • v') + Code.wt (u' + a0 • v') := by
          simpa [sub_smul] using hstep
        refine le_trans this ?_
        have : Code.wt (u' + a1 • v') + Code.wt (u' + a0 • v') ≤ e + e := by
          simpa [add_comm, add_left_comm, add_assoc] using (add_le_add rwt_a1 rwt_a0)
        exact this
      -- Conclude wt(v') ≤ 2e
      -- First rewrite wt v' using hwt_smul, then apply the bound
      simpa [hwt_smul, two_mul] using this
    -- Use the counting lemma on the residuals r(a) = u' + a•v' to bound |G|.
    have hcard_le :
        Nat.card {a : F // Code.wt (u' + a • v') ≤ e} ≤ 2 * e := by
      -- Large union support for u', v' (negation of the small case)
      have h_union_large : (Su' ∪ Sv').card ≥ e + 1 := by
        exact Nat.succ_le_of_lt (lt_of_not_ge h_small)
      -- Apply the generalized counting bound with R = 2e
      have hv' : Code.wt v' ≤ 2 * e := h_v'_wt_le_2e
      exact ProximityToRS.card_scalars_with_small_weight_bound_by_wt (u := u') (v := v')
        (e := e) (R := 2 * e) hv' (h_union_ge := h_union_large)
    -- Map each good scalar a ∈ G to the fact that `wt(u' + a•v') ≤ e` using the affine witnesses.
    -- Define an injective map from good scalars to small-weight scalars
    let g : {a : F // distFromCode (u + a • v) (RS : Set (ι → F)) ≤ e} →
            {a : F // Code.wt (u' + a • v') ≤ e} :=
      fun a =>
        by
          -- Show `wt(u' + a•v') ≤ e` using the affine witnesses
          have haG : a.1 ∈ G := by
            have hmem : a.1 ∈ Finset.univ ∧ distFromCode (u + a.1 • v) (RS : Set (ι → F)) ≤ e := by
              exact ⟨by simp, a.2⟩
            have : a.1 ∈ Finset.univ.filter
                (fun a : F => distFromCode (u + a • v) (RS : Set (ι → F)) ≤ e) :=
              Finset.mem_filter.mpr hmem
            simpa [G] using this
          have hdist : hammingDist (u + a.1 • v) (f ⟨a.1, haG⟩) ≤ e := by
            simpa using hfclose ⟨a.1, haG⟩
          have hdist' : Code.wt ((u + a.1 • v) - (f ⟨a.1, haG⟩)) ≤ e := by
            simpa [LinearCode.hammingDist_eq_wt_sub] using hdist
          have hres : (u + a.1 • v) - (cstar + a.1 • dstar) = u' + a.1 • v' := by
            simpa [u', v'] using ProximityToRS.sub_affine_distrib (u) (v) (cstar) (dstar) a.1
          have hwt : Code.wt (u' + a.1 • v') ≤ e := by
            simpa [hfa_affine ⟨a.1, haG⟩, hres] using hdist'
          exact ⟨a.1, hwt⟩
    have ginj : Function.Injective g := by
      intro x y h
      cases x; cases y; cases h; rfl
    -- Therefore |G| ≤ |{a | wt(u' + a•v') ≤ e}| ≤ 2e < minDist(RS).
    -- Convert cardinalities via `card_subtype`.
    have hcard_good_le :
        Nat.card {a : F // distFromCode (u + a • v) (RS : Set (ι → F)) ≤ e}
          ≤ Nat.card {a : F // Code.wt (u' + a • v') ≤ e} :=
      Finite.card_le_of_injective g ginj
    have hcard_le' := le_trans hcard_good_le hcard_le
    -- Finally, compare 2e with minDist via `he`.
    have h2e_lt : 2 * e < Code.minDist (RS : Set (ι → F)) := by
      have : 2 * e ≤ 3 * e := by nlinarith
      exact lt_of_le_of_lt this he
    -- from card ≤ 2e and 2e < d, deduce card ≤ d
    have hlt := lt_of_le_of_lt hcard_le' h2e_lt
    exact Or.inr (le_of_lt hlt)

/-- Lemma 4.4 (dichotomy form, counting good scalars), specialized to RS. -/
lemma line_dichotomy_card_good
  (he : 3 * e < Code.minDist (ReedSolomon.code α deg : Set (ι → F)))
  (u v : ι → F) :
  (∀ a : F, distFromCode (u + a • v) (ReedSolomon.code α deg) ≤ e)
  ∨ (Nat.card {a : F // distFromCode (u + a • v) (ReedSolomon.code α deg) ≤ e}
        ≤ Code.minDist (ReedSolomon.code α deg : Set (ι → F))) := by
  classical
  -- Abbreviation
  set RS := (ReedSolomon.code α deg) with hRS
  -- Case 1: small union support ⇒ all scalars are good
  let Su : Finset ι := Finset.univ.filter fun i : ι => u i ≠ 0
  let Sv : Finset ι := Finset.univ.filter fun i : ι => v i ≠ 0
  by_cases hSmall : (Su ∪ Sv).card ≤ e
  · left
    intro a
    simpa [hRS] using
      (all_points_close_when_union_support_le_e (L := ReedSolomon.code α deg)
        (u := u) (v := v) hSmall a)
  · -- Large union support: invoke the far‑branch disjunction
    have hfar := far_branch_either_all_or_bound (RS := ReedSolomon.code α deg) (e := e)
      (he := by simpa [hRS] using he) (u := u) (v := v)
    rcases hfar with hall | hbound
    · left; intro a; simpa [hRS] using hall a
    · right; simpa [hRS] using hbound
end ProximityToRS
