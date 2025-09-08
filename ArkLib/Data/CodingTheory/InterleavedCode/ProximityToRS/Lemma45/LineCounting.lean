/-
Per‑line counting via Lemma 4.4 (Roth–Zémor): finished proofs.
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Aux
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Lemma44
import Mathlib.Tactic

open scoped BigOperators

set_option linter.unnecessarySimpa false

noncomputable section

open Code

namespace ProximityToRS

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype F] [DecidableEq ι] [Nonempty ι] in
private lemma v_in_RS_of_all_close_e0
  {deg : ℕ} {α : ι ↪ F} {v x : ι → F}
  (hall0 : ∀ a : F, Code.distFromCode (x + a • v) (ReedSolomon.code α deg) ≤ 0) :
  v ∈ ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F)) := by
  classical
  have hx_mem : x ∈ ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F)) := by
    have hx0 := hall0 0
    have : Code.distFromCode x (ReedSolomon.code α deg) = 0 :=
      le_antisymm (by simpa using hx0) bot_le
    simpa using
      (Code.distFromCode_eq_zero_iff_mem
        ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F)) x).1 this
  have hx1_mem : (x + (1 : F) • v)
      ∈ ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F)) := by
    have hx1 := hall0 1
    have : Code.distFromCode (x + (1 : F) • v) (ReedSolomon.code α deg) = 0 :=
      le_antisymm (by simpa using hx1) bot_le
    simpa using
      (Code.distFromCode_eq_zero_iff_mem
        ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F))
        (x + (1 : F) • v)).1 this
  have hsmul_mem : (1 : F) • v
      ∈ ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F)) := by
    have hsub :=
      Submodule.sub_mem (ReedSolomon.code α deg)
        (by simpa using hx1_mem) (by simpa using hx_mem)
    have hdiff : (x + (1 : F) • v) - x = (1 : F) • v := by simp
    simpa [hdiff] using hsub
  have : (1 : F)⁻¹ • ((1 : F) • v)
      ∈ ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F)) := by
    simpa using
      Submodule.smul_mem (ReedSolomon.code α deg) ((1 : F)⁻¹) (by simpa using hsmul_mem)
  simpa using this

-- Existence of a far point on each parallel line through x.
lemma exists_far_on_line_through_x
  {deg : ℕ} [NeZero deg] {α : ι ↪ F} {e : ℕ} {v x : ι → F}
  (he : 3 * e < Code.minDist (ReedSolomon.code α deg : Set (ι → F)))
  (hv_far : e < Code.distFromCode v (ReedSolomon.code α deg)) :
  ∃ a : F, e < Code.distFromCode (x + a • v) (ReedSolomon.code α deg) := by
  classical
  -- Suppose, towards a contradiction, that every point on the line is within distance ≤ e.
  by_contra hforall
  have hall : ∀ a : F,
      Code.distFromCode (x + a • v) (ReedSolomon.code α deg) ≤ e := by
    intro a; exact not_lt.mp ((not_exists.mp hforall) a)
  -- Split on whether e = 0 or e ≥ 1.
  cases e with
  | zero =>
      have hv_mem : v ∈ ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F)) :=
        v_in_RS_of_all_close_e0 (deg := deg) (α := α) (v := v) (x := x)
          (by intro a; simpa using hall a)
      have : Code.distFromCode v (ReedSolomon.code α deg) = 0 := by
        simpa using
          (Code.distFromCode_eq_zero_iff_mem
            ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F)) v).2 hv_mem
      exact (lt_irrefl (0 : ℕ∞)) (by simpa [this] using hv_far)
  | succ e' =>
      -- Build affine witnesses on all scalars and recenter to residuals r(a) = u' + a•v'.
      let G : Finset F := Finset.univ
      -- Helper: sum over the field of an indicator equals 1
      have sum_eq_one : ∀ x : F,
          (Finset.univ : Finset F).sum (fun a => (if a = x then (1 : ℕ) else 0)) = 1 := by
        classical
        intro x
        have hsum_card :
            (Finset.univ : Finset F).sum (fun a => (if a = x then (1 : ℕ) else 0))
              = (Finset.univ.filter (fun a : F => a = x)).card := by
          simpa [Finset.card_filter]
        have hfilter :
            (Finset.univ.filter (fun a : F => a = x)) = ({x} : Finset F) := by
          classical
          ext a; by_cases h : a = x
          · simp [h]
          · simp [h]
        calc
          (Finset.univ : Finset F).sum (fun a => (if a = x then (1 : ℕ) else 0))
              = (Finset.univ.filter (fun a : F => a = x)).card := hsum_card
          _ = ({x} : Finset F).card := by simpa [hfilter]
          _ = 1 := by simp
      have hf_ex : ∀ a : {a : F // a ∈ G},
          ∃ w ∈ ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F)),
              Δ₀(x + a.1 • v, w) ≤ e'.succ := by
        intro a
        exact
          ProximityToRS.exists_codeword_close_of_dist_le
            (u := x + a.1 • v) (C := (ReedSolomon.code α deg)) (e := e'.succ)
            (by simpa using hall a.1)
      choose f hfRS hfclose using hf_ex
      have h0 : (0 : F) ∈ G := by simp [G]
      have h1 : (1 : F) ∈ G := by simp [G]
      obtain ⟨cstar, dstar, hc_in, hd_in, hfa_affine⟩ :=
        ProximityToRS.affine_param_on_G (RS := ReedSolomon.code α deg)
          (u := x) (v := v) (G := G) (a0 := 0) (a1 := 1)
          (ha0 := h0) (ha1 := h1) (hneq := by simpa using (zero_ne_one : (0 : F) ≠ 1))
          (he3 := he) (f := f)
          (hfRS := by intro a; simpa using hfRS a)
          (hfclose := by intro a; simpa using hfclose a)
      set u' : ι → F := x - cstar
      set v' : ι → F := v - dstar
      have hres_le : ∀ a : F, Code.wt (u' + a • v') ≤ e'.succ := by
        intro a
        have hfa := congrArg (fun (g : ι → F) => (x + a • v) - g) (hfa_affine ⟨a, by simp [G]⟩)
        have hdist_le : Code.wt ((x + a • v) - f ⟨a, by simp [G]⟩) ≤ e'.succ := by
          simpa [LinearCode.hammingDist_eq_wt_sub] using (hfclose ⟨a, by simp [G]⟩)
        have hdist_le' : Code.wt ((x + a • v) - (cstar + a • dstar)) ≤ e'.succ := by
          simpa [hfa] using hdist_le
        have : (x + a • v) - (cstar + a • dstar) = u' + a • v' := by
          simp [u', v', sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add]
        simpa [this, sub_eq_add_neg] using hdist_le'
      -- New double-counting lower bound on the total sum of weights across all scalars
      let S : Finset ι := Finset.univ.filter (fun i : ι => v' i ≠ 0)
      have hsum_lb : (∑ a : F, Code.wt (u' + a • v'))
                      ≥ (Fintype.card F - 1) * S.card := by
        classical
        let a0 : ι → F := fun i => if h : v' i = 0 then 0 else -u' i * (v' i)⁻¹
        have hsubset_for_a : ∀ a : F,
              (S.filter (fun i : ι => a ≠ a0 i))
                ⊆ (Finset.univ.filter
                      (fun i : ι => (u' + a • v') i ≠ 0)) := by
          intro a i hi
          have hvi : v' i ≠ 0 := by simpa [S] using (Finset.mem_filter.mp hi).1
          have ha_ne : a ≠ a0 i := (Finset.mem_filter.mp hi).2
          have hneq : u' i + a * v' i ≠ 0 := by
            have ha0_def : a0 i = -u' i * (v' i)⁻¹ := by simpa [a0, hvi]
            intro hzero
            -- Multiply by (v' i)⁻¹ and solve for a; use v' i ≠ 0
            have hmul := congrArg (fun t => t * (v' i)⁻¹) hzero
            have hvne : v' i ≠ 0 := hvi
            have hsum : u' i * (v' i)⁻¹ + a = 0 := by
              -- (u' + a * v') * (v')⁻¹ = u' * (v')⁻¹ + a * (v' * (v')⁻¹) = u' * (v')⁻¹ + a
              simpa [mul_add, add_mul, mul_left_comm, mul_comm, mul_assoc,
                CommGroupWithZero.mul_inv_cancel (v' i) hvne, mul_one] using hmul
            have a_eq : a = -u' i * (v' i)⁻¹ := by
              have : a = -(u' i * (v' i)⁻¹) := by
                have := eq_neg_of_add_eq_zero_right hsum
                simpa [mul_comm] using this
              simpa [mul_comm] using this
            have : a = a0 i := by simpa [ha0_def] using a_eq
            exact ha_ne this
          have : (u' + a • v') i ≠ 0 := by
            -- pointwise evaluation of addition and scalar multiplication on functions
            simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hneq
          have : i ∈ (Finset.univ.filter fun i : ι => (u' + a • v') i ≠ 0) := by
            apply Finset.mem_filter.mpr; apply And.intro; simp; exact this
          exact this
        have hwt_ge : ∀ a : F,
            Code.wt (u' + a • v') ≥ (S.filter (fun i : ι => a ≠ a0 i)).card := by
          intro a; simpa [Code.wt] using Finset.card_mono (hsubset_for_a a)
        have hsum_ge : (∑ a : F, Code.wt (u' + a • v'))
                        ≥ ∑ a : F, (S.filter (fun i : ι => a ≠ a0 i)).card :=
          by exact Finset.sum_le_sum (fun a _ => hwt_ge a)
        -- Direct double counting via swapping sums and counting nonzeros for each coordinate
        -- First, evaluate the inner sum for each fixed coordinate i ∈ S.
        have hinner : ∀ i ∈ S,
            ∑ a : F, (if (u' i + a * v' i) ≠ 0 then 1 else 0)
              = Fintype.card F - 1 := by
          classical
          intro i hi
          have hvne : v' i ≠ 0 := by
            have : i ∈ Finset.univ.filter (fun j : ι => v' j ≠ 0) := by simpa [S] using hi
            simpa [Finset.mem_filter] using this
          -- Unique zero at a0 i
          have hzero_iff : ∀ a : F, (u' i + a * v' i) = 0 ↔ a = a0 i := by
            intro a; constructor
            · intro h0
              -- Multiply by (v' i)⁻¹ on the right and solve for a
              have hmul := congrArg (fun t => t * (v' i)⁻¹) h0
              have hsum : u' i * (v' i)⁻¹ + a = 0 := by
                -- (u' + a * v') * (v')⁻¹ = u' * (v')⁻¹ + a * (v' * (v')⁻¹) = u' * (v')⁻¹ + a
                simpa [mul_add, add_mul, mul_left_comm, mul_comm, mul_assoc,
                  CommGroupWithZero.mul_inv_cancel (v' i) hvne, mul_one] using hmul
              have hsum' : a + u' i * (v' i)⁻¹ = 0 := by simpa [add_comm] using hsum
              have : a = -(u' i * (v' i)⁻¹) := eq_neg_of_add_eq_zero_left hsum'
              simpa [a0, hvne, mul_comm, mul_left_comm, mul_assoc] using this
            · intro ha
              -- Substitute a = a0 i and compute
              subst ha
              have hmul' : a0 i * v' i = -u' i := by
                simp [a0, hvne]
              simpa [hmul']
          -- sum of (≠ 0) equals |F| - sum of (=0)
          -- Evaluate the inner sum via counting: {a | u' i + a*v' i ≠ 0} = univ.erase (a0 i)
          have hzero_iff' : ∀ a : F, (u' i + a * v' i = 0) ↔ a = a0 i := hzero_iff
          have hfilter_eq :
              (Finset.univ.filter fun a : F => (u' i + a * v' i) ≠ 0)
                = (Finset.univ.erase (a0 i)) := by
            classical
            ext a; constructor
            · intro ha
              have haU : a ∈ (Finset.univ : Finset F) := by simpa using (Finset.mem_filter.mp ha).1
              have hane : a ≠ a0 i := by
                have : (u' i + a * v' i) ≠ 0 := (Finset.mem_filter.mp ha).2
                exact by
                  intro hEq; apply this; have := (hzero_iff' a).mpr hEq; simpa using this
              simpa [Finset.mem_erase, haU, hane, and_comm]  -- reorder to match simp normal form
            · intro ha
              have haU : a ∈ (Finset.univ : Finset F) := by
                exact (Finset.mem_erase.mp ha).2
              have hane : a ≠ a0 i := (Finset.mem_erase.mp ha).1
              have hne0 : (u' i + a * v' i) ≠ 0 := by
                intro h0; exact hane ((hzero_iff' a).mp h0)
              exact by
                apply Finset.mem_filter.mpr; exact And.intro (by simpa using haU) hne0
          -- Now evaluate the sum as a cardinality
          have hzsum :
              ∑ a : F, (if (u' i + a * v' i) = 0 then 1 else 0) = 1 := by
            classical
            have : (fun a : F => (if (u' i + a * v' i) = 0 then 1 else 0))
                      = (fun a : F => (if a = a0 i then 1 else 0)) := by
              funext a; by_cases h : (u' i + a * v' i) = 0
              · have : a = a0 i := (hzero_iff' a).mp h; simp [←this, h]
              · have : a ≠ a0 i := by
                  intro contra; apply h; have := (hzero_iff' a).mpr contra; simpa using this
                simp [h, this]
            simpa [this] using (sum_eq_one (a0 i))
          have htot : ∑ a : F, (1 : ℕ) = Fintype.card F := by
            classical
            have h₁ : ∀ a ∈ (Finset.univ : Finset F), (1 : ℕ) = 1 := by intro a ha; rfl
            simpa using (Finset.sum_const_nat (s := (Finset.univ : Finset F)) (f := fun _ : F => (1 : ℕ)) (m := 1) h₁)
          calc
            ∑ a : F, (if (u' i + a * v' i) ≠ 0 then 1 else 0)
                = (Finset.univ.filter fun a : F => (u' i + a * v' i) ≠ 0).card := by
                      classical
                      simpa [Finset.card_filter]
            _ = (Finset.univ.erase (a0 i)).card := by simpa [hfilter_eq]
            _ = Fintype.card F - 1 := by
                  classical
                  simpa using (Finset.card_erase (s := (Finset.univ : Finset F)) (a := a0 i))
        -- Then swap sums and use the inner evaluation to compute the total.
        have hsum_eq_S :
            ∑ a : F, (S.filter (fun i : ι => (u' + a • v') i ≠ 0)).card
              = (Fintype.card F - 1) * S.card := by
          classical
          have h1 : ∀ a : F,
              (S.filter (fun i : ι => (u' + a • v') i ≠ 0)).card
                = ∑ i ∈ S, (if (u' i + a * v' i) ≠ 0 then 1 else 0) := by
            intro a; simp [Pi.smul_apply, smul_eq_mul, Finset.card_filter]
          have h2 :
              ∑ a : F, (S.filter (fun i : ι => (u' + a • v') i ≠ 0)).card
                = ∑ a : F, ∑ i ∈ S, (if (u' i + a * v' i) ≠ 0 then 1 else 0) := by
            refine Finset.sum_congr rfl ?_;
            intro a ha; simpa using h1 a
          have h3 :
              ∑ a : F, ∑ i ∈ S, (if (u' i + a * v' i) ≠ 0 then 1 else 0)
                = ∑ i ∈ S, ∑ a : F, (if (u' i + a * v' i) ≠ 0 then 1 else 0) := by
            classical
            -- Swap the order of summation explicitly to avoid heavy simp search
            exact Finset.sum_comm
          have h4 :
              ∑ i ∈ S, ∑ a : F, (if (u' i + a * v' i) ≠ 0 then 1 else 0)
                = (Fintype.card F - 1) * S.card := by
            -- Evaluate each inner sum using hinner and then sum constants over S
            have h4a :
                ∑ i ∈ S, ∑ a : F, (if (u' i + a * v' i) ≠ 0 then 1 else 0)
                  = ∑ i ∈ S, (Fintype.card F - 1) :=
              Finset.sum_congr rfl (fun i hi => by simpa using hinner i hi)
            have h4b : ∑ i ∈ S, (Fintype.card F - 1) = S.card * (Fintype.card F - 1) := by
              classical
              -- Sum of a constant over a finite set equals cardinality times the constant
              simpa [Finset.sum_const, nsmul_eq_mul]
            -- Chain the equalities and orient the product at the end
            calc
              ∑ i ∈ S, ∑ a : F, (if (u' i + a * v' i) ≠ 0 then 1 else 0)
                  = ∑ i ∈ S, (Fintype.card F - 1) := by simpa using h4a
              _ = S.card * (Fintype.card F - 1) := h4b
              _ = (Fintype.card F - 1) * S.card := by simpa [Nat.mul_comm]
          -- Rewrite the left-hand side via h2, then swap sums (h3), and apply h4
          calc
            ∑ a : F, (S.filter (fun i : ι => (u' + a • v') i ≠ 0)).card
                = ∑ a : F, ∑ i ∈ S, (if (u' i + a * v' i) ≠ 0 then 1 else 0) := by simpa using h2
            _ = ∑ i ∈ S, ∑ a : F, (if (u' i + a * v' i) ≠ 0 then 1 else 0) := by simpa using h3
            _ = (Fintype.card F - 1) * S.card := h4
        -- Final lower bound: wt dominates filtered-card sum
        have hsum_ge' :
            (∑ a : F, Code.wt (u' + a • v'))
              ≥ ∑ a : F, (S.filter (fun i : ι => (u' + a • v') i ≠ 0)).card := by
          classical
          refine Finset.sum_le_sum ?_
          intro a ha
          -- S.filter ⊆ univ.filter ⇒ card ≤ card; but wt = card of univ.filter
          have hsubset : (S.filter (fun i : ι => (u' + a • v') i ≠ 0))
                          ⊆ (Finset.univ.filter (fun i : ι => (u' + a • v') i ≠ 0)) := by
            intro i hi
            have hiU : i ∈ Finset.univ := by simp
            have hcond : (u' + a • v') i ≠ 0 := (Finset.mem_filter.mp hi).2
            simpa [Finset.mem_filter] using And.intro hiU hcond
          have hcard_le := Finset.card_mono hsubset
          simpa [Code.wt, Pi.smul_apply, smul_eq_mul] using hcard_le
        -- Combine the two steps to get the target bound
        have : (∑ a : F, Code.wt (u' + a • v')) ≥ (Fintype.card F - 1) * S.card := by
          classical
          calc
            ∑ a : F, Code.wt (u' + a • v')
                ≥ ∑ a : F, (S.filter (fun i : ι => (u' + a • v') i ≠ 0)).card := hsum_ge'
            _ = (Fintype.card F - 1) * S.card := hsum_eq_S
        exact this
      -- Upper bound via the per-scalar residual guarantee.
      have hsum_ub :
          (∑ a : F, Code.wt (u' + a • v')) ≤ (Fintype.card F) * e'.succ := by
        classical
        have hpt : ∀ a : F, Code.wt (u' + a • v') ≤ e'.succ := hres_le
        have hsum_le :
            (∑ a : F, Code.wt (u' + a • v')) ≤ ∑ a : F, e'.succ :=
          Finset.sum_le_sum (by intro a _; exact hpt a)
        -- Evaluate the RHS as a constant sum over univ
        simpa [Finset.card_univ, Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]
          using hsum_le
      -- From 3*e < d ≤ |ι| + 1 ≤ |F| + 1, deduce |F| ≥ e + 2
      have hminRS : Code.minDist (ReedSolomon.code α deg : Set (ι → F))
            = Fintype.card ι - deg + 1 := by
        simpa using (ProximityToRS.minDist_RS_general (α := α) (deg := deg) (F := F) (ι := ι))
      have h3e_lt : 3 * e'.succ < Fintype.card ι - deg + 1 := by simpa [hminRS] using he
      have h3e_le_ι : 3 * e'.succ ≤ Fintype.card ι := by
        have : Fintype.card ι - deg + 1 ≤ Fintype.card ι + 1 := Nat.succ_le_succ (Nat.sub_le _ _)
        exact Nat.lt_succ_iff.mp (lt_of_lt_of_le h3e_lt this)
      have hι_leF : Fintype.card ι ≤ Fintype.card F :=
        Fintype.card_le_of_injective (fun i => (α i)) (by intro i j hij; simpa using (α.injective hij))
      have hF_large : e'.succ.succ.succ ≤ Fintype.card F := by
        have h3e_leF : 3 * e'.succ ≤ Fintype.card F := le_trans h3e_le_ι hι_leF
        -- Since e'.succ ≥ 1, we have e'.succ + 2 ≤ 3 * e'.succ
        have h1 : e'.succ.succ.succ ≤ 3 * e'.succ := by nlinarith
        exact le_trans h1 h3e_leF
      -- If wt(v') ≥ e+1, then (|F|-1)*(e+1) ≤ sum ≤ |F|*e, impossible when |F| ≥ e+2.
      have hv'_le : Code.wt v' ≤ e'.succ := by
        classical
        by_contra hk
        have hk' : e'.succ.succ ≤ Code.wt v' := Nat.succ_le_of_lt (lt_of_not_ge hk)
        have hsum_lb' :
            (Fintype.card F - 1) * (e'.succ + 1)
              ≤ (∑ a : F, Code.wt (u' + a • v')) := by
          have : (Fintype.card F - 1) * (e'.succ + 1)
              ≤ (Fintype.card F - 1) * (Code.wt v') :=
            Nat.mul_le_mul_left _ hk'
          exact le_trans this hsum_lb
        have hle :
            (Fintype.card F - 1) * (e'.succ + 1)
              ≤ Fintype.card F * e'.succ :=
          le_trans hsum_lb' hsum_ub
        -- But for |F| ≥ e+2 this inequality is false.
        have : False := by
          -- Rewrite (|F|-1)*(e+1) as |F|*e + (|F| - (e+1)) and cancel.
          -- From e + 2 ≤ |F| we also get e + 1 < |F|
          have hltF' : e'.succ.succ < Fintype.card F := (Nat.succ_le_iff.mp hF_large)
          have hrewrite :
              (Fintype.card F - 1) * (e'.succ + 1)
                = Fintype.card F * e'.succ
                    + (Fintype.card F - (e'.succ + 1)) := by
            -- (m - 1) * k = m*k - 1*k
            have h₁ :
                (Fintype.card F - 1) * (e'.succ + 1)
                  = Fintype.card F * (e'.succ + 1) - (e'.succ + 1) := by
              simpa using Nat.sub_mul (Fintype.card F) 1 (e'.succ + 1)
            -- m * (n + 1) = m*n + m
            have h₂ : Fintype.card F * (e'.succ + 1)
                  = Fintype.card F * e'.succ + Fintype.card F := by
              simpa [Nat.mul_add, Nat.mul_one, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
            -- (a + b) - c = a + (b - c) when c ≤ b
            have hleF : e'.succ + 1 ≤ Fintype.card F := le_of_lt hltF'
            have h₃ : (Fintype.card F * e'.succ + Fintype.card F)
                      - (e'.succ + 1)
                      = Fintype.card F * e'.succ
                          + (Fintype.card F - (e'.succ + 1)) := by
              -- (a + b) - c = a + (b - c) when c ≤ b
              have hgen := Nat.add_sub_assoc hleF
              simpa using (hgen (Fintype.card F * e'.succ))
            -- Chain the equalities
            calc
              (Fintype.card F - 1) * (e'.succ + 1)
                  = Fintype.card F * (e'.succ + 1) - (e'.succ + 1) := h₁
              _ = (Fintype.card F * e'.succ + Fintype.card F)
                    - (e'.succ + 1) := by simpa [h₂]
              _ = Fintype.card F * e'.succ
                    + (Fintype.card F - (e'.succ + 1)) := h₃
          -- Cancel the common left summand to get (|F| - (e+1)) ≤ 0
          have hcancel : Fintype.card F - (e'.succ + 1) ≤ 0 := by
            -- From hle and the rewrite, cancel the left term using add_le_add_iff_left
            have : Fintype.card F * e'.succ
                    + (Fintype.card F - (e'.succ + 1))
                    ≤ Fintype.card F * e'.succ := by
              simpa [hrewrite] using hle
            exact Nat.le_of_add_le_add_left this
          -- But |F| ≥ e+2 ⇒ |F| - (e+1) ≥ 1, contradiction
          have hpos : 0 < Fintype.card F - (e'.succ + 1) := Nat.sub_pos_of_lt hltF'
          have hone_le : 1 ≤ Fintype.card F - (e'.succ + 1) := Nat.succ_le_of_lt hpos
          exact (not_le_of_gt hone_le hcancel).elim
        exact this.elim
      -- Conclude dist(v, RS) ≤ e using d* ∈ RS and wt(v - d*) ≤ e.
      have hv_le : Code.distFromCode v (ReedSolomon.code α deg) ≤ e'.succ := by
        have hvd_nat : (Code.wt v' : ℕ∞) ≤ (e'.succ : ℕ∞) := by exact_mod_cast hv'_le
        have hvd_le : (hammingDist v dstar : ℕ∞) ≤ e'.succ := by
          simpa [LinearCode.hammingDist_eq_wt_sub, v', sub_eq_add_neg] using hvd_nat
        have hmem : (e'.succ : ℕ∞)
            ∈ {d : ℕ∞ | ∃ z ∈ ((ReedSolomon.code α deg : Submodule F (ι → F)) : Set (ι → F)), hammingDist v z ≤ d} := by
          exact ⟨dstar, hd_in, hvd_le⟩
        have hsInf_le := sInf_le hmem
        simpa [Code.distFromCode] using hsInf_le
      -- Combine dist ≤ e and e < dist to get a contradiction
      have hlt := lt_of_le_of_lt hv_le hv_far
      exact lt_irrefl _ hlt

-- Bound the count of close points per line by d.
lemma per_line_close_count_le_d
  {deg : ℕ} [NeZero deg] {α : ι ↪ F} {e : ℕ} {v : ι → F}
  (he : 3 * e < Code.minDist (ReedSolomon.code α deg : Set (ι → F)))
  (hv_far : e < Code.distFromCode v (ReedSolomon.code α deg)) :
  ∀ x : ι → F,
    Fintype.card {a : F // Code.distFromCode (x + a • v) (ReedSolomon.code α deg) ≤ e}
      ≤ (Fintype.card ι - deg + 1) := by
  classical
  intro x
  have h := ProximityToRS.line_dichotomy_card_good (deg := deg) (α := α) (e := e) he x v
  rcases h with hall | hfew
  · -- Contradiction with existence of a far point on the line
    have ⟨a, ha⟩ := exists_far_on_line_through_x (deg := deg) (α := α) (e := e)
      (he := he) (hv_far := hv_far) (x := x)
    have : Code.distFromCode (x + a • v) (ReedSolomon.code α deg) ≤ e := hall a
    exact (lt_of_le_of_lt this ha).false.elim
  · -- Bound the number of good scalars by the RS minimum distance, then rewrite to d = n - deg + 1.
    have hmin :
        Code.minDist (ReedSolomon.code α deg : Set (ι → F)) = Fintype.card ι - deg + 1 := by
      simpa using (ProximityToRS.minDist_RS_general (α := α) (deg := deg) (F := F) (ι := ι))
    simpa [hmin] using hfew

end ProximityToRS
