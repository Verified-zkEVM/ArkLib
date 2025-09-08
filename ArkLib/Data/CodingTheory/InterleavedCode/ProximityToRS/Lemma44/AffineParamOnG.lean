/-
Affine parametrization on G: if three-close-point identity vanishes on G, then witnesses are affine.
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Lemma44.TripleComboZero
import Mathlib.Tactic

noncomputable section

open Code

namespace ProximityToRS

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Appendix A: If a set `G` of at least two good scalars is given and the triple
combination vanishes for all triples of distinct elements of `G`, then there exist
`c* , d* ∈ RS` such that for all `a ∈ G`, the unique witness satisfies `f_a = c* + a•d*`. -/
lemma affine_param_on_G
  (RS : LinearCode ι F) {e : ℕ} (u v : ι → F)
  (G : Finset F)
  (a0 a1 : F) (ha0 : a0 ∈ G) (ha1 : a1 ∈ G) (hneq : a0 ≠ a1)
  (he3 : 3 * e < Code.minDist (RS : Set (ι → F)))
  (f : {a : F // a ∈ G} → (ι → F))
  (hfRS : ∀ a, f a ∈ (RS : Set (ι → F)))
  (hfclose : ∀ a, Δ₀(u + a.1 • v, f a) ≤ e) :
  ∃ (cstar dstar : ι → F), cstar ∈ (RS : Set (ι → F)) ∧ dstar ∈ (RS : Set (ι → F)) ∧
    (∀ a, f a = cstar + a.1 • dstar) := by
  classical
  -- Anchor codewords in RS
  set z0 : ι → F := f ⟨a0, ha0⟩
  set z1 : ι → F := f ⟨a1, ha1⟩
  -- Inverse of (a1 - a0)
  set inv01 : F := (a1 - a0)⁻¹
  have h01_ne : a1 - a0 ≠ 0 := sub_ne_zero.mpr (by exact hneq.symm)
  -- Define d* and c*
  let dstar : ι → F := inv01 • (z1 - z0)
  let cstar : ι → F := z0 - a0 • dstar
  -- Membership in RS
  have hz0 : z0 ∈ (RS : Submodule F (ι → F)) := by simpa [z0] using hfRS ⟨a0, ha0⟩
  have hz1 : z1 ∈ (RS : Submodule F (ι → F)) := by simpa [z1] using hfRS ⟨a1, ha1⟩
  have h_d_in : dstar ∈ (RS : Set (ι → F)) := by
    have hsub : z1 - z0 ∈ (RS : Submodule F (ι → F)) := by
      simpa using Submodule.sub_mem RS hz1 hz0
    have : inv01 • (z1 - z0) ∈ (RS : Submodule F (ι → F)) :=
      Submodule.smul_mem RS inv01 hsub
    simpa [dstar] using this
  have h_c_in : cstar ∈ (RS : Set (ι → F)) := by
    have : z0 - a0 • dstar ∈ (RS : Submodule F (ι → F)) := by
      have hsm : a0 • dstar ∈ (RS : Submodule F (ι → F)) := by
        simpa using Submodule.smul_mem RS a0 (by simpa using h_d_in)
      simpa using Submodule.sub_mem RS hz0 hsm
    simpa [cstar] using this
  -- For any a ∈ G, solve f a = c* + a•d* using the triple-combo identity
  have hfa_affine : ∀ a : {a : F // a ∈ G}, f a = cstar + a.1 • dstar := by
    intro a
    -- Using three-close-points combo = 0
    have htriple :=
      three_close_points_combo_is_zero (RS := RS) (e := e) (u := u) (v := v) (he := he3)
        (a := a.1) (b := a0) (c := a1)
        (fa := f a) (fb := z0) (fc := z1)
        (hfa := by simpa using hfRS a)
        (hfb := by simpa [z0] using hfRS ⟨a0, ha0⟩)
        (hfc := by simpa [z1] using hfRS ⟨a1, ha1⟩)
        (hwa := hfclose a)
        (hwb := by simpa [z0] using hfclose ⟨a0, ha0⟩)
        (hwc := by simpa [z1] using hfclose ⟨a1, ha1⟩)
    -- Let X + Y + Z = 0 with Y = (a0 - a1)•f a
    set X : ι → F := (a.1 - a0) • z1
    set Y : ι → F := (a0 - a1) • f a
    set Z : ι → F := (a1 - a.1) • z0
    have hXYZ : X + Y + Z = 0 := by
      simpa [X, Y, Z, add_comm, add_left_comm, add_assoc]
        using htriple
    -- Rearrange and cancel (a0 - a1)
    have hY : Y = -(X + Z) := by
      have : Y + (X + Z) = 0 := by simpa [add_comm, add_left_comm, add_assoc] using hXYZ
      exact eq_neg_of_add_eq_zero_left this
    -- Use inv10 = (a0 - a1)⁻¹ = -inv01
    have hsub : a0 - a1 = -(a1 - a0) := by
      simpa [sub_eq_add_neg] using (neg_sub a1 a0).symm
    set inv10 : F := -inv01
    have hmul_inv10 : (a0 - a1) * inv10 = (1 : F) := by
      calc
        (a0 - a1) * inv10
            = (-(a1 - a0)) * (-inv01) := by
              -- Expand inv10 first to avoid deep simp recursion, then rewrite with hsub
              dsimp [inv10]
              rw [hsub]
        _ = (a1 - a0) * inv01 := by simpa using (neg_mul_neg (a1 - a0) inv01)
        _ = 1 := by simpa [inv01, h01_ne]
    have hfa_eq_sum' : f a = inv10 • (-(X + Z)) := by
      -- Multiply Y = (a0 - a1)•f a = -(X + Z) by inv10 on the left and cancel
      have h1 := congrArg (fun t => inv10 • t) hY
      have h2 : ((a0 - a1) * inv10) • f a = inv10 • (-(X + Z)) := by
        simpa [Y, smul_smul, mul_comm] using h1
      have hcoef : ((a0 - a1) * inv10) = (1 : F) := hmul_inv10
      simpa [hcoef, one_smul] using h2
    have hfa_eq_sum : f a = inv01 • X + inv01 • Z := by
      -- inv10 = -inv01; distribute over addition, then cancel the negatives
      simpa [inv10, smul_neg, neg_smul, smul_add, add_comm, add_left_comm, add_assoc]
        using hfa_eq_sum'
    -- Distribute and simplify scalars
    have hfa_eq' : f a = ((a.1 - a0) * inv01) • z1 + ((a1 - a.1) * inv01) • z0 := by
      have hX' : inv01 • X = ((a.1 - a0) * inv01) • z1 := by
        simpa [X, smul_smul, mul_comm, mul_left_comm, mul_assoc]
      have hZ' : inv01 • Z = ((a1 - a.1) * inv01) • z0 := by
        simpa [Z, smul_smul, mul_comm, mul_left_comm, mul_assoc]
      calc
        f a = inv01 • X + inv01 • Z := hfa_eq_sum
        _ = ((a.1 - a0) * inv01) • z1 + ((a1 - a.1) * inv01) • z0 := by
              simpa [add_comm, add_left_comm, add_assoc, hX', hZ']
    have hRHS' : cstar + a.1 • dstar
        = ((a1 - a.1) * inv01) • z0 + ((a.1 - a0) * inv01) • z1 := by
      -- Expand cstar and dstar and collect coefficients of z0 and z1
      have hstep1 : cstar + a.1 • dstar
          = (z0 - a0 • dstar) + a.1 • dstar := rfl
      have hstep2 : (z0 - a0 • dstar) + a.1 • dstar
          = z0 + (a.1 • dstar - a0 • dstar) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm]
      have hstep3 : a.1 • dstar - a0 • dstar = (a.1 - a0) • dstar := by
        -- Use (a - b) • x = a•x - b•x
        have h := (sub_smul (a.1) a0 dstar)
        simpa [sub_eq_add_neg] using h.symm
      have hstep4 : z0 + (a.1 - a0) • dstar
          = z0 + ((a.1 - a0) * inv01) • (z1 - z0) := by
        simp [dstar, smul_smul]
      have hstep : cstar + a.1 • dstar
          = z0 + ((a.1 - a0) * inv01) • (z1 - z0) := by
        simpa [hstep1, hstep2, hstep3, hstep4]
      have hcollect : cstar + a.1 • dstar
          = (1 - ((a.1 - a0) * inv01)) • z0 + ((a.1 - a0) * inv01) • z1 := by
        -- Distribute over the difference (z1 - z0)
        have : z0 + ((a.1 - a0) * inv01) • (z1 - z0)
              = (1 - ((a.1 - a0) * inv01)) • z0 + ((a.1 - a0) * inv01) • z1 := by
          -- Rearrange: z0 + t•(z1 - z0) = (1 - t)•z0 + t•z1
          have : z0 + ((a.1 - a0) * inv01) • z1 + -(((a.1 - a0) * inv01) • z0)
                = (1 - ((a.1 - a0) * inv01)) • z0 + ((a.1 - a0) * inv01) • z1 := by
            simp [one_smul, sub_eq_add_neg, add_smul, add_comm, add_left_comm, add_assoc]
          simpa [smul_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
        simpa [hstep]
      have hcoeff : 1 - ((a.1 - a0) * inv01) = ((a1 - a.1) * inv01) := by
        have h1eq : (a1 - a0) * inv01 = (1 : F) := by simpa [inv01, h01_ne]
        calc
          1 - ((a.1 - a0) * inv01)
              = ((a1 - a0) * inv01) - ((a.1 - a0) * inv01) := by simpa [h1eq]
          _ = ((a1 - a0) - (a.1 - a0)) * inv01 := by
                simp [sub_mul]
          _ = (a1 - a.1) * inv01 := by
                have : (a1 - a0) - (a.1 - a0) = a1 - a.1 := by ring
                simpa [this]
      simpa [hcollect, hcoeff]
    -- Reorder and finish
    have hfa_comm : f a
        = ((a1 - a.1) * inv01) • z0 + ((a.1 - a0) * inv01) • z1 := by
      simpa [add_comm, add_left_comm, add_assoc] using hfa_eq'
    have hfinal : f a = cstar + a.1 • dstar := by
      simpa [hRHS', add_comm, add_left_comm, add_assoc] using hfa_comm
    simp [hfinal]
  exact ⟨cstar, dstar, h_c_in, h_d_in, hfa_affine⟩

end ProximityToRS
