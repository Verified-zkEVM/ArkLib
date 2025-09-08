/-
Three close points on an affine line and consequences.
This file isolates the long weight bound lemma so it can compile separately.
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Aux
import Mathlib.Tactic

noncomputable section

open Code

namespace ProximityToRS

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {deg : ℕ} {α : ι ↪ F}

/-- If three points on the affine line are each within `e` of the RS code, then the standard
linear combination has weight at most `3*e`.

Let `wₐ, w_b, w_c` be corresponding close codewords to `u + a•v`, `u + b•v`, `u + c•v`.
Then `(b-c)•wₐ + (c-a)•w_b + (a-b)•w_c` has weight ≤ `3*e`.
-/
lemma three_close_points_weight_bound
  (a b c : F) {e : ℕ} {u v : ι → F}
  {wₐ w_b w_c : ι → F}
  (dₐ : Δ₀(u + a • v, wₐ) ≤ e)
  (d_b : Δ₀(u + b • v, w_b) ≤ e)
  (d_c : Δ₀(u + c • v, w_c) ≤ e) :
  Code.wt ((b - c) • wₐ + (c - a) • w_b + (a - b) • w_c) ≤ 3 * e := by
  classical
  -- Define residuals rₐ, r_b, r_c capturing the e-closeness witnesses
  set rₐ : ι → F := (u + a • v) - wₐ
  set r_b : ι → F := (u + b • v) - w_b
  set r_c : ι → F := (u + c • v) - w_c
  have hrₐ : Code.wt rₐ ≤ e := by
    -- Δ₀(u + a•v, wₐ) = wt((u + a•v) - wₐ)
    simpa [rₐ, LinearCode.hammingDist_eq_wt_sub, sub_eq_add_neg] using dₐ
  have hr_b : Code.wt r_b ≤ e := by
    simpa [r_b, LinearCode.hammingDist_eq_wt_sub, sub_eq_add_neg] using d_b
  have hr_c : Code.wt r_c ≤ e := by
    simpa [r_c, LinearCode.hammingDist_eq_wt_sub, sub_eq_add_neg] using d_c

  -- Consider the standard linear combination of residuals and codewords
  let R : ι → F := (b - c) • rₐ + (c - a) • r_b + (a - b) • r_c
  let W : ι → F := (b - c) • wₐ + (c - a) • w_b + (a - b) • w_c
  let S : ι → F :=
    (b - c) • (u + a • v) + (c - a) • (u + b • v) + (a - b) • (u + c • v)

  -- Coefficient identity used for cancellation on the affine line
  have hcoeff_v : (b - c) * a + (c - a) * b + (a - b) * c = (0 : F) := by ring

  -- Regroup S into u- and v-terms, both vanish
  have hS_zero : S = 0 := by
    -- Prove pointwise using cancellation of coefficients
    ext i
    have :
        S i = ((b - c) + (c - a) + (a - b)) * (u i)
              + ((b - c) * a + (c - a) * b + (a - b) * c) * (v i) := by
      simp [S]
      ring
    simp [this, hcoeff_v]

  -- R = S - W, hence R = -W since S = 0
  have hRS : R = S - W := by
    unfold R W S rₐ r_b r_c
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hR_eq_negW : R = -W := by
    simpa [hS_zero] using hRS

  -- wt(W) = wt(-R) = wt(R)
  have hwt_eq : Code.wt W = Code.wt R := by
    -- From R = -W, deduce W = (-1)•R and use weight invariance under nonzero smul
    have hneg : (-1 : F) ≠ 0 := by simpa using (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0))
    have hW_eq : (-1 : F) • R = W := by
      -- Apply smul to both sides of R = -W
      have := congrArg (fun x => (-1 : F) • x) hR_eq_negW
      simpa [smul_neg, one_smul] using this
    -- thus wt W = wt ((-1)•R) = wt R
    simpa [hW_eq] using (wt_smul_eq_of_ne_zero (ι := ι) (a := (-1 : F)) (x := R) hneg)

  -- Triangle inequality and scaling bound give wt(R) ≤ wt((b-c)•rₐ) + wt((c-a)•r_b) + wt((a-b)•r_c)
  have hsmul_le : ∀ (s : F) (x : ι → F), Code.wt (s • x) ≤ Code.wt x := by
    intro s x; by_cases hs : s = 0
    · simp [hs, Code.wt]
    · simp [wt_smul_eq_of_ne_zero hs]
  have hR_le : Code.wt R ≤ Code.wt ((b - c) • rₐ) + Code.wt ((c - a) • r_b + (a - b) • r_c) := by
    simpa [R, add_assoc] using
      (wt_add_le (x := (b - c) • rₐ) (y := (c - a) • r_b + (a - b) • r_c))
  have h_tail : Code.wt ((c - a) • r_b + (a - b) • r_c)
                ≤ Code.wt ((c - a) • r_b) + Code.wt ((a - b) • r_c) := by
    simpa using (wt_add_le (x := (c - a) • r_b) (y := (a - b) • r_c))
  have hR_le' : Code.wt R ≤ Code.wt ((b - c) • rₐ)
                    + (Code.wt ((c - a) • r_b) + Code.wt ((a - b) • r_c)) := by
    exact le_trans hR_le (add_le_add_left h_tail _)
  -- Bound each scaled residual by the residual's weight
  have hb1 : Code.wt ((b - c) • rₐ) ≤ Code.wt rₐ := hsmul_le (b - c) rₐ
  have hb2 : Code.wt ((c - a) • r_b) ≤ Code.wt r_b := hsmul_le (c - a) r_b
  have hb3 : Code.wt ((a - b) • r_c) ≤ Code.wt r_c := hsmul_le (a - b) r_c
  -- Chain the inequalities and use hrₐ, hr_b, hr_c ≤ e
  have : Code.wt R ≤ e + (e + e) := by
    refine le_trans hR_le' ?_
    have hsumle' : Code.wt ((b - c) • rₐ)
                      + (Code.wt ((c - a) • r_b) + Code.wt ((a - b) • r_c))
                      ≤ Code.wt rₐ + (Code.wt r_b + Code.wt r_c) := by
      simpa [add_assoc] using (add_le_add (add_le_add hb1 hb2) hb3)
    have hsumle : Code.wt rₐ + (Code.wt r_b + Code.wt r_c) ≤ e + (e + e) := by
      simpa [add_assoc] using (add_le_add (add_le_add hrₐ hr_b) hr_c)
    exact le_trans hsumle' hsumle
  -- Convert to 3*e by arithmetic
  have hsum : e + (e + e) = 3 * e := by linarith
  -- Conclude for W using wt(W) = wt(R)
  have hR_le_3e : Code.wt R ≤ 3 * e := by simpa [hsum] using this
  simp [←hwt_eq, W] at hR_le_3e
  exact hR_le_3e

end ProximityToRS
