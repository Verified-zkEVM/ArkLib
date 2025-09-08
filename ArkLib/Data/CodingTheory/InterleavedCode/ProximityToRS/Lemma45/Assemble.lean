/-
Assembling Lemma 4.5 from the components: lemma stub.
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Lemma45.CosetAveraging
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Lemma45.LineCounting
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Lemma45.ExistDirection
import ArkLib.Data.CodingTheory.InterleavedCode.ProximityToRS.Aux
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

noncomputable section

open Code

namespace ProximityToRS

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι] [Nonempty ι]

-- Stub: assemble the probability bound using the three components.
lemma probOfBadPts_assemble {deg : ℕ} [NeZero deg] {α : ι ↪ F} {e : ℕ} {U : Matrix κ ι F}
  [Fintype (Matrix.rowSpan U)]
  (he : 3 * e < Code.minDist (ReedSolomon.code α deg : Set (ι → F)))
  (hU : e < Δ(U,InterleavedCode.matrixSubmoduleOfLinearCode κ (ReedSolomon.code α deg))) :
  (PMF.uniformOfFintype (Matrix.rowSpan U)).toOuterMeasure
    { w | distFromCode (n := ι) (R := F) w (ReedSolomon.code α deg) ≤ e }
  ≤ (Fintype.card ι - deg + 1)/(Fintype.card F) := by
  classical
  -- Notation for the RS code
  let RS : Set (ι → F) := (ReedSolomon.code α deg : Set (ι → F))
  -- Field size lower bound needed by Lemma 4.3
  have hmin' : Code.minDist (ReedSolomon.code α deg : Set (ι → F))
      = Fintype.card ι - deg + 1 := by
    simpa using (ProximityToRS.minDist_RS_general (α := α) (deg := deg) (F := F) (ι := ι))
  have he' : 3 * e < Fintype.card ι - deg + 1 := by
    simpa [hmin'] using he
  have h_le : Fintype.card ι - deg + 1 ≤ Fintype.card ι + 1 :=
    Nat.succ_le_succ (Nat.sub_le _ _)
  have h3e_le_n : 3 * e ≤ Fintype.card ι := by
    have := lt_of_lt_of_le he' h_le
    exact (Nat.lt_succ_iff.mp this)
  have hι_leF : Fintype.card ι ≤ Fintype.card F :=
    Fintype.card_le_of_injective (fun i => (α i)) (by intro _ _ h; simpa using (α.injective h))
  have h3e_le_F : 3 * e ≤ Fintype.card F := le_trans h3e_le_n hι_leF
  have hF : Nat.card F ≥ e.succ.succ := by
    cases e with
    | zero =>
        -- Show 2 ≤ |F| using 0 ≠ 1 in a field.
        have h2le : 2 ≤ Fintype.card F := by
          classical
          -- Inject `Fin 2` into `F` via 0 ↦ 0, 1 ↦ 1
          let f : Fin 2 → F := fun i => (if (i : ℕ) = 0 then (0 : F) else 1)
          have hf_inj : Function.Injective f := by
            intro i j hij
            fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
          have := Fintype.card_le_of_injective f hf_inj
          simpa using this
        simpa using h2le
    | succ e' =>
        -- From 3(e+1) ≤ |F| and e+3 ≤ 3(e+1), deduce e+3 ≤ |F|.
        have h_e3_le_3e : e'.succ.succ.succ ≤ 3 * e'.succ := by
          -- nlinarith handles simple linear arithmetic over ℕ
          nlinarith
        have : e'.succ.succ.succ ≤ Fintype.card F :=
          le_trans h_e3_le_3e (by simpa using h3e_le_F)
        -- e.succ.succ = (e'+1).succ.succ = e'+3
        simpa using this
  -- Far direction in the row span from Lemma 4.3
  rcases ProximityToRS.exists_far_dir_in_rowSpan (α := α) (e := e) (U := U)
      (hF := hF) (he := he) (hU := hU) with ⟨v, hv_span, hv_far⟩
  -- Per-line counting bound (≤ d = n - deg + 1 good scalars per line parallel to v)
  have hline : ∀ x : ι → F,
      Fintype.card {a : F // Code.distFromCode (x + a • v) RS ≤ e}
        ≤ (Fintype.card ι - deg + 1) :=
    per_line_close_count_le_d (deg := deg) (α := α) (e := e) (v := v)
      (he := he) (hv_far := hv_far)
  -- A Fintype instance on the row span is available from the `Finite` hypothesis
  -- Apply the uniform fraction bound with predicate P(w) := distFromCode(w, RS) ≤ e
  let P : (ι → F) → Prop := fun w => Code.distFromCode w RS ≤ e
  have hcoset : ∀ x ∈ Matrix.rowSpan U,
      Nat.card {a : F // P (fun j => x j + a * v j)} ≤ (Fintype.card ι - deg + 1) := by
    intro x _hx
    simpa [P, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using (hline x)
  have hbound0 :=
    ProximityToRS.uniform_fraction_bound (U := U) (v := v)
      (M := Fintype.card ι - deg + 1) P hv_span hcoset
  -- Convert Nat.card to Fintype.card in the denominator.
  have hbound :
      (PMF.uniformOfFintype (Matrix.rowSpan U)).toOuterMeasure {w | P (w : ι → F)}
        ≤ ((Fintype.card ι - deg + 1 : ENNReal) / (Fintype.card F : ENNReal)) := by
    simpa [Nat.card_eq_fintype_card] using hbound0
  -- Rewrite to the desired form
  -- Final rewrite to the goal statement: unfold the LHS definitionally
  change
      (PMF.uniformOfFintype (Matrix.rowSpan U)).toOuterMeasure
        {w | P (w : ι → F)}
        ≤ ((Fintype.card ι - deg + 1 : ENNReal) / (Fintype.card F : ENNReal))
  simpa [P, RS] using hbound

end ProximityToRS
