/- Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, František Silváši
-/
import ArkLib.Data.CodingTheory.JohnsonBound.Lemmas

namespace JohnsonBound

/-!
This module is based on the Johnson Bound section from [listdecoding].
In what follows we reference theorems from [listdecoding] by default.

## References

* [Venkatesan Guruswami, *Algorithmic Results in List Decoding*][listdecoding]
-/

variable {n : ℕ}
         {F : Type} [Fintype F] [DecidableEq F]
         {B : Finset (Fin n → F)} {v : Fin n → F}

/-- The denominator of the bound from Theorem 3.1.
-/
def JohnsonDenominator (B : Finset (Fin n → F)) (v : Fin n → F) : ℚ :=
  let e := e B v
  let d := d B
  let q : ℚ := Fintype.card F
  let frac := q / (q - 1)
  (1- frac * e/n) ^ 2 - (1 - frac * d/n)

lemma johnson_denominator_def :
  JohnsonDenominator B v = ((1 - ((Fintype.card F) / (Fintype.card F - 1)) * (e B v / n)) ^ 2
      - (1 - ((Fintype.card F) / (Fintype.card F - 1)) * (d B/n))) := by
  simp [JohnsonDenominator]
  field_simp

/-- The bound from `Theorem 3.1` makes sense only if the denominator is positive.
This condition ensures that holds.
-/
def JohnsonConditionStrong (B : Finset (Fin n → F)) (v : Fin n → F) : Prop :=
  let e := e B v
  let d := d B
  let q : ℚ := Fintype.card F
  let frac := q / (q - 1)
  (1 - frac * d/n) < (1- frac * e/n) ^ 2

/-- The function used for `q`-ary Johnson Bound.
-/
noncomputable def J (q δ : ℚ) : ℝ :=
  let frac := q / (q - 1)
  (1 / frac) * (1 - Real.sqrt (1 - frac * δ))

/-- A lemma for proving sqrt_le_J
-/
lemma division_by_conjugate {a b : ℝ} (hpos : 0 ≤ b) (hnonzero : a + b.sqrt ≠ 0) :
  a - (b).sqrt = (a^2 - b)/(a + b.sqrt) := by
  rw[eq_div_iff hnonzero]
  ring_nf
  simp_all

lemma sqrt_le_J {q δ : ℚ} (hq : q > 1) (hx0 : 0 ≤ δ) (hx1 : δ ≤ 1) (hqx : q / (q - 1) * δ ≤ 1) :
  1 - ((1-δ) : ℝ).sqrt ≤ J q δ := by
  unfold J
  set frac := q / (q - 1) with hfrac
  have hfrac_ge : frac ≥ 1 := by rw [hfrac, ge_iff_le, one_le_div] <;> grind
  have hx' : 1 - δ ≥ 0 := by linarith
  have hfracx' : 1 - frac * δ ≥ 0 := by nlinarith
  suffices 1 - √(1 - δ) ≤ (1 / frac) * (1 - √(1 - frac * δ)) by simpa
  rw[
    division_by_conjugate (by exact_mod_cast hx') (by positivity),
    division_by_conjugate (by exact_mod_cast hfracx') (by positivity)]
  have : δ = 1 - (1 - δ) := by ring
  have : frac * δ = 1 - (1 - frac * δ) := by ring
  field_simp
  norm_cast
  gcongr
  have : 1 * δ  ≤ frac * δ  := by exact mul_le_mul_of_nonneg_right hfrac_ge hx0
  simp at this
  exact this

/-- The `q`-ary Johnson bound.
-/
def JohnsonConditionWeak (B : Finset (Fin n → F)) (e : ℕ) : Prop :=
  let d := sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
  let q : ℚ := Fintype.card F
  (e : ℚ) / n < J q (d / n)

lemma johnson_condition_weak_implies_strong {B : Finset (Fin n → F)} {v : Fin n → F} {e : ℕ}
  (h : JohnsonConditionWeak B e)
  :
  JohnsonConditionStrong (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)) v := by
  sorry

private lemma johnson_condition_strong_implies_n_pos
  (h_johnson : JohnsonConditionStrong B v)
  :
  0 < n := by
  cases n <;> try simp [JohnsonConditionStrong] at *

private lemma johnson_condition_strong_implies_2_le_F_card
  (h_johnson : JohnsonConditionStrong B v)
  :
  2 ≤ Fintype.card F := by
  revert h_johnson
  dsimp [JohnsonConditionStrong]
  rcases Fintype.card F with _ | _ | _ <;> aesop

private lemma johnson_condition_strong_implies_2_le_B_card
  (h_johnson : JohnsonConditionStrong B v)
  :
  2 ≤ B.card := by
  dsimp [JohnsonConditionStrong] at h_johnson
  rcases eq : B.card with _ | card | _ <;> [simp_all [e, d]; skip; omega]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 eq
  replace h_johnson : 1 < |1 - (Fintype.card F) / ((Fintype.card F) - 1) * Δ₀(v, a) / (n : ℚ)| := by
    simp_all [e, d, choose_2]
  generalize eq₁ : Fintype.card F = q
  rcases q with _ | _ | q <;> [simp_all; simp_all; skip]
  have h : (Fintype.card F : ℚ) / (Fintype.card F - 1) = 1 + 1 / (Fintype.card F - 1) := by
    have : (Fintype.card F : ℚ) - 1 ≠ 0 := by simp [sub_eq_zero]; omega
    field_simp
  have h' := JohnsonBound.abs_one_sub_div_le_one (v := v) (a := a) (by omega)
  exact absurd (lt_of_lt_of_le (h ▸ h_johnson) h') (lt_irrefl _)

/-- `JohnsonConditionStrong` is equvalent to `JohnsonDenominator` being positive.
-/
lemma johnson_condition_strong_iff_johnson_denom_pos {B : Finset (Fin n → F)} {v : Fin n → F} :
  JohnsonConditionStrong B v ↔ 0 < JohnsonDenominator B v := by
  simp [JohnsonDenominator, JohnsonConditionStrong]

/-- Theorem 3.1.
-/
theorem johnson_bound [Field F]
  (h_condition : JohnsonConditionStrong B v)
  :
  let d := d B
  let q : ℚ := Fintype.card F
  let frac := q / (q - 1)
  B.card ≤ (frac * d/n) / JohnsonDenominator B v
  := by
  suffices B.card * JohnsonDenominator B v ≤
           Fintype.card F / (Fintype.card F - 1) * d B / n by
    rw [johnson_condition_strong_iff_johnson_denom_pos] at h_condition
    rw [←mul_le_mul_right h_condition]
    convert this using 1
    field_simp; rw [mul_div_mul_right]; linarith
  rw [johnson_denominator_def]
  exact JohnsonBound.johnson_bound_lemma
    (johnson_condition_strong_implies_n_pos h_condition)
    (johnson_condition_strong_implies_2_le_B_card h_condition)
    (johnson_condition_strong_implies_2_le_F_card h_condition)

/-- Alphabet-free Johnson bound from [codingtheory].
## References

* [Venkatesan Guruswami, Atri Rudra, Madhu Sudan, *Essential Coding Theory*][codingtheory]
-/
theorem johnson_bound_alphabet_free [Field F] [DecidableEq F]
  {B : Finset (Fin n → F)}
  {v : Fin n → F}
  {e : ℕ}
  :
  let d := sInf { d | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ hammingDist u v = d }
  let q : ℚ := Fintype.card F
  let frac := q / (q - 1)
  e ≤ n - ((n * (n - d)) : ℝ).sqrt
  →
  (B ∩ ({ x | Δ₀(x, v) ≤ e } : Finset _)).card ≤ q * d * n := by
  sorry

end JohnsonBound
