/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticPolynomialCost
public import CompPoly.Univariate.Raw.Size

/-!
# Exact profiles of raw convolution

Each pair of stored coefficients occurs in one convolution window. Metadata counts one tick per
term, one per output coefficient, and one terminal tick. Canonical multiplication separately
charges the final trim.
-/

@[expose] public section

namespace CompPoly.Arithmetic
open OracleComp OracleSpec

/-- Summing the convolution window lengths counts each pair of input indices once. -/
private theorem sum_convolutionWindows (m n : ℕ) :
    ∑ k ∈ Finset.range (n + m - 1), (min (k + 1) m - (k + 1 - n)) = m * n := by
  let windows := (Finset.range (n + m - 1)).sigma
    (fun k ↦ Finset.Ico (k + 1 - n) (min (k + 1) m))
  have hcard : windows.card = ((Finset.range m) ×ˢ (Finset.range n)).card := by
    apply Finset.card_nbij' (fun x ↦ (x.2, x.1 - x.2)) (fun x ↦ ⟨x.1 + x.2, x.1⟩)
    · intro ⟨k, i⟩ h
      simp only [Finset.mem_coe, windows, Finset.mem_sigma, Finset.mem_range,
        Finset.mem_Ico] at h
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
      omega
    · intro ⟨i, j⟩ h
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at h
      simp only [Finset.mem_coe, windows, Finset.mem_sigma, Finset.mem_range, Finset.mem_Ico]
      omega
    · intro ⟨k, i⟩ h
      simp only [Finset.mem_coe, windows, Finset.mem_sigma, Finset.mem_range,
        Finset.mem_Ico] at h
      have hk : i + (k - i) = k := by omega
      simp [hk]
    · intro ⟨i, j⟩ _
      simp
  simpa [windows, Finset.card_sigma, Nat.card_Ico] using hcard

section Operations
variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

/-- Each term of a convolution window reads two coefficients and charges its multiply, add,
and control tick. -/
theorem profileArithmetic_convolutionEntry (p q : CPolynomial.Raw F) (k lo n : ℕ)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (convolutionEntry p q k lo n)).2 kind =
      if kind = .coefficientRead then 2 * n
      else if kind = .add ∨ kind = .mul ∨ kind = .metadata then n else 0 := by
  induction n with
  | zero => simp [convolutionEntry]
  | succ n ih =>
    cases kind <;>
      simp [convolutionEntry, profileArithmetic_bind, profileArithmetic_map,
        arithmeticCost, ArithmeticOp.costKind, Nat.mul_succ] at ih ⊢ <;> omega

end Operations

section Semiring
variable {F : Type} [Semiring F] [Sub F] [Inv F] [DecidableEq F]

/-- Raw multiplication charges one addition, one multiplication, two reads and one tick per pair
of stored coefficients. Metadata also counts one tick per output position and one terminal tick. -/
theorem profileArithmetic_mulRaw (p q : CPolynomial.Raw F) :
    (profileArithmetic (mulRaw p q)).2 =
      fun kind ↦ if kind = .add ∨ kind = .mul then p.size * q.size
        else if kind = .coefficientRead then 2 * (p.size * q.size)
        else if kind = .metadata then
          p.size * q.size + (if p.size = 0 then 0 else q.size + p.size - 1) + 1
        else 0 := by
  funext kind
  by_cases hp : p.size = 0
  · cases kind <;> simp [mulRaw, hp, arithmeticCost, ArithmeticOp.costKind]
  have h : ((List.finRange (q.size + p.size - 1)).map
      (fun k ↦ min (k.val + 1) p.size - (k.val + 1 - q.size))).sum = p.size * q.size := by
    rw [← Fin.sum_univ_def]
    calc
      _ = ∑ k ∈ Finset.range (q.size + p.size - 1),
          (min (k + 1) p.size - (k + 1 - q.size)) :=
        (Finset.sum_range (fun k ↦ min (k + 1) p.size - (k + 1 - q.size))).symm
      _ = p.size * q.size := sum_convolutionWindows p.size q.size
  cases kind <;>
    simp [mulRaw, hp, profileArithmetic_certifiedOfFn, profileArithmetic_convolutionEntry,
      List.sum_map_mul_left, h, Nat.add_assoc]

/-- A convolution with at most one left coefficient has linear primitive bounds. -/
theorem profileArithmetic_mulRaw_le_of_size_le_one (p q : CPolynomial.Raw F) (hp : p.size ≤ 1)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (mulRaw p q)).2 kind ≤
      if kind = .add ∨ kind = .mul then q.size
      else if kind = .coefficientRead then 3 * q.size + 1
      else if kind = .metadata then 2 * q.size + 4 else 0 := by
  have hm := Nat.mul_le_mul_right q.size hp
  by_cases h0 : p.size = 0 <;> cases kind <;> simp [profileArithmetic_mulRaw, h0] <;> omega

/-- A convolution with at most two left coefficients has linear primitive bounds. -/
theorem profileArithmetic_mulRaw_le_of_size_le_two (p q : CPolynomial.Raw F) (hp : p.size ≤ 2)
    (kind : ArithmeticCostKind) :
    (profileArithmetic (mulRaw p q)).2 kind ≤
      if kind = .add then 2 * q.size + 1
      else if kind = .mul then 2 * q.size
      else if kind = .coefficientRead then 6 * q.size + 4
      else if kind = .metadata then 4 * q.size + 8 else 0 := by
  have hm := Nat.mul_le_mul_right q.size hp
  by_cases h0 : p.size = 0 <;> cases kind <;> simp [profileArithmetic_mulRaw, h0] <;> omega

end Semiring
end CompPoly.Arithmetic
