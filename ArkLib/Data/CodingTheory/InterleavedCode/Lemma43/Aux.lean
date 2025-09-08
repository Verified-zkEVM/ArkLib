/-
Auxiliaries for Lemma 4.3: error sets and Hamming-norm helpers.
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

noncomputable section

open Code

namespace InterleavedCode
namespace Lemma43

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {κ : Type*} [Fintype κ]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- A small finite-set helper. -/
lemma exists_not_mem_of_card_lt_univ
  {α : Type*} [Finite α] [DecidableEq α]
  (s : Finset α) (h : s.card < Nat.card α) : ∃ a : α, a ∉ s := by
  classical
  by_contra hnone
  push_neg at hnone
  let fFintype : Fintype α := Fintype.ofFinite α
  have : s = (Finset.univ : Finset α) := by
    ext a; constructor <;> intro ha
    · exact Finset.mem_univ a
    · exact hnone a
  have hc : s.card = Nat.card α := by simp [this]
  have h' : s.card < s.card := by simpa [hc] using h
  exact (lt_irrefl (s.card)).elim h'

/-- Hamming distance equals the size of the error set. -/
def Err (v c : ι → F) : Finset ι := Finset.univ.filter (fun j => v j ≠ c j)

omit [Field F] [Fintype F] [DecidableEq ι] in
lemma errset_card_eq_hamming (v c : ι → F) :
  hammingDist v c = (Err (ι := ι) v c).card := by
  classical
  simp [Err, hammingDist]

/-- Error vector `χ(v,c)`. -/
def chi (v c : ι → F) : ι → F := fun j => v j - c j

omit [Fintype F] [DecidableEq ι] in
/-- Hamming norm of the difference equals Hamming distance. -/
lemma hammingNorm_sub_eq_hamming (v c : ι → F) :
  hammingNorm (fun j => v j - c j) = hammingDist v c := by
  classical
  -- (v j - c j) = 0 ↔ v j = c j
  have hset :
      (Finset.univ.filter fun j : ι => (v j - c j) ≠ 0)
        = (Finset.univ.filter fun j : ι => v j ≠ c j) := by
    ext j; simp [sub_eq_zero]
  simp [hammingNorm, hammingDist, hset]

omit [Fintype F] [DecidableEq ι] in
/-- Scaling by a nonzero does not change Hamming weight. -/
lemma hammingNorm_smul_eq_of_ne_zero (α : F) (hα : α ≠ 0) (x : ι → F) :
  hammingNorm (fun j => α * x j) = hammingNorm x := by
  classical
  have hset :
      (Finset.univ.filter fun j : ι => α * x j ≠ 0)
        = (Finset.univ.filter fun j : ι => x j ≠ 0) := by
    ext j; simp [mul_eq_zero, hα]
  simpa [hammingNorm] using congrArg Finset.card hset

end Lemma43
end InterleavedCode
