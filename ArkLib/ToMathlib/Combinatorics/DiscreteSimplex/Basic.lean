/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra, Quang Dao
-/
module


public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finsupp.Multiset

/-!
# Finite discrete simplices

Nonnegative integer tuples with bounded coordinate sum, identified with symmetric powers
by adjoining a slack coordinate. These results are independent of polynomial interpolation.
Adapted with permission from `kz99/rs-ld-mca`, revision
`9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`; see the repository permission record.
-/

@[expose] public section

namespace DiscreteSimplex
open scoped BigOperators

/-- An ordinary discrete simplex, represented by a nonnegative tuple whose
coordinate sum is bounded by `z`. -/
def OrdinarySimplex (r z : ℕ) :=
  {a : Fin r → ℕ // ∑ i, a i ≤ z}

/-! ## Stars and bars for the ordinary comparison simplex -/

def ExactSimplex (r z : ℕ) :=
  {a : Fin (r + 1) → ℕ // ∑ i, a i = z}

def ordinaryToExact (r z : ℕ) (a : OrdinarySimplex r z) :
    ExactSimplex r z :=
  ⟨Fin.lastCases (z - ∑ i, a.1 i) a.1, by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
    exact Nat.add_sub_of_le a.2⟩

def exactToOrdinary (r z : ℕ) (a : ExactSimplex r z) :
    OrdinarySimplex r z :=
  ⟨fun (i : Fin r) ↦ a.1 i.castSucc, by
    change (∑ i : Fin r, a.1 i.castSucc) ≤ z
    have ha := a.2
    rw [Fin.sum_univ_castSucc] at ha
    omega⟩

/-- Adding a slack coordinate identifies a bounded ordinary simplex with a
symmetric power. -/
noncomputable def ordinarySimplexEquivSym (r z : ℕ) :
    OrdinarySimplex r z ≃ Sym (Fin (r + 1)) z :=
  (Equiv.trans {
    toFun := ordinaryToExact r z
    invFun := exactToOrdinary r z
    left_inv := fun a ↦ by
      apply Subtype.ext
      funext i
      simp [ordinaryToExact, exactToOrdinary]
    right_inv := fun a ↦ by
      apply Subtype.ext
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp only [ordinaryToExact, exactToOrdinary, Fin.lastCases_last]
        have ha := a.2
        rw [Fin.sum_univ_castSucc] at ha
        omega
      · simp [ordinaryToExact, exactToOrdinary]
  } (Sym.equivNatSumOfFintype _ _).symm)

noncomputable instance ordinarySimplexFintype (r z : ℕ) :
    Fintype (OrdinarySimplex r z) :=
  Fintype.ofEquiv (Sym (Fin (r + 1)) z)
    (ordinarySimplexEquivSym r z).symm

/-- Stars and bars for tuples whose sum is at most `z`. -/
theorem card_ordinarySimplex (r z : ℕ) :
    Fintype.card (OrdinarySimplex r z) = (z + r).choose r := by
  rw [Fintype.card_congr (ordinarySimplexEquivSym r z),
    Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have hbase : r + 1 + z - 1 = z + r := by omega
  rw [hbase]
  exact Nat.choose_symm_add

end DiscreteSimplex
