import Mathlib.Algebra.BigOperators.Fin

/-!
# More lemmas about `Fin` and big operators
-/

namespace Fin

section Interval

open Finset

variable {M : Type*} [CommMonoid M] {n : ℕ} {v : Fin (n + 1) → M}

-- @[to_additive]
-- theorem prod_Ioi_zero : ∏ i ∈ Ioi 0, v i = ∏ j : Fin n, v j.succ := by simp
--   -- rw [Ioi_zero_eq_map, Finset.prod_map, val_succEmb]

-- @[to_additive]
-- theorem prod_Ioi_succ (i : Fin n) : ∏ j ∈ Ioi i.succ, v j = ∏ j ∈ Ioi i, v j.succ := by
--   rw [Ioi_succ, Finset.prod_map, val_succEmb]

-- @[to_additive]
-- theorem prod_Ici_succ (i : Fin n) :
--     ∏ j ∈ Ici i.succ, v j = ∏ j ∈ Ici i, v j.succ := by
--   rw [Ici_succ, Finset.prod_map, val_succEmb]

@[to_additive]
theorem prod_Iio_succ (i : Fin n) :
    ∏ j ∈ Iio i.succ, v j = (∏ j ∈ Iio i.castSucc, v j) * v i.castSucc := by
  calc
    _ = ∏ j ∈ Ico 0 i.succ, v j :=
      prod_congr (by rw [← bot_eq_zero, Ico_bot]) (fun _ _ => rfl)
    _ = ∏ j ∈ Icc 0 i.castSucc, v j :=
      prod_congr rfl (fun _ _ => rfl)
    _ = ∏ j ∈ insert i.castSucc (Ico 0 i.castSucc), v j :=
      prod_congr (by simp only [zero_le, Ico_insert_right]) (fun _ _ => rfl)
    _ = v i.castSucc * ∏ j ∈ Iio i.castSucc, v j :=
      prod_insert (by simp only [mem_Ico, zero_le, lt_self_iff_false, and_false, not_false_eq_true])
    _ = (∏ j ∈ Iio i.castSucc, v j) * v i.castSucc := mul_comm _ _

@[to_additive]
theorem prod_Iio_eq_univ (i : Fin (n + 1)) :
    ∏ j ∈ Iio i, v j = ∏ j : Fin i, v (Fin.castLE i.isLt.le j) := by
  induction i using Fin.induction with
  | zero =>
    conv_lhs => rw [← bot_eq_zero]
    simp only [Iio_bot, prod_empty, val_zero, univ_eq_empty]
  | succ i hi => simp only [prod_Iio_succ, hi, prod_univ_castSucc, val_succ]; congr

@[to_additive (attr := simp)]
theorem prod_Iic_zero : ∏ j ∈ Iic 0, v j = v 0 := by
  rw [← bot_eq_zero, Iic_bot, prod_singleton]

@[to_additive]
theorem prod_Iic_succ (i : Fin n) :
    ∏ j ∈ Iic i.succ, v j = (∏ j ∈ Iic i.castSucc, v j) * v i.succ := by
  calc
    _ = ∏ j ∈ Icc 0 i.succ, v j :=
      prod_congr (by rw [← bot_eq_zero, Icc_bot]) (fun _ _ => rfl)
    _ = ∏ j ∈ insert i.succ (Ico 0 i.succ), v j :=
      prod_congr (by simp only [zero_le, Ico_insert_right]) (fun _ _ => rfl)
    _ = v i.succ * ∏ j ∈ Iic i.castSucc, v j :=
      prod_insert (by simp only [mem_Ico, zero_le, lt_self_iff_false, and_false, not_false_eq_true])
    _ = (∏ j ∈ Iic i.castSucc, v j) * v i.succ := mul_comm _ _

@[to_additive]
theorem prod_Iic_eq_univ (i : Fin (n + 1)) :
    ∏ j ∈ Iic i, v j = ∏ j : Fin (i + 1), v (Fin.castLE i.isLt j) := by
  induction i using Fin.induction with
  | zero => simp only [prod_Iic_zero, val_zero, Nat.reduceAdd, univ_unique, default_eq_zero,
    prod_singleton, castLE_zero]
  | succ i hi => simp only [prod_Iic_succ, hi, prod_univ_castSucc, val_succ]; congr

@[simp]
theorem Ici_zero : Ici (0 : Fin (n + 1)) = univ := by rw [← bot_eq_zero, Ici_bot]

@[simp]
theorem Iio_zero : Iio (0 : Fin (n + 1)) = ∅ := by rw [← bot_eq_zero, Iio_bot]

@[simp]
theorem Iic_zero : Iic (0 : Fin (n + 1)) = {0} := by rw [← bot_eq_zero, Iic_bot]

theorem Iic_castSucc (i : Fin n) : Iic (castSucc i) = (Iic i).map Fin.castSuccEmb := by
  rw [Iic_eq_cons_Iio, Iic_eq_cons_Iio, map_cons]
  simp only [Iio_castSucc, cons_eq_insert, castSuccEmb_apply]

@[simp]
theorem Ici_succ (i : Fin n) : Ici i.succ = (Ici i).map (Fin.succEmb _) := by
  rw [Ici_eq_cons_Ioi, Ici_eq_cons_Ioi, map_cons]
  simp only [Ioi_succ, cons_eq_insert, coe_succEmb]

end Interval

end Fin
