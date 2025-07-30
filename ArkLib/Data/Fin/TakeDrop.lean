/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.Basic

/-!
# Take and Drop for `Fin` tuples

Note that `Fin.take` is already in mathlib. In this file, we define:
- `Fin.rtake m h v` for taking the last `m` elements of a `Fin n` tuple `v`, where `h : m ≤ n`
- `Fin.drop m h v` for dropping the first `m` elements of a `Fin n` tuple `v`, where `h : m ≤ n`
- `Fin.rdrop m h v` for dropping the last `m` elements of a `Fin n` tuple `v`, where `h : m ≤ n`

We also prove some properties of these functions.
-/

universe u v

namespace Fin

variable {n : ℕ} {α : Fin n → Sort u}

theorem take_addCases'_left {n' : ℕ} {β : Fin n' → Sort u} (m : ℕ) (h : m ≤ n)
    (u : (i : Fin n) → α i) (v : (j : Fin n') → β j) (i : Fin m) :
    take m (Nat.le_add_right_of_le h) (addCases' u v) i =
      (append_left α β (castLE h i)) ▸ (take m h u i) := by
  have : i < n := Nat.lt_of_lt_of_le i.isLt h
  simp [take_apply, addCases', addCases, this, cast_eq_iff_heq, castLE]

-- theorem take_addCases'_right {n' : ℕ} {β : Fin n' → Sort u} (m : ℕ) (h : m ≤ n')
--     (u : (i : Fin n) → α i) (v : (j : Fin n') → β j) (i : Fin (n + m)) :
--       take (n + m) (Nat.add_le_add_left h n) (addCases' u v) i =
--         addCases' u (take m h v) i := by
--   have : i < n := Nat.lt_of_lt_of_le i.isLt h
--   simp [take_apply, addCases', addCases, this, cast_eq_iff_heq, castLT, castLE]
--   have {i : Fin m} : castLE (Nat.le_add_right_of_le h) i = natAdd n (castLE h i) := by congr
--   refine (Fin.heq_fun_iff' rfl (fun i => ?_)).mpr (fun i => ?_)
--   · sorry
--     simp only [append_right, cast_eq_self]
--   · rw [take, this]
--     simp [addCases_right]

/-- Take the last `m` elements of a finite vector -/
def rtake (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    (i : Fin m) → α (Fin.cast (Nat.sub_add_cancel h) (natAdd (n - m) i)) :=
  fun i => v (Fin.cast (Nat.sub_add_cancel h) (natAdd (n - m) i))

@[simp]
theorem rtake_apply (v : (i : Fin n) → α i) (m : ℕ) (h : m ≤ n)
    (i : Fin m) : rtake m h v i = v (Fin.cast (Nat.sub_add_cancel h) (natAdd (n - m) i)) := rfl

@[simp]
theorem rtake_zero {n : ℕ} {α : Sort u} (v : Fin n → α) :
    rtake 0 (by omega) v = fun i => Fin.elim0 i := by ext i; exact Fin.elim0 i

@[simp]
theorem rtake_self {n : ℕ} {α : Sort u} (v : Fin n → α) :
    rtake n (by omega) v = v := by ext i; simp [rtake, Fin.natAdd]

-- @[simp]
-- theorem rtake_succ {n : ℕ} {α : Sort u} (v : Fin n → α) (m : Fin (n + 1)) :
--     rtake v (Fin.succ m) = Fin.addCases (v (Fin.cast (by omega) (Fin.natAdd (n - m) m)))
--       (rtake (v ∘ Fin.succ) m) := by
--   ext i <;> simp [rtake, Fin.natAdd]

-- @[simp]
-- theorem rtake_eq_take_rev {n : ℕ} {α : Sort u} (v : Fin n → α) (m : Fin (n + 1)) :
--     rtake v m = take v m ∘ Fin.rev := by
--   ext i
--   simp [rtake, take, Fin.natAdd, Fin.cast, Fin.rev]
--   congr;

-- @[simp]
-- theorem take_rtake_append {n : ℕ} {α : Sort u} (v : Fin n → α) (m : Fin (n + 1)) :
--     fun i => Fin.addCases (take v m) (rtake v (n - m)) i = v := by
--   ext i
--   refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [take, rtake]
--   · exact v j
--   · exact v (Fin.addNat j (n - m))

/-
* `Fin.drop`: Given `h : m ≤ n`, `Fin.drop m h v` for a `n`-tuple `v = (v 0, ..., v (n - 1))` is the
  `(n - m)`-tuple `(v m, ..., v (n - 1))`.
-/
section Drop

/-- Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. -/
def drop (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    (i : Fin (n - m)) → α (Fin.cast (Nat.sub_add_cancel h) (addNat i m)) :=
  fun i ↦ v (Fin.cast (Nat.sub_add_cancel h) (addNat i m))

@[simp]
theorem drop_apply (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) (i : Fin (n - m)) :
    (drop m h v) i = v (Fin.cast (Nat.sub_add_cancel h) (addNat i m)) := rfl

@[simp]
theorem drop_zero (v : (i : Fin n) → α i) : drop 0 n.zero_le v = v := by
  ext i
  simp only [Nat.sub_zero, Nat.add_zero, addNat, Fin.eta, cast_eq_self, drop_apply]

@[simp]
theorem drop_one {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) :
    drop 1 (Nat.le_add_left 1 n) v = tail v := by
  ext i
  simp only [drop, tail]
  congr

@[simp]
theorem drop_of_succ {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) :
    drop n n.le_succ v = fun i => v (Fin.cast (Nat.sub_add_cancel n.le_succ) (addNat i n)) := by
  ext i
  simp only [drop]

@[simp]
theorem drop_all (v : (i : Fin n) → α i) :
    drop n n.le_refl v = fun i => Fin.elim0 (i.cast (Nat.sub_self n)) := by
  ext i
  simp at i
  exact Fin.elim0 i

-- @[simp]
-- theorem drop_all (v : (i : Fin n) → α i) :
--     HEq (drop n (le_refl n) v)
--       (fun (i : Fin 0) ↦
-- @elim0 (α (Fin.cast (Nat.sub_add_cancel (le_refl n)) (i.addNat n))) i) := by
--   sorry
--   refine (Fin.heq_fun_iff ?_).mpr ?_
--   · simp
--   · intro i

theorem drop_tail {α : Fin (n + 1) → Sort*} (m : ℕ) (h : m ≤ n) (v : (i : Fin (n + 1)) → α i) :
    HEq (drop m h (tail v)) (drop m.succ (Nat.succ_le_succ h) v) := by
  refine (Fin.heq_fun_iff' (Nat.succ_sub_succ_eq_sub n m).symm (fun i => by congr)).mpr ?_
  intro i
  simp [drop, tail]
  congr

theorem drop_repeat {α : Type*} {n' : ℕ} (m : ℕ) (h : m ≤ n) (a : Fin n' → α) :
    HEq (drop (m * n') (Nat.mul_le_mul_right n' h) (Fin.repeat n a)) (Fin.repeat (n - m) a) :=
  (Fin.heq_fun_iff (Nat.sub_mul n m n').symm).mpr (fun i => by simp [modNat])

/-- Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. -/
def rdrop (m : ℕ) (h : m ≤ n) (v : (i : Fin n) → α i) :
    (i : Fin (n - m)) → α (Fin.cast (Nat.sub_add_cancel h) (i.castAdd m)) :=
  fun i => v (Fin.cast (Nat.sub_add_cancel h) (i.castAdd m))

@[simp]
theorem rdrop_apply (v : (i : Fin n) → α i) (m : ℕ) (h : m ≤ n) (i : Fin (n - m)) :
    rdrop m h v i = v (Fin.cast (Nat.sub_add_cancel h) (i.castAdd m)) := rfl

@[simp]
theorem rdrop_zero (v : (i : Fin n) → α i) : rdrop 0 n.zero_le v = v := by
  ext i
  simp [Nat.sub_zero, Nat.add_zero, cast_eq_self, rdrop_apply]

@[simp]
theorem rdrop_all (v : (i : Fin n) → α i) :
    rdrop n n.le_refl v = fun i => Fin.elim0 (i.cast (Nat.sub_self n)) := by
  ext i
  simp at i
  exact Fin.elim0 i

@[simp]
theorem rdrop_one {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) :
    rdrop 1 (Nat.le_add_left 1 n) v = init v := by
  ext i
  simp only [rdrop, init]
  congr

@[simp]
theorem rdrop_of_succ {α : Fin (n + 1) → Sort*} (v : (i : Fin (n + 1)) → α i) :
    rdrop n n.le_succ v = fun i : Fin ((n + 1) - n) => v ((i.castAdd n).cast (by omega)) := by
  ext i
  simp only [rdrop]

end Drop

end Fin
