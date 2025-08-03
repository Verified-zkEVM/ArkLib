import ArkLib.Data.CNat.LevelOne

/-!
# Level Two of the Cayley Hierarchy for Natural Numbers: CNat₂

This file defines `CNat₂`, the second level of the Cayley transformation hierarchy.
`CNat₂` has the property that multiplication becomes definitionally associative.

`CNat₂` is defined as `Cayley CNat`.
-/

/-- `CNat₂` is `Cayley CNat`. -/
abbrev CNat₂ := Cayley CNat

namespace CNat₂

/-- Evaluation function for `CNat₂`. -/
def toNat (c : CNat₂) : Nat := CNat.toNat (Cayley.toT c)

/-- `0` is the identity function on `CNat`. -/
@[inline] def zero : CNat₂ := Cayley.zero

/-- `1` is the successor function on `CNat`. -/
@[inline] def one : CNat₂ := Cayley.one

/-- Addition on `CNat₂` is function composition. -/
@[inline] def add : CNat₂ → CNat₂ → CNat₂ := Cayley.add

/-- Subtraction for `CNat₂`. -/
@[inline] def sub : CNat₂ → CNat₂ → CNat₂ := Cayley.sub CNat.toNat

/-- Multiplication for `CNat₂`. -/
@[inline] def mul : CNat₂ → CNat₂ → CNat₂ := Cayley.mul CNat.toNat

/-- Division for `CNat₂`. -/
@[inline] def div : CNat₂ → CNat₂ → CNat₂ := Cayley.div CNat.toNat

/-- Exponentiation for `CNat₂`. -/
@[inline] def pow : CNat₂ → CNat₂ → CNat₂ := Cayley.pow CNat.toNat

/-- Successor for `CNat₂`. -/
@[inline] def succ : CNat₂ → CNat₂ := Cayley.succ

/-- Predecessor for `CNat₂`. -/
@[inline] def pred : CNat₂ → CNat₂ := Cayley.pred CNat.toNat

/-- Less than for `CNat₂`. -/
def lt : CNat₂ → CNat₂ → Prop := Cayley.lt CNat.toNat

/-- Less than or equal for `CNat₂`. -/
def le : CNat₂ → CNat₂ → Prop := Cayley.le CNat.toNat

/-- Minimum for `CNat₂`. -/
def min : CNat₂ → CNat₂ → CNat₂ := Cayley.min CNat.toNat

/-- Maximum for `CNat₂`. -/
def max : CNat₂ → CNat₂ → CNat₂ := Cayley.max CNat.toNat

/-- Convert a `k : Nat` into a `CNat₂` via the hierarchy. -/
@[inline] def ofNat (k : Nat) : CNat₂ :=
  -- Convert Nat → CNat → CNat₂
  ⟨fun c => CNat.add c (CNat.ofNat k), by
    intro c
    simp [CNat.add]
    exact c.toFun_succ (CNat.ofNat k).toFun⟩

-- Typeclass instances

instance : Zero CNat₂ := ⟨zero⟩
instance : One CNat₂ := ⟨one⟩
instance : Add CNat₂ := ⟨add⟩
instance : Sub CNat₂ := ⟨sub⟩
instance : Mul CNat₂ := ⟨mul⟩
instance : Div CNat₂ := ⟨div⟩
instance : Pow CNat₂ CNat₂ := ⟨pow⟩

instance : HasPred CNat₂ where
  pred := pred

instance : LT CNat₂ where
  lt := lt

instance : LE CNat₂ where
  le := le

instance : Min CNat₂ where
  min := min

instance : Max CNat₂ where
  max := max

instance : DecidableEq CNat₂ := by
  intro a b
  by_cases h : toNat a = toNat b
  · right
    ext t
    -- This needs more work to prove properly
    sorry
  · left
    intro heq
    exact h (by rw [heq])

-- Definitional equality theorems

/-- `a + 0 = a` holds definitionally. -/
@[simp] theorem add_zero {a : CNat₂} : a + 0 = a := rfl

/-- `0 + a = a` holds definitionally. -/
@[simp] theorem zero_add {a : CNat₂} : 0 + a = a := rfl

/-- Addition is definitionally associative. -/
theorem add_assoc (a b c : CNat₂) : (a + b) + c = a + (b + c) := rfl

/-- `a * 0 = 0` holds definitionally. -/
@[simp] theorem mul_zero {a : CNat₂} : a * 0 = 0 := rfl

/-- `a * 1 = a` holds definitionally. -/
@[simp] theorem mul_one {a : CNat₂} : a * 1 = a := rfl

/-- Multiplication is definitionally associative at this level. -/
theorem mul_assoc (a b c : CNat₂) : (a * b) * c = a * (b * c) := rfl

-- Propositional theorems (mirroring the pattern from LevelOne)

/-- `0 * a = 0` holds only propositionally. -/
theorem zero_mul {a : CNat₂} : 0 * a = 0 := by
  change mul zero a = zero
  ext n
  simp [mul, zero]
  induction h : a.toNat with
  | zero => simp [zero, Cayley.mulAux, toNat]
  | succ n ih => simp [Cayley.mulAux, toNat, ih, h]; sorry

/-- `1 * a = a` holds only propositionally. -/
@[simp] theorem one_mul {a : CNat₂} : 1 * a = a := by
  change mul one a = a
  ext n
  simp [mul, one]
  induction h : a.toNat with
  | zero => simp [zero, Cayley.mulAux, toNat]; simp [toNat] at h; sorry
  | succ n ih => simp [Cayley.mulAux, toNat, ih, h]; sorry

/-- `(succ a) * b = a * b + b` holds only propositionally. -/
theorem succ_mul {a b : CNat₂} : (succ a) * b = a * b + b := by sorry

/-- `a * (b + c) = a * b + a * c` holds only propositionally. -/
theorem mul_add {a b c : CNat₂} : a * (b + c) = a * b + a * c := by sorry

/-- `toNat` commutes with successor. -/
@[simp] theorem toNat_succ (t : CNat₂) : toNat (succ t) = (toNat t).succ := by
  simp [succ, toNat, add, one]

/-- Extensionality theorem for `CNat₂`. -/
@[ext]
theorem ext' {a b : CNat₂} (h : (Cayley.toT a).toFun 0 = (Cayley.toT b).toFun 0) : a = b := by
  ext m
  induction m using CNat.toNat.induct with
  | h₀ => simp [h]
  | succ m ih => simp [ih]; sorry

/-- `ofNat` commutes with successor. -/
@[simp] theorem ofNat_succ (n : Nat) : ofNat n.succ = succ (ofNat n) := by
  ext
  simp [ofNat, succ, one, add]
  sorry

/-- `toNat` turns composition into addition. -/
@[simp] theorem toNat_add (a b : CNat₂) : toNat (add a b) = toNat a + toNat b := by
  simp [toNat, add]
  sorry

/-- `toNat` turns multiplication into multiplication. -/
private theorem toNat_mulAux (a : CNat₂) (k : Nat) : toNat (Cayley.mulAux a k) = toNat a * k := by
  induction k with
  | zero => simp [Cayley.mulAux, toNat, zero]
  | succ k ih => sorry

@[simp] theorem toNat_mul (a b : CNat₂) : toNat (mul a b) = toNat a * toNat b := by
  dsimp [mul]
  exact toNat_mulAux a (toNat b)

/-- `ofNat` respects addition. -/
@[simp] theorem ofNat_add (n m : Nat) : ofNat (n + m) = add (ofNat n) (ofNat m) := by
  ext
  simp [ofNat, add]
  sorry

/-- `toNat` is the left inverse of `ofNat`. -/
@[simp] theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n := by
  simp [toNat, ofNat]
  sorry

/-- `ofNat` is the right inverse of `toNat`. -/
@[simp] theorem ofNat_toNat (t : CNat₂) : ofNat (toNat t) = t := by
  ext
  simp [ofNat, toNat]
  sorry

/-- The explicit equivalence `Nat ≃ CNat₂`. -/
@[simps] def equivNat : Nat ≃ CNat₂ where
  toFun := ofNat
  invFun := toNat
  left_inv := by
    intro n; simp
  right_inv := by
    intro t; simp

/-- The less-than relation is well-defined. -/
theorem lt_iff_toNat_lt (a b : CNat₂) : a < b ↔ toNat a < toNat b := by
  rfl

/-- The less-equal relation is well-defined. -/
theorem le_iff_toNat_le (a b : CNat₂) : a ≤ b ↔ toNat a ≤ toNat b := by
  rfl

end CNat₂
