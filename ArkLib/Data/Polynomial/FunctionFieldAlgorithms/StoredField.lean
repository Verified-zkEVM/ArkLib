/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.StoredFraction

/-!
# Executable field of stored rational functions

This computational quotient reuses `Fraction` representatives and Mathlib's
`RatFunc` semantics. Equality tests polynomial cross products. Arithmetic lifts
stored operations directly, cancelling polynomial gcds after addition and
multiplication; no representative is extracted by classical choice.
The noncomputable semantic map occurs only in correctness proofs.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.StoredField

open CompPoly CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- A stored numerator and certified nonzero polynomial denominator. -/
abbrev Representative (F : Type*) [Field F] [BEq F] [LawfulBEq F] :=
  {a : Fraction F // a.Valid}

/-- Computable equality of fractions by cross multiplication. -/
def Related (a b : Representative F) : Prop :=
  a.val.num * b.val.den = b.val.num * a.val.den

/-- Cross multiplication is precisely equality in the existing function field. -/
theorem related_iff_value (a b : Representative F) :
    Related a b ↔ a.val.value = b.val.value := by
  rw [Fraction.value, Fraction.value,
    div_eq_div_iff (RatFunc.algebraMap_ne_zero a.property)
      (RatFunc.algebraMap_ne_zero b.property)]
  rw [← map_mul, ← map_mul, (RatFunc.algebraMap_injective F).eq_iff]
  exact ⟨fun h => by rw [← toPoly_mul, ← toPoly_mul]; exact congrArg CPolynomial.toPoly h,
    fun h => by
      apply toPolyLinearEquiv.injective
      simpa only [toPolyLinearEquiv_apply, toPoly_mul] using h⟩

instance representativeSetoid : Setoid (Representative F) where
  r := Related
  iseqv := ⟨fun a => (related_iff_value a a).mpr rfl,
    fun h => (related_iff_value _ _).mpr ((related_iff_value _ _).mp h).symm,
    fun h₁ h₂ => (related_iff_value _ _).mpr
      (((related_iff_value _ _).mp h₁).trans ((related_iff_value _ _).mp h₂))⟩

/-- Rational-function coefficients whose runtime values are stored fractions. -/
def Carrier (F : Type*) [Field F] [BEq F] [LawfulBEq F] :=
  Quotient (representativeSetoid (F := F))

/-- Inject a valid stored fraction into the computational field. -/
def ofFraction (a : Fraction F) (ha : a.Valid) : Carrier F := Quotient.mk _ ⟨a, ha⟩

/-- Interpret the computational quotient in Mathlib's function field. -/
noncomputable def value : Carrier F → RatFunc F :=
  Quotient.lift (fun a => a.val.value) (fun a b h => (related_iff_value a b).mp h)

@[simp] theorem value_ofFraction (a : Fraction F) (ha : a.Valid) :
    value (ofFraction a ha) = a.value := rfl

/-- The interpretation identifies exactly equivalent stored representatives. -/
theorem value_injective : Function.Injective (value (F := F)) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      intro h
      exact Quotient.sound ((related_iff_value a b).mpr h)

instance : DecidableRel (Related (F := F)) := fun a b =>
  decidable_of_iff (a.val.num * b.val.den == b.val.num * a.val.den) beq_iff_eq

instance : DecidableEq (Carrier F) := by
  letI : DecidableRel (fun a b : Representative F => a ≈ b) :=
    fun a b => inferInstanceAs (Decidable (Related a b))
  exact Quotient.decidableEq
instance : BEq (Carrier F) := ⟨fun a b => decide (a = b)⟩
instance : LawfulBEq (Carrier F) where
  eq_of_beq := of_decide_eq_true
  rfl := by intro a; exact decide_eq_true rfl

/-- Lift a stored operation with a proof that it preserves equivalence. -/
def liftUnary (op : Fraction F → Fraction F)
    (valid : ∀ a : Representative F, (op a.val).Valid)
    (respect : ∀ a b : Representative F, a.val.value = b.val.value →
      (op a.val).value = (op b.val).value) : Carrier F → Carrier F :=
  Quotient.lift (fun a => ofFraction (op a.val) (valid a)) (by
    intro a b h
    exact value_injective (respect a b ((related_iff_value a b).mp h)))

/-- Lift binary stored arithmetic with a proof that it preserves equivalence. -/
def liftBinary (op : Fraction F → Fraction F → Fraction F)
    (valid : ∀ a b : Representative F, (op a.val b.val).Valid)
    (respect : ∀ a b c d : Representative F,
      a.val.value = c.val.value → b.val.value = d.val.value →
      (op a.val b.val).value = (op c.val d.val).value) :
    Carrier F → Carrier F → Carrier F :=
  Quotient.lift₂ (fun a b => ofFraction (op a.val b.val) (valid a b)) (by
    intro a b c d hac hbd
    exact value_injective
      (respect a b c d ((related_iff_value a c).mp hac) ((related_iff_value b d).mp hbd)))

/-- Embed an existing stored polynomial as a rational function. -/
def ofPolynomial (p : CPolynomial F) : Carrier F :=
  ofFraction (Fraction.ofPolynomial p) (Fraction.valid_ofPolynomial p)

instance : Zero (Carrier F) := ⟨ofPolynomial 0⟩
instance : One (Carrier F) := ⟨ofPolynomial 1⟩
instance : Add (Carrier F) := ⟨liftBinary (fun a b => (a.add b).cancelGcd)
  (fun a b => Fraction.valid_cancelGcd (Fraction.valid_add a.property b.property)) (by
    intro a b c d hac hbd
    rw [Fraction.value_cancelGcd (Fraction.valid_add a.property b.property),
      Fraction.value_cancelGcd (Fraction.valid_add c.property d.property),
      Fraction.value_add a.property b.property,
      Fraction.value_add c.property d.property, hac, hbd])⟩
instance : Mul (Carrier F) := ⟨liftBinary (fun a b => (a.mul b).cancelGcd)
  (fun a b => Fraction.valid_cancelGcd (Fraction.valid_mul a.property b.property)) (by
    intro a b c d hac hbd
    rw [Fraction.value_cancelGcd (Fraction.valid_mul a.property b.property),
      Fraction.value_cancelGcd (Fraction.valid_mul c.property d.property),
      Fraction.value_mul, Fraction.value_mul, hac, hbd])⟩
instance : Neg (Carrier F) := ⟨liftUnary Fraction.neg (fun a => a.property) (by
  intro a b h
  rw [Fraction.value_neg, Fraction.value_neg, h])⟩
instance : Inv (Carrier F) := ⟨liftUnary Fraction.inv
  (fun a => Fraction.valid_inv a.val) (by
    intro a b h
    rw [Fraction.value_inv, Fraction.value_inv, h])⟩
instance : Sub (Carrier F) := ⟨fun a b => a + -b⟩
instance : Div (Carrier F) := ⟨fun a b => a * b⁻¹⟩
instance : NatCast (Carrier F) := ⟨fun n => ofPolynomial (CPolynomial.C (n : F))⟩
instance : IntCast (Carrier F) := ⟨fun n => ofPolynomial (CPolynomial.C (n : F))⟩
instance : SMul ℕ (Carrier F) := ⟨nsmulRec⟩
instance : SMul ℤ (Carrier F) := ⟨zsmulRec⟩
instance : Pow (Carrier F) ℕ := ⟨fun a n => npowRec n a⟩

@[simp] theorem value_ofPolynomial (p : CPolynomial F) :
    value (ofPolynomial p) = algebraMap (Polynomial F) (RatFunc F) p.toPoly :=
  Fraction.value_ofPolynomial p

@[simp] theorem value_zero : value (0 : Carrier F) = 0 := by
  change value (ofPolynomial 0) = 0
  rw [value_ofPolynomial, toPoly_zero, map_zero]

@[simp] theorem value_one : value (1 : Carrier F) = 1 := by
  change value (ofPolynomial 1) = 1
  rw [value_ofPolynomial, toPoly_one, map_one]

@[simp] theorem value_add (a b : Carrier F) : value (a + b) = value a + value b := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      exact (Fraction.value_cancelGcd (Fraction.valid_add a.property b.property)).trans
        (Fraction.value_add a.property b.property)

@[simp] theorem value_mul (a b : Carrier F) : value (a * b) = value a * value b := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      exact (Fraction.value_cancelGcd (Fraction.valid_mul a.property b.property)).trans
        (Fraction.value_mul a.val b.val)

@[simp] theorem value_neg (a : Carrier F) : value (-a) = -value a := by
  induction a using Quotient.inductionOn with
  | h a => exact Fraction.value_neg a.val

@[simp] theorem value_inv (a : Carrier F) : value a⁻¹ = (value a)⁻¹ := by
  induction a using Quotient.inductionOn with
  | h a => exact Fraction.value_inv a.val

@[simp] theorem value_sub (a b : Carrier F) : value (a - b) = value a - value b := by
  change value (a + -b) = _
  rw [value_add, value_neg, sub_eq_add_neg]

@[simp] theorem value_div (a b : Carrier F) : value (a / b) = value a / value b := by
  change value (a * b⁻¹) = _
  rw [value_mul, value_inv, div_eq_mul_inv]

theorem value_nsmul (n : ℕ) (a : Carrier F) : value (n • a) = n • value a := by
  change value (nsmulRec n a) = _
  induction n with
  | zero => simpa only [nsmulRec, zero_nsmul] using (value_zero (F := F))
  | succ n ih => simpa only [nsmulRec, value_add, ih] using (succ_nsmul (value a) n).symm

theorem value_zsmul (n : ℤ) (a : Carrier F) : value (n • a) = n • value a := by
  cases n with
  | ofNat n => exact (value_nsmul n a).trans (natCast_zsmul (value a) n).symm
  | negSucc n =>
    change value (-nsmulRec (n + 1) a) = _
    rw [value_neg]
    exact congrArg Neg.neg (value_nsmul (n + 1) a) |>.trans (negSucc_zsmul (value a) n).symm

theorem value_pow (a : Carrier F) (n : ℕ) : value (a ^ n) = value a ^ n := by
  change value (npowRec n a) = _
  induction n with
  | zero => exact value_one
  | succ n ih => simpa only [npowRec, value_mul, ih] using (pow_succ (value a) n).symm

@[simp] theorem value_natCast (n : ℕ) : value (n : Carrier F) = n := by
  change value (ofPolynomial (CPolynomial.C (n : F))) = _
  rw [value_ofPolynomial, C_toPoly, Polynomial.C_eq_natCast, map_natCast]

@[simp] theorem value_intCast (n : ℤ) : value (n : Carrier F) = n := by
  change value (ofPolynomial (CPolynomial.C (n : F))) = _
  rw [value_ofPolynomial, C_toPoly, Polynomial.C_eq_intCast, map_intCast]

instance : CommRing (Carrier F) :=
  fast_instance% value_injective.commRing value value_zero value_one value_add value_mul value_neg
    value_sub value_nsmul value_zsmul value_pow value_natCast value_intCast

instance : Nontrivial (Carrier F) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hv := congrArg (value (F := F)) h
  rw [value_zero, value_one] at hv
  exact zero_ne_one hv

instance : Field (Carrier F) where
  __ := (inferInstance : CommRing (Carrier F))
  inv := Inv.inv
  div := HDiv.hDiv
  div_eq_mul_inv := fun _ _ => rfl
  mul_inv_cancel a ha := value_injective (by
    rw [value_mul, value_inv, value_one]
    exact mul_inv_cancel₀ (fun h => ha (value_injective (h.trans value_zero.symm))))
  inv_zero := value_injective (by rw [value_inv, value_zero, inv_zero])
  nnqsmul := _
  qsmul := _

/-- The semantic interpretation is an injective field homomorphism. -/
noncomputable def valueHom : Carrier F →+* RatFunc F where
  toFun := value
  map_zero' := value_zero
  map_one' := value_one
  map_add' := value_add
  map_mul' := value_mul

end Polynomial.FunctionFieldAlgorithms.StoredField
