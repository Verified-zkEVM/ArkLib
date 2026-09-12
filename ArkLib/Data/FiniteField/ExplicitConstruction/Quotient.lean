/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.ModularInverse
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Stored arithmetic over a current coefficient field

Canonical representatives reuse `PolynomialQuotient.reduce` and its extended-gcd inverse.
The modulus is supplied and certified monic. Irreducibility is a separate explicit boundary:
this file does not yet search for an irreducible polynomial or choose an extension degree.
No enumeration of the coefficient field is used by these operations.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction

open CompPoly CompPoly.CPolynomial PolynomialQuotient

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]
variable (m : CPolynomial F) [Fact m.monic]

/-- Stored representatives fixed by the existing monic quotient reduction. -/
abbrev Carrier := {p : CPolynomial F // PolynomialQuotient.reduce m p = p}

/-- Canonicalize stored coefficient data modulo the supplied monic polynomial. -/
def canonical (p : CPolynomial F) : Carrier m :=
  ⟨reduce m p, reduce_idempotent Fact.out p⟩

instance : DecidableEq (Carrier m) := by
  letI : DecidableEq F := instDecidableEqOfLawfulBEq
  infer_instance

instance : BEq (Carrier m) := ⟨fun p q => decide (p = q)⟩
instance : LawfulBEq (Carrier m) where
  eq_of_beq := by intro p q h; exact of_decide_eq_true h
  rfl := by intro p; exact decide_eq_true rfl

omit [Fact m.monic] in
@[ext] theorem ext (p q : Carrier m) (h : p.val = q.val) : p = q := Subtype.ext h

@[simp] theorem canonical_val (p : Carrier m) : canonical m p.val = p :=
  Subtype.ext p.property

theorem canonical_surjective : Function.Surjective (canonical m) :=
  fun p => ⟨p.val, canonical_val m p⟩

instance : Zero (Carrier m) := ⟨canonical m 0⟩
instance : One (Carrier m) := ⟨canonical m 1⟩
instance : Add (Carrier m) := ⟨fun p q => canonical m (p.val + q.val)⟩
instance : Mul (Carrier m) := ⟨fun p q => canonical m (p.val * q.val)⟩
instance : Neg (Carrier m) := ⟨fun p => canonical m (-p.val)⟩
instance : Sub (Carrier m) := ⟨fun p q => p + -q⟩
instance : NatCast (Carrier m) := ⟨fun n => canonical m n⟩
instance : IntCast (Carrier m) := ⟨fun n => canonical m n⟩
instance : SMul ℕ (Carrier m) := ⟨nsmulRec⟩
instance : SMul ℤ (Carrier m) := ⟨zsmulRec⟩
instance : Pow (Carrier m) ℕ := ⟨fun p n => npowRec n p⟩

@[simp] theorem canonical_zero : canonical m 0 = (0 : Carrier m) := rfl
@[simp] theorem canonical_one : canonical m 1 = (1 : Carrier m) := rfl

private theorem poly_remainder_idempotent (p : Polynomial F) :
    (p %ₘ m.toPoly) %ₘ m.toPoly = p %ₘ m.toPoly :=
  (Polynomial.modByMonic_eq_self_iff ((monic_toPoly_iff m).mp Fact.out)).mpr
    (Polynomial.degree_modByMonic_lt _ ((monic_toPoly_iff m).mp Fact.out))

@[simp] theorem canonical_add (p q : CPolynomial F) :
    canonical m (p + q) = (canonical m p + canonical m q : Carrier m) := by
  apply ext
  change reduce m (p + q) = reduce m (reduce m p + reduce m q)
  apply toPoly_injective
  simp only [reduce, modByMonic_toPoly_eq_modByMonic _ _ Fact.out, toPoly_add]
  rw [Polynomial.add_modByMonic, Polynomial.add_modByMonic,
    poly_remainder_idempotent, poly_remainder_idempotent]

@[simp] theorem canonical_mul (p q : CPolynomial F) :
    canonical m (p * q) = (canonical m p * canonical m q : Carrier m) := by
  apply ext
  change reduce m (p * q) = reduce m (reduce m p * reduce m q)
  apply toPoly_injective
  simp only [reduce, modByMonic_toPoly_eq_modByMonic _ _ Fact.out, toPoly_mul]
  exact Polynomial.mul_modByMonic _ _ _

@[simp] theorem canonical_neg (p : CPolynomial F) :
    canonical m (-p) = (-canonical m p : Carrier m) := by
  apply ext
  change reduce m (-p) = reduce m (-reduce m p)
  apply toPoly_injective
  simp only [reduce, modByMonic_toPoly_eq_modByMonic _ _ Fact.out, toPoly_neg]
  rw [Polynomial.neg_modByMonic, Polynomial.neg_modByMonic,
    poly_remainder_idempotent]

@[simp] theorem canonical_sub (p q : CPolynomial F) :
    canonical m (p - q) = (canonical m p - canonical m q : Carrier m) := by
  change canonical m (p - q) = canonical m p + -canonical m q
  rw [sub_eq_add_neg, canonical_add, canonical_neg]

theorem canonical_nsmul (n : ℕ) (p : CPolynomial F) :
    canonical m (n • p) = (n • canonical m p : Carrier m) := by
  change canonical m (n • p) = nsmulRec n (canonical m p)
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ n ih => rw [succ_nsmul, canonical_add, ih]; rfl

theorem canonical_zsmul (n : ℤ) (p : CPolynomial F) :
    canonical m (n • p) = (n • canonical m p : Carrier m) := by
  change canonical m (n • p) = zsmulRec nsmulRec n (canonical m p)
  cases n with
  | ofNat n =>
    change canonical m ((n : ℤ) • p) = nsmulRec n (canonical m p)
    rw [natCast_zsmul]
    exact canonical_nsmul m n p
  | negSucc n =>
    simp only [negSucc_zsmul, canonical_neg, canonical_nsmul, zsmulRec]
    rfl

theorem canonical_pow (p : CPolynomial F) (n : ℕ) :
    canonical m (p ^ n) = (canonical m p ^ n : Carrier m) := by
  change canonical m (p ^ n) = npowRec n (canonical m p)
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, canonical_mul, ih]; rfl

instance : CommRing (Carrier m) :=
  (canonical_surjective m).commRing (canonical m) (canonical_zero m) (canonical_one m)
    (canonical_add m) (canonical_mul m) (canonical_neg m) (canonical_sub m)
    (canonical_nsmul m) (canonical_zsmul m) (canonical_pow m) (fun _ => rfl) (fun _ => rfl)

/-- Executable quotient projection on stored polynomials. -/
def projection : CPolynomial F →+* Carrier m where
  toFun := canonical m
  map_zero' := canonical_zero m
  map_one' := canonical_one m
  map_add' := canonical_add m
  map_mul' := canonical_mul m

/-- Coefficient embedding over the current field, which need not be a prime field. -/
def embedding : F →+* Carrier m := (projection m).comp CHom

/-- The stored image of a coefficient. -/
def embed (a : F) : Carrier m := embedding m a

/-- Canonical extended-gcd inversion; `none` explicitly reports a nonunit. -/
def inverse? (a : Carrier m) : Option (Carrier m) :=
  (inverseMod? a.val m).map (canonical m)

/-- Every stored element has degree below the modulus. -/
theorem degree_lt (a : Carrier m) : a.val.toPoly.degree < m.toPoly.degree := by
  rw [← a.property]
  exact degree_reduce_lt Fact.out _

/-- Every returned inverse obeys the actual stored multiplication equation. -/
theorem mul_inverse?_eq_one {a b : Carrier m} (h : inverse? m a = some b) : a * b = 1 := by
  obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp h
  change a * canonical m v = canonical m 1
  rw [← canonical_val m a, ← canonical_mul]
  apply ext
  exact inverseMod?_mul_modByMonic Fact.out hv

/-- The representation agrees with the existing proof-facing polynomial quotient. -/
noncomputable def semantics : Carrier m →+* ModAlgebra m :=
  { toFun := fun a => quotientHom m a.val
    map_zero' := by
      change quotientHom m (reduce m 0) = 0
      rw [quotientHom_reduce Fact.out, map_zero]
    map_one' := by
      change quotientHom m (reduce m 1) = 1
      rw [quotientHom_reduce Fact.out, map_one]
    map_add' := by
      intro a b
      change quotientHom m (reduce m (a.val + b.val)) = _
      rw [quotientHom_reduce Fact.out, map_add]
    map_mul' := by
      intro a b
      change quotientHom m (reduce m (a.val * b.val)) = _
      rw [quotientHom_reduce Fact.out, map_mul] }

/-- Irreducibility ensures the xgcd guard succeeds on each nonzero canonical element. -/
theorem inverse?_exists_of_irreducible (hm : Irreducible m.toPoly)
    {a : Carrier m} (ha : a ≠ 0) : ∃ b, inverse? m a = some b := by
  have haPoly : a.val.toPoly ≠ 0 := by
    intro hz
    have hv : a.val = 0 := toPoly_injective (by simpa only [toPoly_zero] using hz)
    apply ha
    rw [← canonical_val m a, hv]
    rfl
  have hcoprime : IsCoprime a.val.toPoly m.toPoly := by
    apply IsCoprime.symm
    apply hm.coprime_iff_not_dvd.mpr
    intro hd
    exact (not_le_of_gt (degree_lt m a)) (Polynomial.degree_le_of_dvd hd haPoly)
  obtain ⟨v, hv⟩ := (inverseMod_exists_iff_coprime a.val m).mpr hcoprime
  exact ⟨canonical m v, by simp [inverse?, hv]⟩

/-- Total executable inverse, with the standard zero convention. The failure default is
unreachable on nonzero inputs once irreducibility is certified. -/
def inverse (a : Carrier m) : Carrier m :=
  if a == 0 then 0 else (inverse? m a).getD 0

theorem inverse_zero : inverse m (0 : Carrier m) = 0 := by simp [inverse]

theorem mul_inverse (hm : Irreducible m.toPoly) {a : Carrier m} (ha : a ≠ 0) :
    a * inverse m a = 1 := by
  obtain ⟨b, hb⟩ := inverse?_exists_of_irreducible m hm ha
  simpa [inverse, beq_iff_eq, ha, hb] using mul_inverse?_eq_one m hb

/-- Positive modulus degree preserves scalar coefficients literally. -/
theorem embed_val (hm : 0 < m.toPoly.degree) (a : F) : (embed m a).val = C a := by
  apply toPoly_injective
  change (reduce m (C a)).toPoly = (C a).toPoly
  rw [reduce, modByMonic_toPoly_eq_modByMonic _ _ Fact.out, toPoly_C]
  exact (Polynomial.modByMonic_eq_self_iff ((monic_toPoly_iff m).mp Fact.out)).mpr
    (lt_of_le_of_lt Polynomial.degree_C_le hm)

/-- The coefficient field embeds injectively; no prime-field restriction is needed. -/
theorem embedding_injective (hm : 0 < m.toPoly.degree) :
    Function.Injective (embedding m) := by
  intro a b hab
  have h := congrArg Subtype.val hab
  change (embed m a).val = (embed m b).val at h
  rw [embed_val m hm, embed_val m hm] at h
  have hpoly := congrArg CPolynomial.toPoly h
  simpa only [toPoly_C, Polynomial.coeff_C_zero] using
    congrArg (fun p : Polynomial F => p.coeff 0) hpoly

instance [Fact (Irreducible m.toPoly)] : Nontrivial (Carrier m) :=
  (embedding_injective m (Polynomial.degree_pos_of_irreducible Fact.out)).nontrivial

instance : Inv (Carrier m) := ⟨inverse m⟩

instance [Fact (Irreducible m.toPoly)] : Field (Carrier m) where
  div a b := a * inverse m b
  div_eq_mul_inv := fun _ _ => rfl
  zpow := zpowRec
  zpow_zero' := fun _ => rfl
  zpow_succ' := fun _ _ => rfl
  zpow_neg' := fun _ _ => rfl
  mul_inv_cancel := fun _ h => mul_inverse m Fact.out h
  inv_zero := inverse_zero m
  nnqsmul := _
  qsmul := _

end ArkLib.FiniteField.ExplicitConstruction
