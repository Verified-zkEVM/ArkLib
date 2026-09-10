/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToCompPoly.Univariate.Basic
public import ArkLib.Data.Polynomial.GCDSplit
public import CompPoly.Univariate.Deriv
public import CompPoly.Univariate.EuclideanAlgorithm
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Polynomial.Radical

/-!
# Executable squarefree support of a finite-field polynomial

The zero-derivative branch of squarefree support extraction cannot discard the
polynomial: in positive characteristic it can be a nonconstant `p`-th power.
This file first supplies the executable inverse-Frobenius contraction needed by
that branch.  Unlike `PerfectRing.frobeniusEquiv`, the inverse below computes by
finite-field exponentiation.

The public `squarefreeSupport` recursively removes repeated factors, merges
overlapping recursive supports by a monic lcm, and normalizes the result.  For
every nonzero input it is monic, nonzero, squarefree, has no larger degree, and
has exactly the same roots after any coefficient-field extension.

The generic inverse-Frobenius kernel reads `Fintype.card F`. Computing that cardinality may
materialize the field enumeration, especially for extension fields. A fast decoder must replace
this metadata lookup with an explicit field size and its erased correctness proof. This module
proves exact squarefree support; its generic kernel does not establish a polynomial-bit bound.
-/

@[expose] public section

namespace CompPoly.CPolynomial

variable {F : Type*} [Field F] [Fintype F]
variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- In a field of size q and characteristic p, raising to q/p inverts Frobenius:
`(a^(q/p))^p = a^q = a`, since p divides q. The exponent also works at a=0. -/
def inverseFrobenius (a : F) : F :=
  a ^ (Fintype.card F / p)

@[simp] theorem inverseFrobenius_pow (a : F) :
    inverseFrobenius p a ^ p = a := by
  have hchar : ringChar F = p :=
    CharP.ringChar_of_prime_eq_zero Fact.out (CharP.cast_eq_zero F p)
  have hdiv : p ∣ Fintype.card F :=
    (prime_dvd_char_iff_dvd_card (R := F) p).mp (hchar ▸ dvd_rfl)
  rw [inverseFrobenius, ← pow_mul, Nat.div_mul_cancel hdiv]
  exact FiniteField.pow_card a

theorem inverseFrobenius_eq_frobeniusEquiv_symm (a : F) :
    inverseFrobenius p a = (frobeniusEquiv F p).symm a := by
  apply (frobeniusEquiv F p).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_def, inverseFrobenius_pow]

variable [BEq F] [LawfulBEq F]

/-- Compress exponents by the characteristic and apply inverse Frobenius to
the retained coefficients. This is the computable `p`-th root used when the
formal derivative vanishes. -/
def frobeniusContract (f : CPolynomial F) : CPolynomial F :=
  CPolynomial.ofArray <| Array.ofFn fun i : Fin (f.natDegree / p + 1) ↦
    inverseFrobenius p (f.coeff (i * p))

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem coeff_frobeniusContract (f : CPolynomial F) (i : ℕ) :
    (frobeniusContract p f).coeff i =
      if i < f.natDegree / p + 1 then
        inverseFrobenius p (f.coeff (i * p))
      else 0 := by
  rw [frobeniusContract, CPolynomial.coeff_ofArray]
  simp only [Array.getD, Array.size_ofFn]
  split <;> simp_all

theorem frobeniusContract_toPoly (f : CPolynomial F) :
    (frobeniusContract p f).toPoly =
      (Polynomial.contract p f.toPoly).map (frobeniusEquiv F p).symm.toRingHom := by
  ext i
  rw [← CPolynomial.coeff_toPoly, coeff_frobeniusContract,
    Polynomial.coeff_map, Polynomial.coeff_contract (Fact.out : Nat.Prime p).ne_zero]
  split_ifs with hi
  · rw [← CPolynomial.coeff_toPoly]
    exact inverseFrobenius_eq_frobeniusEquiv_symm p _
  · have hp : 0 < p := (Fact.out : Nat.Prime p).pos
    have hdegree : f.toPoly.natDegree < i * p := by
      apply (Nat.div_lt_iff_lt_mul hp).mp
      rw [← CPolynomial.natDegree_toPoly]
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdegree]
    simp

/-- When the derivative vanishes, executable contraction is an exact `p`-th
root. This is the kernel fact needed by the inseparable recursion branch. -/
theorem frobeniusContract_pow_eq (f : CPolynomial F)
    (hderiv : f.derivative = 0) : frobeniusContract p f ^ p = f := by
  apply toPoly_injective
  rw [toPoly_pow, frobeniusContract_toPoly]
  have hmap :
      ((Polynomial.contract p f.toPoly).map (frobeniusEquiv F p).symm.toRingHom).map
          (frobenius F p) = Polynomial.contract p f.toPoly := by
    rw [Polynomial.map_map]
    ext i
    simp
  rw [← Polynomial.map_frobenius_expand]
  rw [Polynomial.map_expand, hmap]
  apply Polynomial.expand_contract p
  · simpa only [derivative_toPoly, toPoly_zero] using congrArg CPolynomial.toPoly hderiv
  · exact (Fact.out : Nat.Prime p).ne_zero

theorem frobeniusContract_ne_zero {f : CPolynomial F} (hf : f ≠ 0)
    (hderiv : f.derivative = 0) : frobeniusContract p f ≠ 0 := by
  intro hcontract
  apply hf
  rw [← frobeniusContract_pow_eq p f hderiv, hcontract, zero_pow]
  exact (Fact.out : Nat.Prime p).ne_zero

theorem natDegree_frobeniusContract_lt {f : CPolynomial F} (hfDegree : 0 < f.natDegree)
    (hderiv : f.derivative = 0) : (frobeniusContract p f).natDegree < f.natDegree := by
  have hpow := congrArg (CPolynomial.toPoly (R := F))
    (frobeniusContract_pow_eq p f hderiv)
  rw [toPoly_pow] at hpow
  have hdegree := congrArg Polynomial.natDegree hpow
  rw [Polynomial.natDegree_pow, ← natDegree_toPoly, ← natDegree_toPoly] at hdegree
  have hpTwo : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  by_cases hc : (frobeniusContract p f).natDegree = 0
  · simpa [hc] using hfDegree
  · calc
      (frobeniusContract p f).natDegree < 2 * (frobeniusContract p f).natDegree :=
        by omega
      _ ≤ p * (frobeniusContract p f).natDegree := Nat.mul_le_mul_right _ hpTwo
      _ = f.natDegree := hdegree

theorem eval₂_frobeniusContract_eq_zero_iff
    {K : Type*} [Field K] (phi : F →+* K) (x : K) {f : CPolynomial F}
    (hderiv : f.derivative = 0) :
    (frobeniusContract p f).toPoly.eval₂ phi x = 0 ↔ f.toPoly.eval₂ phi x = 0 := by
  have hpow := congrArg (CPolynomial.toPoly (R := F))
    (frobeniusContract_pow_eq p f hderiv)
  rw [toPoly_pow] at hpow
  rw [← hpow, Polynomial.eval₂_pow,
    pow_eq_zero_iff (Fact.out : Nat.Prime p).ne_zero]

theorem frobeniusContract_monic {f : CPolynomial F} (hf : f.monic)
    (hderiv : f.derivative = 0) : (frobeniusContract p f).monic := by
  rw [monic_toPoly_iff]
  have hpow := congrArg (CPolynomial.toPoly (R := F))
    (frobeniusContract_pow_eq p f hderiv)
  rw [toPoly_pow] at hpow
  have hleading := congrArg Polynomial.leadingCoeff hpow
  rw [Polynomial.leadingCoeff_pow, ((monic_toPoly_iff f).mp hf).leadingCoeff] at hleading
  apply (frobeniusEquiv F p).injective
  simpa only [frobeniusEquiv_def, RingEquiv.coe_mk, Equiv.coe_fn_mk, map_one] using hleading

/-! ## Executable least common multiple -/

/-- Monic least common multiple computed using CompPoly gcd and monic division. -/
def lcmMonic (a b : CPolynomial F) : CPolynomial F :=
  (a * b).divByMonic (gcdMonic a b)

omit [Fintype F] in
theorem gcdMonic_mul_lcmMonic {a b : CPolynomial F} (ha : a ≠ 0) :
    gcdMonic a b * lcmMonic a b = a * b := by
  have hmonic : (gcdMonic a b).monic := gcdFactor_monic (e := b) ha
  have hdivision := modByMonic_add_mul_divByMonic (a * b) (gcdMonic a b) hmonic
  have hmod : (a * b).modByMonic (gcdMonic a b) = 0 := by
    apply toPoly_injective
    rw [modByMonic_toPoly_eq_modByMonic _ _ hmonic, toPoly_zero]
    apply Polynomial.modByMonic_eq_zero_iff_dvd ((monic_toPoly_iff _).mp hmonic) |>.2
    rw [toPoly_mul]
    exact (gcdFactor_dvd_left a b).mul_right b.toPoly
  simpa [lcmMonic, hmod] using hdivision

omit [Fintype F] in
theorem lcmMonic_toPoly_associated_lcm [DecidableEq F]
    {a b : CPolynomial F} (ha : a ≠ 0) :
    Associated (lcmMonic a b).toPoly (EuclideanDomain.lcm a.toPoly b.toPoly) := by
  have hfactor := congrArg (CPolynomial.toPoly (R := F))
    (gcdMonic_mul_lcmMonic (a := a) (b := b) ha)
  rw [toPoly_mul, toPoly_mul, gcdMonic_toPoly_eq_normalize_gcd] at hfactor
  have hproducts : Associated
      (normalize (EuclideanDomain.gcd a.toPoly b.toPoly) * (lcmMonic a b).toPoly)
      (EuclideanDomain.gcd a.toPoly b.toPoly *
        EuclideanDomain.lcm a.toPoly b.toPoly) := by
    apply Associated.of_eq
    rw [EuclideanDomain.gcd_mul_lcm, hfactor]
  apply Associated.of_mul_left hproducts (normalize_associated _)
  intro hnormalize
  have hgcd := normalize_eq_zero.mp hnormalize
  exact ha ((toPoly_eq_zero_iff a).mp (EuclideanDomain.gcd_eq_zero_iff.mp hgcd).1)

omit [Fintype F] in
theorem eval₂_lcmMonic_eq_zero_iff
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {a b : CPolynomial F} (ha : a ≠ 0) :
    (lcmMonic a b).toPoly.eval₂ phi x = 0 ↔
      a.toPoly.eval₂ phi x = 0 ∨ b.toPoly.eval₂ phi x = 0 := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  have hassociated := lcmMonic_toPoly_associated_lcm (a := a) (b := b) ha
  have hroot : (lcmMonic a b).toPoly.eval₂ phi x = 0 ↔
      (EuclideanDomain.lcm a.toPoly b.toPoly).eval₂ phi x = 0 := by
    rcases hassociated with ⟨u, hu⟩
    rw [← hu, Polynomial.eval₂_mul, mul_eq_zero]
    have hunit : IsUnit (Polynomial.eval₂ phi x (u : Polynomial F)) :=
      u.isUnit.map (Polynomial.eval₂RingHom phi x)
    exact (or_iff_left hunit.ne_zero).symm
  rw [hroot]
  constructor
  · intro hlcm
    obtain ⟨c, hc⟩ := EuclideanDomain.lcm_dvd
      (dvd_mul_right a.toPoly b.toPoly) (dvd_mul_left b.toPoly a.toPoly)
    have hproduct : (a.toPoly * b.toPoly).eval₂ phi x = 0 := by
      simp [hc, Polynomial.eval₂_mul, hlcm]
    simpa [Polynomial.eval₂_mul] using hproduct
  · rintro (haRoot | hbRoot)
    · obtain ⟨c, hc⟩ := EuclideanDomain.dvd_lcm_left a.toPoly b.toPoly
      simp [hc, Polynomial.eval₂_mul, haRoot]
    · obtain ⟨c, hc⟩ := EuclideanDomain.dvd_lcm_right a.toPoly b.toPoly
      simp [hc, Polynomial.eval₂_mul, hbRoot]

omit [Fintype F] in
theorem lcmMonic_ne_zero {a b : CPolynomial F} (ha : a ≠ 0) (hb : b ≠ 0) :
    lcmMonic a b ≠ 0 := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  intro hlcm
  have hassociated := lcmMonic_toPoly_associated_lcm (a := a) (b := b) ha
  rw [hlcm, toPoly_zero] at hassociated
  have hmathlib : EuclideanDomain.lcm a.toPoly b.toPoly = 0 :=
    hassociated.eq_zero_iff.mp rfl
  exact (EuclideanDomain.lcm_eq_zero_iff.mp hmathlib).elim
    (fun haPoly ↦ ha ((toPoly_eq_zero_iff a).mp haPoly))
    (fun hbPoly ↦ hb ((toPoly_eq_zero_iff b).mp hbPoly))

omit [Fintype F] in
theorem natDegree_lcmMonic_le_add {a b : CPolynomial F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (lcmMonic a b).natDegree ≤ a.natDegree + b.natDegree := by
  have hfactor := congrArg (CPolynomial.toPoly (R := F))
    (gcdMonic_mul_lcmMonic (a := a) (b := b) ha)
  rw [toPoly_mul, toPoly_mul] at hfactor
  have hgPoly : (gcdMonic a b).toPoly ≠ 0 :=
    ((monic_toPoly_iff _).mp (gcdFactor_monic (e := b) ha)).ne_zero
  have hlcmPoly : (lcmMonic a b).toPoly ≠ 0 :=
    (toPoly_eq_zero_iff _).not.mpr (lcmMonic_ne_zero ha hb)
  have haPoly : a.toPoly ≠ 0 := (toPoly_eq_zero_iff a).not.mpr ha
  have hbPoly : b.toPoly ≠ 0 := (toPoly_eq_zero_iff b).not.mpr hb
  have hdegree := congrArg Polynomial.natDegree hfactor
  rw [Polynomial.natDegree_mul hgPoly hlcmPoly,
    Polynomial.natDegree_mul haPoly hbPoly] at hdegree
  simp only [← natDegree_toPoly] at hdegree
  omega

omit [Fintype F] in
theorem lcmMonic_monic {a b : CPolynomial F} (ha : a.monic) (hb : b.monic) :
    (lcmMonic a b).monic := by
  have haNe : a ≠ 0 :=
    (toPoly_eq_zero_iff a).not.mp ((monic_toPoly_iff a).mp ha).ne_zero
  rw [monic_toPoly_iff]
  apply ((monic_toPoly_iff _).mp (gcdFactor_monic (e := b) haNe)).of_mul_monic_left
  have hfactor := congrArg (CPolynomial.toPoly (R := F))
    (gcdMonic_mul_lcmMonic (a := a) (b := b) haNe)
  rw [toPoly_mul, toPoly_mul] at hfactor
  change ((gcdMonic a b).toPoly * (lcmMonic a b).toPoly).Monic
  rw [hfactor]
  exact ((monic_toPoly_iff a).mp ha).mul ((monic_toPoly_iff b).mp hb)

omit [Fintype F] in
/-- The executable lcm of nonzero squarefree polynomials is squarefree. -/
theorem lcmMonic_squarefree {a b : CPolynomial F} (ha : a ≠ 0) (hb : b ≠ 0)
    (hasq : Squarefree a.toPoly) (hbsq : Squarefree b.toPoly) :
    Squarefree (lcmMonic a b).toPoly := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  have hab := lcmMonic_toPoly_associated_lcm (a := a) (b := b) ha
  apply hab.squarefree_iff.mpr
  have hlcm : EuclideanDomain.lcm a.toPoly b.toPoly ≠ 0 := by
    simpa [EuclideanDomain.lcm_eq_zero_iff, ha, hb] using
      And.intro ((toPoly_eq_zero_iff a).not.mpr ha) ((toPoly_eq_zero_iff b).not.mpr hb)
  have hradA : IsRadical a.toPoly :=
    (isRadical_iff_squarefree_of_ne_zero ((toPoly_eq_zero_iff a).not.mpr ha)).2 hasq
  have hradB : IsRadical b.toPoly :=
    (isRadical_iff_squarefree_of_ne_zero ((toPoly_eq_zero_iff b).not.mpr hb)).2 hbsq
  have hlcmDvdRadical : EuclideanDomain.lcm a.toPoly b.toPoly ∣
      UniqueFactorizationMonoid.radical (EuclideanDomain.lcm a.toPoly b.toPoly) := by
    rw [EuclideanDomain.lcm_dvd_iff]
    constructor
    · exact (UniqueFactorizationMonoid.dvd_radical_iff hradA hlcm).2
        (EuclideanDomain.dvd_lcm_left _ _)
    · exact (UniqueFactorizationMonoid.dvd_radical_iff hradB hlcm).2
        (EuclideanDomain.dvd_lcm_right _ _)
  have hlcmAssociated : Associated (EuclideanDomain.lcm a.toPoly b.toPoly)
      (UniqueFactorizationMonoid.radical (EuclideanDomain.lcm a.toPoly b.toPoly)) :=
    associated_of_dvd_dvd hlcmDvdRadical UniqueFactorizationMonoid.radical_dvd_self
  exact hlcmAssociated.squarefree_iff.mpr UniqueFactorizationMonoid.squarefree_radical

omit [Fintype F] in
/-- Removing the gcd with the derivative leaves a squarefree factor. -/
theorem gcdDerivativeComplement_squarefree (f : CPolynomial F) (hf : f ≠ 0) :
    Squarefree (gcdComplement f f.derivative).toPoly := by
  let : DecidableEq F := instDecidableEqOfLawfulBEq
  let P := f.toPoly
  let D := EuclideanDomain.divRadical P
  have hfPoly : P ≠ 0 := (toPoly_eq_zero_iff f).not.mpr hf
  have hDgcd : D ∣ (gcdFactor f f.derivative).toPoly := by
    rw [gcdFactor_toPoly, dvd_normalize_iff]
    change D ∣ EuclideanDomain.gcd P f.derivative.toPoly
    apply EuclideanDomain.dvd_gcd
    · exact EuclideanDomain.divRadical_dvd_self P
    · simpa only [P, derivative_toPoly] using divRadical_dvd_derivative P
  obtain ⟨k, hk⟩ := hDgcd
  have hsplit := congrArg (CPolynomial.toPoly (R := F))
    (gcdFactor_mul_gcdComplement (h := f) (e := f.derivative) hf)
  rw [toPoly_mul] at hsplit
  have hcancel : D * (k * (gcdComplement f f.derivative).toPoly) =
      D * UniqueFactorizationMonoid.radical P := by
    calc
      _ = (D * k) * (gcdComplement f f.derivative).toPoly := (mul_assoc _ _ _).symm
      _ = (gcdFactor f f.derivative).toPoly *
          (gcdComplement f f.derivative).toPoly := by rw [hk]
      _ = P := hsplit
      _ = UniqueFactorizationMonoid.radical P * D :=
        EuclideanDomain.radical_mul_divRadical.symm
      _ = _ := mul_comm _ _
  have hquotient : (gcdComplement f f.derivative).toPoly ∣
      UniqueFactorizationMonoid.radical P := by
    refine ⟨k, ?_⟩
    calc
      _ = k * (gcdComplement f f.derivative).toPoly :=
        (mul_left_cancel₀ (EuclideanDomain.divRadical_ne_zero hfPoly) hcancel).symm
      _ = _ := mul_comm _ _
  exact UniqueFactorizationMonoid.squarefree_radical.squarefree_of_dvd hquotient

omit [Fintype F] in
theorem gcdDerivativeComplement_ne_zero (f : CPolynomial F) (hf : f ≠ 0) :
    gcdComplement f f.derivative ≠ 0 := by
  intro hcomplement
  have hsplit := gcdFactor_mul_gcdComplement
    (h := f) (e := f.derivative) hf
  rw [hcomplement, mul_zero] at hsplit
  exact hf hsplit.symm

omit [Fintype F] in
theorem natDegree_gcdFactor_derivative_lt {f : CPolynomial F}
    (hfDegree : 0 < f.natDegree) (hderiv : f.derivative ≠ 0) :
    (gcdFactor f f.derivative).natDegree < f.natDegree := by
  have hderivPoly : f.derivative.toPoly ≠ 0 :=
    (toPoly_eq_zero_iff f.derivative).not.mpr hderiv
  have hle := Polynomial.natDegree_le_of_dvd
    (gcdFactor_dvd_right f f.derivative) hderivPoly
  have hlt : f.derivative.toPoly.natDegree < f.toPoly.natDegree := by
    rw [derivative_toPoly]
    exact Polynomial.natDegree_derivative_lt (by simpa [← natDegree_toPoly] using hfDegree.ne')
  simpa only [← natDegree_toPoly] using hle.trans_lt hlt

/-! ## Recursive squarefree support -/

/-- Fuel-bounded executable support extraction.  The public wrapper supplies
one more unit of fuel than the input degree. -/
def squarefreeSupportAux : ℕ → CPolynomial F → CPolynomial F
  | 0, f => f
  | fuel + 1, f =>
      if f == 0 then 0
      else if f.natDegree == 0 then f
      else if f.derivative == 0 then
        squarefreeSupportAux fuel (frobeniusContract p f)
      else
        lcmMonic (gcdComplement f f.derivative)
          (squarefreeSupportAux fuel (gcdFactor f f.derivative))

/-- A total executable monic normalization of the recursively extracted support. -/
def squarefreeSupport (f : CPolynomial F) : CPolynomial F :=
  gcdFactor (squarefreeSupportAux p (f.natDegree + 1) f) 0

theorem squarefreeSupportAux_squarefree_ne_zero {fuel : ℕ} {f : CPolynomial F}
    (hf : f ≠ 0) (hdegree : f.natDegree < fuel) :
    Squarefree (squarefreeSupportAux p fuel f).toPoly ∧
      squarefreeSupportAux p fuel f ≠ 0 := by
  induction fuel generalizing f with
  | zero => omega
  | succ fuel ih =>
      rw [squarefreeSupportAux]
      simp only [beq_iff_eq, hf, if_false]
      by_cases hfDegree : f.natDegree = 0
      · rw [if_pos hfDegree]
        refine ⟨?_, hf⟩
        apply IsUnit.squarefree
        rw [Polynomial.isUnit_iff_degree_eq_zero]
        rw [Polynomial.degree_eq_natDegree ((toPoly_eq_zero_iff f).not.mpr hf),
          ← natDegree_toPoly, hfDegree]
        simp
      · rw [if_neg hfDegree]
        by_cases hderiv : f.derivative = 0
        · rw [if_pos (by simp [hderiv])]
          apply ih (frobeniusContract_ne_zero p hf hderiv)
          exact (natDegree_frobeniusContract_lt p (Nat.pos_of_ne_zero hfDegree) hderiv).trans_le
            (Nat.le_of_lt_succ hdegree)
        · rw [if_neg (by simp [hderiv])]
          have hfPositive : 0 < f.natDegree := Nat.pos_of_ne_zero hfDegree
          have hgDegree := natDegree_gcdFactor_derivative_lt hfPositive hderiv
          have hgSpec := ih (f := gcdFactor f f.derivative)
            ((toPoly_eq_zero_iff _).not.mp
              ((monic_toPoly_iff _).mp (gcdFactor_monic hf)).ne_zero)
            (hgDegree.trans_le (Nat.le_of_lt_succ hdegree))
          exact ⟨lcmMonic_squarefree
              (gcdDerivativeComplement_ne_zero f hf) hgSpec.2
              (gcdDerivativeComplement_squarefree f hf) hgSpec.1,
            lcmMonic_ne_zero (gcdDerivativeComplement_ne_zero f hf) hgSpec.2⟩

theorem natDegree_squarefreeSupportAux_le {fuel : ℕ} {f : CPolynomial F}
    (hf : f ≠ 0) (hdegree : f.natDegree < fuel) :
    (squarefreeSupportAux p fuel f).natDegree ≤ f.natDegree := by
  induction fuel generalizing f with
  | zero => omega
  | succ fuel ih =>
      rw [squarefreeSupportAux]
      simp only [beq_iff_eq, hf, if_false]
      by_cases hfDegree : f.natDegree = 0
      · rw [if_pos hfDegree]
      · rw [if_neg hfDegree]
        by_cases hderiv : f.derivative = 0
        · rw [if_pos (by simp [hderiv])]
          have hcDegree :=
            natDegree_frobeniusContract_lt p (Nat.pos_of_ne_zero hfDegree) hderiv
          exact (ih (frobeniusContract_ne_zero p hf hderiv)
            (hcDegree.trans_le (Nat.le_of_lt_succ hdegree))).trans hcDegree.le
        · rw [if_neg (by simp [hderiv])]
          have hfPositive : 0 < f.natDegree := Nat.pos_of_ne_zero hfDegree
          have hgDegree := natDegree_gcdFactor_derivative_lt hfPositive hderiv
          have hgNe : gcdFactor f f.derivative ≠ 0 :=
            (toPoly_eq_zero_iff _).not.mp
              ((monic_toPoly_iff _).mp (gcdFactor_monic hf)).ne_zero
          have hgSupportNe := (squarefreeSupportAux_squarefree_ne_zero p hgNe
            (hgDegree.trans_le (Nat.le_of_lt_succ hdegree))).2
          have hlcm := natDegree_lcmMonic_le_add
            (gcdDerivativeComplement_ne_zero f hf) hgSupportNe
          have hrecursive := ih hgNe
            (hgDegree.trans_le (Nat.le_of_lt_succ hdegree))
          have hsplit := natDegree_gcdFactor_add_gcdComplement
            (h := f) (e := f.derivative) hf
          simp only [← natDegree_toPoly] at hsplit
          omega

theorem squarefreeSupportAux_monic {fuel : ℕ} {f : CPolynomial F}
    (hfMonic : f.monic) (hdegree : f.natDegree < fuel) :
    (squarefreeSupportAux p fuel f).monic := by
  have hf : f ≠ 0 :=
    (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hfMonic).ne_zero
  induction fuel generalizing f with
  | zero => omega
  | succ fuel ih =>
      rw [squarefreeSupportAux]
      simp only [beq_iff_eq, hf, if_false]
      by_cases hfDegree : f.natDegree = 0
      · rw [if_pos hfDegree]
        exact hfMonic
      · rw [if_neg hfDegree]
        by_cases hderiv : f.derivative = 0
        · rw [if_pos (by simp [hderiv])]
          apply ih (frobeniusContract_monic p hfMonic hderiv)
          · exact (natDegree_frobeniusContract_lt p
              (Nat.pos_of_ne_zero hfDegree) hderiv).trans_le
              (Nat.le_of_lt_succ hdegree)
          · exact frobeniusContract_ne_zero p hf hderiv
        · rw [if_neg (by simp [hderiv])]
          apply lcmMonic_monic (gcdComplement_monic hfMonic)
          apply ih (gcdFactor_monic hf)
          · exact (natDegree_gcdFactor_derivative_lt
              (Nat.pos_of_ne_zero hfDegree) hderiv).trans_le
              (Nat.le_of_lt_succ hdegree)
          · exact (toPoly_eq_zero_iff _).not.mp
              ((monic_toPoly_iff _).mp (gcdFactor_monic hf)).ne_zero

theorem eval₂_squarefreeSupportAux_eq_zero_iff
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {fuel : ℕ} {f : CPolynomial F} (hf : f ≠ 0) (hdegree : f.natDegree < fuel) :
    (squarefreeSupportAux p fuel f).toPoly.eval₂ phi x = 0 ↔
      f.toPoly.eval₂ phi x = 0 := by
  induction fuel generalizing f with
  | zero => omega
  | succ fuel ih =>
      rw [squarefreeSupportAux]
      simp only [beq_iff_eq, hf, if_false]
      by_cases hfDegree : f.natDegree = 0
      · rw [if_pos hfDegree]
      · rw [if_neg hfDegree]
        by_cases hderiv : f.derivative = 0
        · rw [if_pos (by simp [hderiv])]
          exact (ih (f := frobeniusContract p f)
            (frobeniusContract_ne_zero p hf hderiv)
            ((natDegree_frobeniusContract_lt p (Nat.pos_of_ne_zero hfDegree) hderiv).trans_le
              (Nat.le_of_lt_succ hdegree))).trans
                (eval₂_frobeniusContract_eq_zero_iff p phi x hderiv)
        · rw [if_neg (by simp [hderiv])]
          have hfPositive : 0 < f.natDegree := Nat.pos_of_ne_zero hfDegree
          have hgDegree := natDegree_gcdFactor_derivative_lt hfPositive hderiv
          have hgNe : gcdFactor f f.derivative ≠ 0 :=
            (toPoly_eq_zero_iff _).not.mp
              ((monic_toPoly_iff _).mp (gcdFactor_monic hf)).ne_zero
          rw [eval₂_lcmMonic_eq_zero_iff phi x (gcdDerivativeComplement_ne_zero f hf)]
          rw [ih hgNe (hgDegree.trans_le (Nat.le_of_lt_succ hdegree))]
          rw [eval₂_gcdFactor_eq_zero_or_gcdComplement_eq_zero phi x hf]
          tauto

theorem squarefreeSupport_squarefree {f : CPolynomial F} (hf : f ≠ 0) :
    Squarefree (squarefreeSupport p f).toPoly := by
  apply gcdFactor_squarefree
  exact (squarefreeSupportAux_squarefree_ne_zero p hf (Nat.lt_succ_self _)).1

theorem squarefreeSupport_ne_zero {f : CPolynomial F} (hf : f ≠ 0) :
    squarefreeSupport p f ≠ 0 := by
  apply (toPoly_eq_zero_iff _).not.mp
  apply ((monic_toPoly_iff _).mp (gcdFactor_monic ?_)).ne_zero
  exact (squarefreeSupportAux_squarefree_ne_zero p hf (Nat.lt_succ_self _)).2

theorem natDegree_squarefreeSupport_le {f : CPolynomial F} (hf : f ≠ 0) :
    (squarefreeSupport p f).natDegree ≤ f.natDegree := by
  let raw := squarefreeSupportAux p (f.natDegree + 1) f
  have hrawNe : raw ≠ 0 :=
    (squarefreeSupportAux_squarefree_ne_zero p hf (Nat.lt_succ_self _)).2
  have hle : (gcdFactor raw 0).toPoly.natDegree ≤ raw.toPoly.natDegree :=
    Polynomial.natDegree_le_of_dvd (gcdFactor_dvd_left raw 0)
      ((toPoly_eq_zero_iff raw).not.mpr hrawNe)
  have hnormalized : (squarefreeSupport p f).natDegree ≤ raw.natDegree := by
    simpa only [squarefreeSupport, raw, ← natDegree_toPoly] using hle
  exact hnormalized.trans
    (natDegree_squarefreeSupportAux_le p hf (Nat.lt_succ_self _))

theorem squarefreeSupport_monic {f : CPolynomial F} (hf : f ≠ 0) :
    (squarefreeSupport p f).monic := by
  apply gcdFactor_monic
  exact (squarefreeSupportAux_squarefree_ne_zero p hf (Nat.lt_succ_self _)).2

/-- Support extraction preserves roots after every coefficient-field extension. -/
theorem eval₂_squarefreeSupport_eq_zero_iff
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {f : CPolynomial F} (hf : f ≠ 0) :
    (squarefreeSupport p f).toPoly.eval₂ phi x = 0 ↔ f.toPoly.eval₂ phi x = 0 := by
  rw [squarefreeSupport]
  rw [eval₂_gcdFactor_eq_zero_iff_left_right phi x]
  simp only [toPoly_zero, Polynomial.eval₂_zero, and_true]
  exact eval₂_squarefreeSupportAux_eq_zero_iff
    p phi x hf (Nat.lt_succ_self f.natDegree)

end CompPoly.CPolynomial
