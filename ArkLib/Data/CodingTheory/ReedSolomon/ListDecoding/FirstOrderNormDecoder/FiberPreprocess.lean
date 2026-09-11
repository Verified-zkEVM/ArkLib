/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FiniteRepresentation
public import ArkLib.Data.Polynomial.SquarefreeSupport
public import Mathlib.Algebra.CharP.Algebra

/-!
# Bounded-degree preprocessing of first-order decoder fibers

After the norm sieve has selected a squarefree base block, the first-order decoder must remove
nilpotents in the bounded fiber and then remove the points where the separant vanishes.  This
file implements and proves the field-fiber operation

`hRed = h / gcd(h, h.derivative)` and `hGood = hRed / gcd(hRed, separant)`.

When `h.natDegree < p` in characteristic `p`, `hRed` has exactly the geometric roots of `h`,
without multiplicity.  The second quotient therefore has exactly the roots of `h` where the
separant is nonzero.  All root statements hold after an arbitrary field extension.

`toFiniteRepresentation?` reduces a supplied coefficient list modulo `hGood` and packages a
nonempty result for the existing agreement-recovery consumer.  It does not construct the
coefficients of the Taylor family.

The remaining tower-level step is dynamic evaluation over `E[u]/G`: the current concrete
polynomial gcd API requires field coefficients.  Completing the full squarefree-base operation
therefore needs an executable D5 routine that splits `G` whenever a prospective leading
coefficient is a zero divisor, together with specialization correctness and preservation of the
sum of `deg G * deg_v h` across all returned blocks.  This module does not postulate that missing
routine and makes no whole-decoder or runtime claim.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormDecoder

open Polynomial Polynomial.JetHornerMachine CompPoly CompPoly.CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Remove repeated roots from one bounded-degree field fiber. -/
def fiberRadical (h : CPolynomial F) : CPolynomial F :=
  gcdComplement h h.derivative

/-- Remove the separant-zero roots after radicalizing one field fiber. -/
def goodFiber (h separant : CPolynomial F) : CPolynomial F :=
  gcdComplement (fiberRadical h) separant

/-- Both intermediate polynomials produced by fiber preprocessing. -/
structure FiberPreprocessResult (F : Type*) [Field F] [BEq F] [LawfulBEq F] where
  /-- The squarefree polynomial with the same geometric roots as the input fiber. -/
  radical : CPolynomial F
  /-- The squarefree polynomial retaining only separant-nonzero roots. -/
  good : CPolynomial F

/-- Execute bounded-degree radicalization followed by separant filtering. -/
def preprocess (h separant : CPolynomial F) : FiberPreprocessResult F :=
  { radical := fiberRadical h, good := goodFiber h separant }

@[simp] theorem preprocess_radical (h separant : CPolynomial F) :
    (preprocess h separant).radical = fiberRadical h := rfl

@[simp] theorem preprocess_good (h separant : CPolynomial F) :
    (preprocess h separant).good = goodFiber h separant := rfl

theorem fiberRadical_ne_zero {h : CPolynomial F} (hh : h ≠ 0) : fiberRadical h ≠ 0 :=
  gcdDerivativeComplement_ne_zero h hh

theorem fiberRadical_monic {h : CPolynomial F} (hh : h.monic) :
    (fiberRadical h).monic :=
  gcdComplement_monic hh

theorem fiberRadical_squarefree (h : CPolynomial F) (hh : h ≠ 0) :
    Squarefree (fiberRadical h).toPoly :=
  gcdDerivativeComplement_squarefree h hh

theorem fiberRadical_natDegree_le {h : CPolynomial F} (hh : h ≠ 0) :
    (fiberRadical h).natDegree ≤ h.natDegree := by
  have hdvd : (fiberRadical h).toPoly ∣ h.toPoly := by
    refine ⟨(gcdFactor h h.derivative).toPoly, ?_⟩
    have hfactor := congrArg (CPolynomial.toPoly (R := F))
      (gcdFactor_mul_gcdComplement (h := h) (e := h.derivative) hh)
    rw [toPoly_mul] at hfactor
    simpa only [fiberRadical, mul_comm] using hfactor.symm
  have hdegree := Polynomial.natDegree_le_of_dvd hdvd
    ((toPoly_eq_zero_iff h).not.mpr hh)
  simpa only [← natDegree_toPoly] using hdegree

private theorem rootMultiplicity_lt_char
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {K : Type*} [Field K] [CharP K p] (phi : F →+* K) (x : K)
    {h : CPolynomial F} (hdegree : h.natDegree < p) :
    (h.toPoly.map phi).rootMultiplicity x < p := by
  by_cases hh : h = 0
  · simpa [hh, CPolynomial.toPoly_zero] using (Fact.out : Nat.Prime p).pos
  have hmapped : h.toPoly.map phi ≠ 0 :=
    (Polynomial.map_ne_zero_iff phi.injective).2 ((toPoly_eq_zero_iff h).not.mpr hh)
  have hdvd := (h.toPoly.map phi).pow_rootMultiplicity_dvd x
  have hle := Polynomial.natDegree_le_of_dvd hdvd hmapped
  have hmultiplicity : (h.toPoly.map phi).rootMultiplicity x ≤
      (h.toPoly.map phi).natDegree := by
    simpa using hle
  exact hmultiplicity.trans_lt <| by
    simpa only [Polynomial.natDegree_map_eq_of_injective phi.injective,
      ← natDegree_toPoly] using hdegree

private theorem derivative_rootMultiplicity_of_natDegree_lt_char
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {K : Type*} [Field K] [CharP K p] (phi : F →+* K) (x : K)
    {h : CPolynomial F} (hh : h ≠ 0) (hdegree : h.natDegree < p)
    (hroot : (h.toPoly.map phi).IsRoot x) :
    (h.toPoly.derivative.map phi).rootMultiplicity x =
      (h.toPoly.map phi).rootMultiplicity x - 1 := by
  have hderivative : h.toPoly.derivative.map phi = (h.toPoly.map phi).derivative := by
    rw [Polynomial.derivative_map]
  rw [hderivative]
  apply Polynomial.derivative_rootMultiplicity_of_root_of_mem_nonZeroDivisors hroot
  apply mem_nonZeroDivisors_of_ne_zero
  exact (CharP.cast_eq_zero_iff K p _).not.mpr <| Nat.not_dvd_of_pos_of_lt
    ((Polynomial.rootMultiplicity_pos
      ((Polynomial.map_ne_zero_iff phi.injective).2
        ((toPoly_eq_zero_iff h).not.mpr hh))).2 hroot)
    (rootMultiplicity_lt_char p phi x hdegree)

private theorem mapped_derivative_ne_zero_of_root_of_natDegree_lt_char
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {K : Type*} [Field K] [CharP K p] (phi : F →+* K) (x : K)
    {h : CPolynomial F} (hh : h ≠ 0) (hdegree : h.natDegree < p)
    (hroot : h.toPoly.eval₂ phi x = 0) : h.toPoly.derivative.map phi ≠ 0 := by
  have hhPoly : h.toPoly ≠ 0 := (toPoly_eq_zero_iff h).not.mpr hh
  have hnpos : 0 < h.toPoly.natDegree :=
    Polynomial.natDegree_pos_of_eval₂_root hhPoly phi hroot fun _ hx ↦
      phi.injective (hx.trans phi.map_zero.symm)
  have hnCast : (h.toPoly.natDegree : K) ≠ 0 :=
    (CharP.cast_eq_zero_iff K p _).not.mpr <|
      Nat.not_dvd_of_pos_of_lt hnpos (by simpa only [← natDegree_toPoly] using hdegree)
  have hleading : phi h.toPoly.leadingCoeff ≠ 0 :=
    fun hz ↦ Polynomial.leadingCoeff_ne_zero.mpr hhPoly <|
      phi.injective (hz.trans phi.map_zero.symm)
  intro hzero
  have hcoeff := congrArg
    (fun q : K[X] ↦ q.coeff (h.toPoly.natDegree - 1)) hzero
  rw [Polynomial.coeff_map, Polynomial.coeff_derivative, Polynomial.coeff_zero] at hcoeff
  rw [Nat.sub_add_cancel hnpos, Polynomial.coeff_natDegree, map_mul] at hcoeff
  norm_cast at hcoeff
  rw [Nat.sub_add_cancel hnpos, map_natCast] at hcoeff
  exact mul_ne_zero hleading hnCast hcoeff

/-- Below the characteristic, the derivative quotient retains exactly every geometric root.
The statement is stable under arbitrary coefficient-field extension. -/
theorem eval₂_fiberRadical_eq_zero_iff
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {h : CPolynomial F} (hh : h ≠ 0) (hdegree : h.natDegree < p) :
    (fiberRadical h).toPoly.eval₂ phi x = 0 ↔ h.toPoly.eval₂ phi x = 0 := by
  let _ : CharP K p := charP_of_injective_ringHom phi.injective p
  constructor
  · intro hroot
    have hfactor := congrArg (CPolynomial.toPoly (R := F))
      (gcdFactor_mul_gcdComplement (h := h) (e := h.derivative) hh)
    rw [toPoly_mul] at hfactor
    have heval := congrArg (fun q : F[X] ↦ q.eval₂ phi x) hfactor
    calc
      h.toPoly.eval₂ phi x =
          (gcdFactor h h.derivative).toPoly.eval₂ phi x *
            (fiberRadical h).toPoly.eval₂ phi x := by
              rw [← Polynomial.eval₂_mul]
              simpa only [fiberRadical] using heval.symm
      _ = 0 := mul_eq_zero.mpr (Or.inr hroot)
  · intro hroot
    have hrootMap : (h.toPoly.map phi).IsRoot x := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hroot
    have hfactor := congrArg (CPolynomial.toPoly (R := F))
      (gcdFactor_mul_gcdComplement (h := h) (e := h.derivative) hh)
    rw [toPoly_mul] at hfactor
    have hfactorMap := congrArg (Polynomial.map phi) hfactor
    rw [Polynomial.map_mul] at hfactorMap
    change (gcdFactor h h.derivative).toPoly.map phi *
      (fiberRadical h).toPoly.map phi = h.toPoly.map phi at hfactorMap
    have hgNe : (gcdFactor h h.derivative).toPoly.map phi ≠ 0 :=
      (Polynomial.map_ne_zero_iff phi.injective).2 <|
        ((monic_toPoly_iff _).mp (gcdFactor_monic hh)).ne_zero
    have hrNe : (fiberRadical h).toPoly.map phi ≠ 0 :=
      (Polynomial.map_ne_zero_iff phi.injective).2 <|
        (toPoly_eq_zero_iff _).not.mpr (fiberRadical_ne_zero hh)
    by_contra hnotRoot
    have hrMultiplicity :
        ((fiberRadical h).toPoly.map phi).rootMultiplicity x = 0 :=
      Polynomial.rootMultiplicity_eq_zero <| by
        simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hnotRoot
    have hhMultiplicity := congrArg (fun q : K[X] ↦ q.rootMultiplicity x) hfactorMap
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hgNe hrNe), hrMultiplicity,
      add_zero] at hhMultiplicity
    have hgDvdBase : (gcdFactor h h.derivative).toPoly ∣ h.toPoly.derivative := by
      simpa only [derivative_toPoly] using gcdFactor_dvd_right h h.derivative
    have hgDvd : (gcdFactor h h.derivative).toPoly.map phi ∣
        h.toPoly.derivative.map phi :=
      (Polynomial.map_dvd_map phi phi.injective
        ((monic_toPoly_iff _).mp (gcdFactor_monic hh))).2
          hgDvdBase
    have hderivativeNe : h.toPoly.derivative.map phi ≠ 0 :=
      mapped_derivative_ne_zero_of_root_of_natDegree_lt_char p phi x hh hdegree hroot
    have hle := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd
      hderivativeNe hgDvd x
    rw [hhMultiplicity] at hle
    rw [derivative_rootMultiplicity_of_natDegree_lt_char
      p phi x hh hdegree hrootMap] at hle
    have hpositive := (Polynomial.rootMultiplicity_pos
      ((Polynomial.map_ne_zero_iff phi.injective).2
        ((toPoly_eq_zero_iff h).not.mpr hh))).2 hrootMap
    omega

theorem goodFiber_ne_zero {h separant : CPolynomial F} (hh : h ≠ 0) :
    goodFiber h separant ≠ 0 := by
  intro hzero
  have hfactor := gcdFactor_mul_gcdComplement
    (h := fiberRadical h) (e := separant) (fiberRadical_ne_zero hh)
  change gcdFactor (fiberRadical h) separant * goodFiber h separant = fiberRadical h at hfactor
  rw [hzero, CPolynomial.mul_zero] at hfactor
  exact fiberRadical_ne_zero hh hfactor.symm

theorem goodFiber_monic {h separant : CPolynomial F} (hh : h.monic) :
    (goodFiber h separant).monic :=
  gcdComplement_monic (fiberRadical_monic hh)

theorem goodFiber_squarefree {h separant : CPolynomial F} (hh : h ≠ 0) :
    Squarefree (goodFiber h separant).toPoly :=
  gcdComplement_squarefree (fiberRadical_ne_zero hh) (fiberRadical_squarefree h hh)

theorem goodFiber_natDegree_le {h separant : CPolynomial F} (hh : h ≠ 0) :
    (goodFiber h separant).natDegree ≤ h.natDegree := by
  have hdvd : (goodFiber h separant).toPoly ∣ (fiberRadical h).toPoly := by
    refine ⟨(gcdFactor (fiberRadical h) separant).toPoly, ?_⟩
    have hfactor := congrArg (CPolynomial.toPoly (R := F))
      (gcdFactor_mul_gcdComplement (h := fiberRadical h) (e := separant)
        (fiberRadical_ne_zero hh))
    rw [toPoly_mul] at hfactor
    simpa only [goodFiber, mul_comm] using hfactor.symm
  have hdegree := Polynomial.natDegree_le_of_dvd hdvd
    ((toPoly_eq_zero_iff _).not.mpr (fiberRadical_ne_zero hh))
  have hdegree' : (goodFiber h separant).natDegree ≤ (fiberRadical h).natDegree := by
    simpa only [← natDegree_toPoly] using hdegree
  exact hdegree'.trans (fiberRadical_natDegree_le hh)

/-- The retained fiber represents exactly the original geometric points where the separant is
nonzero, after every field extension. -/
theorem eval₂_goodFiber_eq_zero_iff
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {h separant : CPolynomial F} (hh : h ≠ 0) (hdegree : h.natDegree < p) :
    (goodFiber h separant).toPoly.eval₂ phi x = 0 ↔
      h.toPoly.eval₂ phi x = 0 ∧ separant.toPoly.eval₂ phi x ≠ 0 := by
  rw [goodFiber]
  rw [eval₂_gcdComplement_eq_zero_iff_left_and_right_ne_zero phi x
    (fiberRadical_ne_zero hh) (fiberRadical_squarefree h hh)]
  rw [eval₂_fiberRadical_eq_zero_iff p phi x hh hdegree]

/-- Reduce materialized message coefficients modulo the retained squarefree fiber.  A constant
retained modulus has no geometric points and is discarded. -/
def toFiniteRepresentation? (h separant : CPolynomial F)
    (coefficients : List (CPolynomial F)) : Option (FiniteRepresentation F) :=
  let modulus := goodFiber h separant
  if modulus.natDegree = 0 then none
  else some {
    modulus
    coefficients := coefficients.map fun c ↦ c.modByMonic modulus }

theorem toFiniteRepresentation?_eq_some_iff
    {h separant : CPolynomial F} {coefficients : List (CPolynomial F)}
    {output : FiniteRepresentation F} :
    toFiniteRepresentation? h separant coefficients = some output ↔
      (goodFiber h separant).natDegree ≠ 0 ∧
        output = {
          modulus := goodFiber h separant
          coefficients := coefficients.map fun c ↦ c.modByMonic (goodFiber h separant) } := by
  simp only [toFiniteRepresentation?]
  split <;> simp_all [eq_comm]

/-- Every nonempty preprocessed fiber becomes a well-formed input to `AgreementRecovery`.
The coefficient width is preserved while each coefficient is reduced modulo `hGood`. -/
theorem toFiniteRepresentation?_wellFormed
    {h separant : CPolynomial F} {coefficients : List (CPolynomial F)}
    {output : FiniteRepresentation F}
    (houtput : toFiniteRepresentation? h separant coefficients = some output)
    (hh : h.monic) : output.WellFormed coefficients.length := by
  obtain ⟨hdegree, rfl⟩ := toFiniteRepresentation?_eq_some_iff.mp houtput
  have hhNe : h ≠ 0 :=
    (toPoly_eq_zero_iff h).not.mp ((monic_toPoly_iff h).mp hh).ne_zero
  refine ⟨(monic_toPoly_iff _).mp (goodFiber_monic hh),
    goodFiber_squarefree hhNe, by simp, ?_⟩
  intro c hc
  simp only [List.mem_map] at hc
  obtain ⟨source, _, rfl⟩ := hc
  rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ (goodFiber_monic hh)]
  exact Polynomial.degree_modByMonic_lt _
    ((monic_toPoly_iff _).mp (goodFiber_monic hh))

theorem toFiniteRepresentation?_modulus_natDegree_le
    {h separant : CPolynomial F} {coefficients : List (CPolynomial F)}
    {output : FiniteRepresentation F}
    (houtput : toFiniteRepresentation? h separant coefficients = some output)
    (hh : h ≠ 0) : output.modulus.natDegree ≤ h.natDegree := by
  obtain ⟨_, rfl⟩ := toFiniteRepresentation?_eq_some_iff.mp houtput
  exact goodFiber_natDegree_le hh

/-- The packaged modulus retains the exact geometric-point semantics of `goodFiber`. -/
theorem eval₂_toFiniteRepresentation?_modulus_eq_zero_iff
    (p : ℕ) [Fact p.Prime] [CharP F p]
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {h separant : CPolynomial F} {coefficients : List (CPolynomial F)}
    {output : FiniteRepresentation F}
    (houtput : toFiniteRepresentation? h separant coefficients = some output)
    (hh : h ≠ 0) (hdegree : h.natDegree < p) :
    output.modulus.toPoly.eval₂ phi x = 0 ↔
      h.toPoly.eval₂ phi x = 0 ∧ separant.toPoly.eval₂ phi x ≠ 0 := by
  obtain ⟨_, rfl⟩ := toFiniteRepresentation?_eq_some_iff.mp houtput
  exact eval₂_goodFiber_eq_zero_iff p phi x hh hdegree

/-- Reducing the supplied coefficients modulo `hGood` preserves their specialization at every
retained root.  Thus the packaged value can be consumed by `FiniteRepresentation.specialize`
without changing the represented message family. -/
theorem toFiniteRepresentation?_specialize
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {h separant : CPolynomial F} {coefficients : List (CPolynomial F)}
    {output : FiniteRepresentation F}
    (houtput : toFiniteRepresentation? h separant coefficients = some output)
    (hh : h.monic) (hroot : output.modulus.toPoly.eval₂ phi x = 0) :
    output.specialize phi x =
      coefficientPolynomial (coefficients.map fun c ↦ c.toPoly.eval₂ phi x) := by
  obtain ⟨_, rfl⟩ := toFiniteRepresentation?_eq_some_iff.mp houtput
  apply congrArg coefficientPolynomial
  simp only [List.map_map]
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply]
  rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ (goodFiber_monic hh)]
  exact Polynomial.eval₂_modByMonic_eq_self_of_root hroot

end ReedSolomon.ListDecoding.FirstOrderNormDecoder
