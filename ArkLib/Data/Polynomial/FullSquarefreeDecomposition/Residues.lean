/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.SquarefreeSupport
public import ArkLib.Data.Polynomial.GCDSplit
public import ArkLib.Data.Polynomial.ModularInverse
public import CompPoly.Univariate.Deriv

/-!
# Multiplicity-residue stage of squarefree decomposition

This is the residue stage in the paper's finite-algebra appendix, not a full
squarefree decomposition. It computes the derivative gcd and modular inverse,
then extracts residue strata in order, reducing the residue polynomial after
each exact division. The fuel is bounded by both degree and characteristic.
The residual is retained explicitly when fuel is exhausted. Recursive
inverse Frobenius and product/remainder-tree refinement are subsequent stages.
-/

@[expose] public section

namespace CompPoly.CPolynomial.FullSquarefreeDecomposition

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Derivative gcd and the two exact quotients used in residue initialization. -/
def derivativeParts (f : CPolynomial F) :
    CPolynomial F × CPolynomial F × CPolynomial F :=
  let u := gcdFactor f f.derivative
  (u, f.divByMonic u, f.derivative.divByMonic u)

/-- Compute `w * inverse(v') mod v`; a failed inverse is reported explicitly.
The unit modulus has no residue strata and needs no inversion. -/
def residuePolynomial? (f : CPolynomial F) : Option (CPolynomial F) :=
  let parts := derivativeParts f
  let v := parts.2.1
  if v == 1 then some 0 else
    (inverseMod? v.derivative v).map fun inverse =>
      (parts.2.2 * inverse).modByMonic v

/-- Ordered extracted strata and the unprocessed residual modulus. Labels are
natural integer residues; the polynomial `1` is retained for empty strata. -/
structure ResidueOutput (F : Type*) [Field F] [BEq F] where
  strata : List (ℕ × CPolynomial F)
  residual : CPolynomial F

/-- Bounded appendix loop, including exact quotient, remainder reduction and
unit early stop. The next residue starts at one in the public entrypoint. -/
def residueLoop : ℕ → ℕ → CPolynomial F → CPolynomial F → ResidueOutput F
  | 0, _, a, _ => ⟨[], a⟩
  | fuel + 1, r, a, q =>
    if a == 1 then ⟨[], a⟩ else
      let e := q - C (r : F)
      let h := gcdFactor a e
      let next := gcdComplement a e
      let out := residueLoop fuel (r + 1) next (q.modByMonic next)
      ⟨(r, h) :: out.strata, out.residual⟩

/-- Run the residue stage. Zero is rejected; monic constants and monic derivative-zero
inputs return no strata with residual one. This does not discard their
unprocessed derivative gcd, available separately in `derivativeParts`.
Here `p` supplies a numeric loop bound; multiplicity interpretation additionally
requires `CharP F p` and the logarithmic-differentiation lemma. -/
def run (p : ℕ) (f : CPolynomial F) : Option (ResidueOutput F) :=
  if f == 0 then none else
    (residuePolynomial? f).map fun q =>
      residueLoop (min (p - 1) f.natDegree) 1 (derivativeParts f).2.1 q

/-- The derivative-gcd split reconstructs the original nonzero input. -/
theorem derivativeParts_exact {f : CPolynomial F} (hf : f ≠ 0) :
    (derivativeParts f).1 * (derivativeParts f).2.1 = f :=
  gcdFactor_mul_gcdComplement hf

/-- Every executed loop step preserves the product of the extracted factors
and residual, even if the caller's fuel is insufficient to finish. -/
theorem residueLoop_exact (fuel r : ℕ) (a q : CPolynomial F) (ha : a.monic) :
    ((residueLoop fuel r a q).strata.map Prod.snd).prod *
      (residueLoop fuel r a q).residual = a := by
  induction fuel generalizing r a q with
  | zero => simp [residueLoop]
  | succ fuel ih =>
    by_cases hunit : a = 1
    · simp [residueLoop, hunit]
    · simp only [residueLoop, beq_iff_eq, hunit, ↓reduceIte,
        List.map_cons, List.prod_cons]
      rw [mul_assoc, ih _ _ _ (gcdComplement_monic ha)]
      exact gcdFactor_mul_gcdComplement
        ((toPoly_eq_zero_iff a).not.mp ((monic_toPoly_iff a).mp ha).ne_zero)

/-- The loop performs at most the supplied number of residue tests. -/
theorem residueLoop_length_le (fuel r : ℕ) (a q : CPolynomial F) :
    (residueLoop fuel r a q).strata.length ≤ fuel := by
  induction fuel generalizing r a q with
  | zero => simp [residueLoop]
  | succ fuel ih =>
    simp only [residueLoop]
    split
    · simp
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (ih _ _ _)

/-- Exact division leaves a monic residual at every bounded stopping point. -/
theorem residueLoop_residual_monic (fuel r : ℕ) (a q : CPolynomial F)
    (ha : a.monic) : (residueLoop fuel r a q).residual.monic := by
  induction fuel generalizing r a q with
  | zero => exact ha
  | succ fuel ih =>
    simp only [residueLoop]
    split
    · exact ha
    · exact ih _ _ _ (gcdComplement_monic ha)

/-- Extracted strata are monic factors of the input; this invariant does not
require the multiplicity-residue interpretation of `q`. -/
theorem residueLoop_strata_monic (fuel r : ℕ) (a q : CPolynomial F)
    (ha : a.monic) :
    ∀ z ∈ (residueLoop fuel r a q).strata, z.2.monic := by
  induction fuel generalizing r a q with
  | zero => simp [residueLoop]
  | succ fuel ih =>
    simp only [residueLoop]
    split
    · simp
    · intro z hz
      rcases List.mem_cons.mp hz with hz | hz
      · subst z
        exact gcdFactor_monic
          ((toPoly_eq_zero_iff a).not.mp ((monic_toPoly_iff a).mp ha).ne_zero)
      · exact ih _ _ _ (gcdComplement_monic ha) z hz

/-- Squarefree input gives squarefree strata and residual through the actual
loop's gcd and exact quotient operations. -/
theorem residueLoop_squarefree (fuel r : ℕ) (a q : CPolynomial F)
    (ha : a.monic) (hs : Squarefree a.toPoly) :
    Squarefree (residueLoop fuel r a q).residual.toPoly ∧
      ∀ z ∈ (residueLoop fuel r a q).strata, Squarefree z.2.toPoly := by
  induction fuel generalizing r a q with
  | zero => simpa [residueLoop] using hs
  | succ fuel ih =>
    simp only [residueLoop]
    split
    · simpa using hs
    · have hn : a ≠ 0 :=
        (toPoly_eq_zero_iff a).not.mp ((monic_toPoly_iff a).mp ha).ne_zero
      obtain ⟨hr, hstrata⟩ := ih _ _ _ (gcdComplement_monic ha)
        (gcdComplement_squarefree hn hs)
      refine ⟨hr, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with hz | hz
      · subst z
        exact gcdFactor_squarefree hs
      · exact hstrata z hz

/-- The entire initialized residue stage reconstructs its input together with
the derivative gcd. No multiplicity classification premise is hidden here. -/
theorem run_exact (p : ℕ) {f : CPolynomial F} (hf : f.monic)
    {out : ResidueOutput F} (hout : run p f = some out) :
    (derivativeParts f).1 * (out.strata.map Prod.snd).prod * out.residual = f := by
  have hn : f ≠ 0 := (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  simp only [run, beq_iff_eq, hn, ↓reduceIte] at hout
  cases hq : residuePolynomial? f with
  | none => simp [hq] at hout
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at hout
    subst out
    have hv : (derivativeParts f).2.1.monic := gcdComplement_monic hf
    rw [mul_assoc, residueLoop_exact _ _ _ _ hv]
    exact derivativeParts_exact hn

/-- On certified monic input whose derivative quotient is separable, the
actual producer succeeds and reconstructs the input. Deriving this coprimality
certificate from finite-field multiplicities is a subsequent obligation. -/
theorem run_exists_exact (p : ℕ) {f : CPolynomial F} (hf : f.monic)
    (hc : IsCoprime (derivativeParts f).2.1.derivative.toPoly
      (derivativeParts f).2.1.toPoly) :
    ∃ out, run p f = some out ∧
      (derivativeParts f).1 * (out.strata.map Prod.snd).prod * out.residual = f := by
  have hn : f ≠ 0 := (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  have hq : ∃ q, residuePolynomial? f = some q := by
    by_cases hu : (derivativeParts f).2.1 = 1
    · exact ⟨0, by simp [residuePolynomial?, hu]⟩
    · obtain ⟨inverse, hi⟩ := (inverseMod_exists_iff_coprime _ _).mpr hc
      refine ⟨((derivativeParts f).2.2 * inverse).modByMonic (derivativeParts f).2.1, ?_⟩
      simp [residuePolynomial?, beq_iff_eq, hu, hi]
  obtain ⟨q, hq⟩ := hq
  have hout : run p f = some
      (residueLoop (min (p - 1) f.natDegree) 1 (derivativeParts f).2.1 q) := by
    simp [run, beq_iff_eq, hn, hq]
  exact ⟨_, hout, run_exact p hf hout⟩

/-- Over a perfect field the derivative quotient supplies its own inversion
certificate. The support owner's theorem is used only in this proof; the
executable call graph remains the appendix's residue calculation. -/
theorem run_exists_exact_of_perfect [PerfectField F] (p : ℕ)
    {f : CPolynomial F} (hf : f.monic) :
    ∃ out, run p f = some out ∧
      (derivativeParts f).1 * (out.strata.map Prod.snd).prod * out.residual = f := by
  have hn : f ≠ 0 := (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp hf).ne_zero
  have hs : Squarefree (derivativeParts f).2.1.toPoly :=
    gcdDerivativeComplement_squarefree f hn
  apply run_exists_exact p hf
  simpa only [derivative_toPoly] using
    (PerfectField.separable_iff_squarefree.mpr hs).symm

/-- At any root of the initial modulus, the computed residue solves
`q * v' = w`. Turning this into the integer multiplicity residue requires
logarithmic differentiation and remains a separate factorization lemma. -/
theorem residuePolynomial?_root_identity {K : Type*} [Field K]
    (ι : F →+* K) (x : K) {f q : CPolynomial F}
    (hv : (derivativeParts f).2.1.monic)
    (hroot : (derivativeParts f).2.1.toPoly.eval₂ ι x = 0)
    (hq : residuePolynomial? f = some q) :
    q.toPoly.eval₂ ι x * (derivativeParts f).2.1.derivative.toPoly.eval₂ ι x =
      (derivativeParts f).2.2.toPoly.eval₂ ι x := by
  have hunit : (derivativeParts f).2.1 ≠ 1 := by
    intro h
    simp [h, toPoly_one] at hroot
  simp only [residuePolynomial?, beq_iff_eq, hunit, ↓reduceIte] at hq
  cases hi : inverseMod? (derivativeParts f).2.1.derivative
      (derivativeParts f).2.1 with
  | none => simp [hi] at hq
  | some inverse =>
    simp only [hi, Option.map_some, Option.some.injEq] at hq
    subst q
    rw [modByMonic_toPoly_eq_modByMonic _ _ hv,
      Polynomial.eval₂_modByMonic_eq_self_of_root hroot, toPoly_mul,
      Polynomial.eval₂_mul, mul_assoc, mul_comm (inverse.toPoly.eval₂ ι x),
      eval₂_mul_inverseMod_eq_one ι x hroot hi, mul_one]

/-- A residue step selects precisely roots where the current residue equals
its integer label, after any coefficient-field extension. -/
theorem residue_step_roots {K : Type*} [Field K] (ι : F →+* K) (x : K)
    (a q : CPolynomial F) (r : ℕ) :
    (gcdFactor a (q - C (r : F))).toPoly.eval₂ ι x = 0 ↔
      a.toPoly.eval₂ ι x = 0 ∧ q.toPoly.eval₂ ι x = (r : K) := by
  rw [eval₂_gcdFactor_eq_zero_iff_left_right]
  simp [toPoly_sub, toPoly_C, sub_eq_zero]

end CompPoly.CPolynomial.FullSquarefreeDecomposition
