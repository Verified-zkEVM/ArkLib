/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ReedSolomon.Multilinear
import ArkLib.Data.Domain.CosetFftDomain.Mem

/-!
# Constrained Reed-Solomon codes

Constrained Reed-Solomon codes over a smooth coset FFT domain: the codewords of a smooth
Reed-Solomon code whose decoded multilinear polynomial satisfies a weighted sumcheck
constraint over the Boolean cube (Definitions 4.5 and 4.6 of [ACFY24]).

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
    with Super-Fast Verification*][ACFY24]
-/

namespace ReedSolomon

open LinearMvExtension Domain

variable {F : Type} [Field F] [DecidableEq F]
  {n : ℕ} {domain : SmoothCosetFftDomain n F}
  {m : ℕ}

/-- Auxiliary function to assign values to the weight polynomial variables: index `0` ↦ `p.eval b`,
index `j+1` ↦ `b j`. -/
private noncomputable def toWeightAssignment
    (p : MvPolynomial (Fin m) F)
    (b : Fin m → Fin 2) : Fin (m+1) → F :=
  let b' : Fin m → F := fun i => ↑(b i : ℕ)
  Fin.cases (MvPolynomial.eval b' p)
            (fun i => ↑(b i : ℕ))

/-- Constraint is true, if `∑ {b ∈ {0,1}^m} w(f(b),b) = σ` for given `m`-variate polynomial `f` and
`(m+1)`-variate polynomial `w`. -/
def weightConstraint
    (f : MvPolynomial (Fin m) F)
    (w : MvPolynomial (Fin (m + 1)) F) (σ : F) : Prop :=
  ∑ b : Fin m → Fin 2 , w.eval (toWeightAssignment f b) = σ

/-- Definition 4.5, WHIR[ACFY24]
Constrained Reed-Solomon codes are smooth codes whose decoded `m`-variate polynomial satisfies the
weight constraint for given `w` and `σ`.
-/
def constrainedCode
    (domain : SmoothCosetFftDomain n F) (m : ℕ)
    (w : MvPolynomial (Fin (m + 1)) F) (σ : F) : Set (Fin (2 ^ n) → F) :=
  { f | ∃ (h : f ∈ code (domain : Fin (2 ^ n) ↪ F) (2 ^ m)),
    let g := linearMvExtension <| toPolynomialLT ⟨f, h⟩
    weightConstraint g w σ }

/-- Definition 4.6, WHIR[ACFY24]
Multi-constrained Reed-Solomon codes are smooth codes whose decoded `m`-variate polynomial satisfies
the `t` weight constraints for given `w₀,..., wₜ₋₁` and `σ₀,..., σₜ₋₁`. -/
def multiConstrainedCode
    (domain : SmoothCosetFftDomain n F) (m t : ℕ)
    (w : Fin t → MvPolynomial (Fin (m + 1)) F)
    (σ : Fin t → F) : Set (Fin (2 ^ n) → F) :=
  { f |
    ∃ (h : f ∈ code (domain : Fin (2 ^ n) ↪ F) (2 ^ m)),
      let g := linearMvExtension <| toPolynomialLT ⟨f, h⟩
      ∀ i : Fin t, weightConstraint g (w i) (σ i)}

omit [DecidableEq F] in
lemma rs_code_is_multi_constrained
    {domain : SmoothCosetFftDomain n F} {d : ℕ} :
    (code domain (2 ^ d)).carrier =
      multiConstrainedCode domain d 0 (fun _ ↦ 0) (fun _ ↦ 0) := by
  simp [multiConstrainedCode]

end ReedSolomon
