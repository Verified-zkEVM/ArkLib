/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.Folding
import ArkLib.Data.Domain.CosetFftDomain.Subdomain
import ArkLib.Data.Domain.CosetFftDomain.Log
import ArkLib.Data.MvPolynomial.EvenAndOdd
import CompPoly.Data.MvPolynomial.Notation

namespace ProximityGap

open NNReal Finset Function
open scoped ProbabilityTheory
open scoped BigOperators LinearCode
open Code Affine ReedSolomon
open Domain
open CosetFftDomain CosetFftDomainClass
open MvPolynomial LinearMvExtension

variable {F : Type} [Field F] [DecidableEq F]
variable {n : ℕ}
variable {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))}
variable {k : ℕ} {x : F}

lemma foldWord_eq_evalOnPoints_powAlgHom [NeZero n] {α : F}
  {g : F⦃≤ 1⦄[X (Fin n)]}
  (hf : f = evalOnPoints domain (powAlgHom g.1)) :
  foldWord domain f 1 α =
    evalOnPoints
      (domain.subdomain 1)
      (powAlgHom (g.1.aeval (fun i ↦
          if h : i = 0 then C α else MvPolynomial.X (⟨i.val - 1, by omega⟩ : Fin (n - 1))))) := by
  have hchar := CosetFftDomainClass.domain_implies_char_ne_2 domain
  have h2ne0 : (2 : F) ≠ 0 := fun contra ↦ hchar <|
    ringChar.of_eq (CharP.ringChar_of_prime_eq_zero Nat.prime_two contra)
  subst hf
  conv_lhs =>
    rw [powAlgHom_eq_even_add_odd_powAlgHom hchar]
  rw [even_and_odd_eval hchar, foldWord_k_1']
  ext u
  extract_lets x j j'
  have : x.val ≠ 0 := fun contra ↦ by
    have := x.2
    simp_all
  aesop
    (add safe (by field_simp))
    (add simp
      [evalOnPoints,
       subdomain_sqFoldMapGen_eq_pow_domain,
       evalOnPoints_sq_eq_evalOnPoints_subdomain])
    (add unsafe
      [(by ring_nf),
       (by rw [add_comm, mul_comm]),
       sqFoldMapGen_eq_sqFoldMapGen_of_pow_apply_eq_pow_apply])

end ProximityGap
