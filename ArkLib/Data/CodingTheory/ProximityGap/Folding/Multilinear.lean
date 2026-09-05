/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.Folding
import ArkLib.Data.CodingTheory.ProximityGap.Folding.FoldingContext
import ArkLib.Data.Domain.CosetFftDomain.Subdomain
import ArkLib.Data.Domain.CosetFftDomain.Log
import ArkLib.Data.MvPolynomial.EvenAndOdd
import CompPoly.Data.MvPolynomial.Notation

/-! This module provides an equivalent statement
  of folding completeness of RS-codes in terms of multilinear polynomials
  as can be found in [ACFY24].

## References

  * [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *WHIR: Reed–Solomon Proximity Testing
      with Super-Fast Verification*][ACFY24]
-/

namespace ProximityGap

open NNReal Finset Function
open scoped ProbabilityTheory
open scoped BigOperators LinearCode
open Code Affine ReedSolomon
open Domain
open CosetFftDomain CosetFftDomainClass
open MvPolynomial LinearMvExtension

variable {F : Type} [Field F] [DecidableEq F]
variable {n d : ℕ}
variable {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))}
variable {k : ℕ} {x : F}

open FoldingContext in
/-- One step of lemma 4.15 from [ACFY24]. -/
lemma foldWord_eq_evalOnPoints_powAlgHom [FoldingContext 1 d n] {α : F}
    {g : F⦃≤ 1⦄[X (Fin d)]}
  (hf : f = evalOnPoints domain (powAlgHom g.1)) :
  foldWord domain f 1 α =
    evalOnPoints
      (domain.subdomain 1)
      (powAlgHom (g.1.aeval (fun i ↦
          if h : i = 0 then C α else MvPolynomial.X (⟨i.val - 1, by omega⟩ : Fin (d - 1))))) := by
  subst hf
  have hchar := domain_implies_char_ne_2 domain
  conv_lhs =>
    rw [powAlgHom_eq_even_add_odd_powAlgHom hchar]
  rw [even_and_odd_eval hchar, foldWord_k_1']
  have : (2 : F) ≠ 0 := domain_implies_2_ne_0 domain
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

private noncomputable def substFun (m : ℕ) (β : Fin m → F) (i : Fin n) :
    MvPolynomial (Fin (n - m)) F :=
  if h : i.val < m then MvPolynomial.C (β ⟨i.val, h⟩)
  else MvPolynomial.X ⟨i.val - m, by omega⟩

omit [DecidableEq F] in
private lemma aeval_substFun_comp {k : ℕ} [NeZero (n - k)] (γ : Fin (k + 1) → F)
    (g0 : MvPolynomial (Fin n) F) :
    (MvPolynomial.aeval (substFun k (fun j ↦ γ ⟨j.val, by omega⟩)) g0).aeval
        (fun i : Fin (n - k) ↦ if h : i = 0 then MvPolynomial.C (γ ⟨k, by omega⟩)
          else MvPolynomial.X (⟨i.val - 1, by omega⟩ : Fin (n - k - 1)))
      = MvPolynomial.aeval (substFun (k + 1) γ) g0 := by
  rw [MvPolynomial.comp_aeval_apply]
  refine congrArg (fun φ ↦ MvPolynomial.aeval φ g0) ?_
  funext i
  unfold substFun
  by_cases h1 : i.val < k
  · rw [dif_pos h1, dif_pos (show i.val < k + 1 by omega)]
    simp
  · rw [dif_neg h1]
    by_cases h2 : i.val = k
      <;> aesop (add safe (by grind))

private lemma aeval_split_mem {n : ℕ} [NeZero n] {R : Type} [Field R]
  (hchar : ¬CharP R 2)
  (p : R⦃≤ 1⦄[X (Fin n)]) (α : R) :
  p.1.aeval
    (fun i ↦ if h : i = 0 then C α else (MvPolynomial.X ⟨i.val - 1, by omega⟩ : R[X (Fin (n - 1))]))
      ∈ restrictDegree (Fin (n - 1)) R 1 := by
  rw [even_and_odd_eval hchar]
  exact Submodule.add_mem _ (even_pred p).2
    (by rw [MvPolynomial.C_mul']; exact Submodule.smul_mem _ _ (odd_pred p).2)

omit [DecidableEq F] in
private lemma aeval_substFun_mem [NeZero n] {gg : F⦃≤ 1⦄[X (Fin n)]}
  (hchar : ¬CharP F 2) :
  ∀ (m : ℕ), m ≤ n → ∀ (β : Fin m → F),
    MvPolynomial.aeval (substFun m β) gg.1 ∈ MvPolynomial.restrictDegree (Fin (n - m)) F 1 := by
  intro m
  induction m with
  | zero =>
    intro hm β
    have : (substFun (n := n) 0 β) = MvPolynomial.X := by aesop
    aesop
  | succ m ih =>
    intro hm β
    have : NeZero (n - m) := ⟨by omega⟩
    have hq : MvPolynomial.aeval (substFun m (fun j ↦ β ⟨j.val, by omega⟩)) gg.1 ∈
      MvPolynomial.restrictDegree (Fin (n - m)) F 1 := ih (by omega) _
    have hmem :
        (MvPolynomial.aeval (substFun m (fun j ↦ β ⟨j.val, by omega⟩)) gg.1).aeval
          (fun i : Fin (n - m) ↦ if h : i = 0 then MvPolynomial.C (β ⟨m, by omega⟩)
            else MvPolynomial.X (⟨i.val - 1, by omega⟩ : Fin (n - m - 1)))
          ∈ MvPolynomial.restrictDegree (Fin (n - m - 1)) F 1 :=
      aeval_split_mem hchar ⟨_, hq⟩ (β ⟨m, by omega⟩)
    rw [←aeval_substFun_comp (k := m) β gg.1]
    exact hmem

open FoldingContext in
/-- Lemma 4.15 from [ACFY24]. Provides a way to
  compute the corresponding multilinear extension
  for the interated folding of codewords. -/
theorem iteratedFoldWord_eq_evalOnPoints_powAlgHom [FoldingContext k d n]
    {α : Fin k → F} {g : F⦃≤ 1⦄[X (Fin d)]}
  (hf : f = evalOnPoints domain (powAlgHom g.1)) :
  iteratedFoldWord domain f k α =
      evalOnPoints
        (domain.subdomain k)
        (powAlgHom (g.1.aeval (fun i ↦
          if h : i.val < k then C (α ⟨i.val, h⟩) else MvPolynomial.X
            (⟨i.val - k, by omega⟩ : Fin (d - k))))) := by
  suffices H : ∀ (k : ℕ), k ≤ d → ∀ (α : Fin k → F),
      iteratedFoldWord domain f k α
        = evalOnPoints (domain.subdomain k) (powAlgHom (g.1.aeval (substFun k α))) by
    exact H k (by grind) α
  intro k
  induction k with
  | zero =>
    intro _ α
    have : substFun (n := d) 0 α = MvPolynomial.X := by aesop
    aesop
  | succ k ih =>
    intro hk' α
    have : NeZero (d - k) := ⟨by omega⟩
    have hprev := ih (by omega) (fun j ↦ α ⟨j.val, by omega⟩)
    have hmem := aeval_substFun_mem (gg := g)
      (domain_implies_char_ne_2 domain) k (by omega)
      (fun j : Fin k ↦ α ⟨j.val, by omega⟩)
    have : FoldingContext 1 (d - k) (n - k) :=
      FoldingContext.mk' (by omega) (by omega) (by grind)
    rw [iteratedFoldWord_succ,
        foldWord_eq_evalOnPoints_powAlgHom (g := ⟨_, hmem⟩) (α := α ⟨k, by omega⟩) hprev,
        aeval_substFun_comp]
    funext i
    simp only [evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    exact subdomain_comp (ω := domain) (k := k) (j := 1) (by grind) rfl

end ProximityGap
