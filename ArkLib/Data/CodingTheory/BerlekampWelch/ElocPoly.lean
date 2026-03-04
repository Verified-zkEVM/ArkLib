/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Init.Data.List.FinRange
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Mul

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.Fin.Lift

namespace BerlekampWelch

variable {F : Type} [Field F]
         {m n : ℕ} {p : Polynomial F}
variable [DecidableEq F]

section ElocPoly

open Polynomial

protected noncomputable def ElocPoly (n : ℕ) (ωs f : ℕ → F) (p : Polynomial F) : Polynomial F :=
  List.prod <| (List.range n).map fun i =>
    if f i = p.eval (ωs i)
    then 1
    else X - C (ωs i)

section

open BerlekampWelch (ElocPoly)

variable {ωs f : ℕ → F}

@[simp]
protected lemma elocPoly_zero : ElocPoly 0 ωs f p = 1 := rfl

@[simp]
protected lemma elocPoly_one :
  ElocPoly 1 ωs f p = if f 0 ≠ p.eval (ωs 0) then X - (C (ωs 0)) else 1 := by
  simp [ElocPoly, List.range_succ]

@[simp]
protected lemma elocPoly_two :
  ElocPoly 2 ωs f p =
  if f 1 = eval (ωs 1) p
  then if f 0 = eval (ωs 0) p then 1
       else X - C (ωs 0)
  else if f 0 = eval (ωs 0) p then X - C (ωs 1)
       else (X - C (ωs 0)) * (X - C (ωs 1)) := by
  simp [ElocPoly, List.range_succ]

@[simp]
protected lemma elocPoly_succ :
  ElocPoly (n + 1) ωs f p =
  ElocPoly n ωs f p *
    if f n = p.eval (ωs n)
    then 1
    else X - C (ωs n) := by
  conv_lhs => unfold ElocPoly
  rw [List.range_succ, List.map_append, List.prod_append, ←ElocPoly.eq_def]
  simp

open BerlekampWelch (elocPoly_succ) in
protected lemma roots_of_eloc_poly {x : F}
  (h : (ElocPoly n ωs f p).eval x = 0) :
  ∃ i, i < n ∧ f i ≠ p.eval (ωs i) := by
  induction n generalizing x with
  | zero => aesop
  | succ n ih =>
    rw [elocPoly_succ, Polynomial.eval_mul, mul_eq_zero] at h
    rcases h with heval | heval
    · obtain ⟨i, _⟩ := ih heval
      aesop (add safe [(by existsi i), (by omega)])
    · aesop (add safe (by use n))

protected lemma errors_are_roots_of_elocPoly {i : ℕ}
  (hi : i < n) (h : f i ≠ p.eval (ωs i)) : (ElocPoly n ωs f p).eval (ωs i) = 0 := by
  induction n with
  | zero => aesop
  | succ n ih =>
    by_cases i = n
    · aesop
    · have : i < n := by omega
      aesop

@[simp]
protected lemma elocPoly_ne_zero : ElocPoly n ωs f p ≠ 0 := by
  induction n with
  | zero => simp
  | succ n hn => aesop (add simp [sub_eq_zero]) (add safe forward (Polynomial.X_ne_C (ωs n)))

@[simp]
protected lemma elocPoly_leading_coeff_one : (ElocPoly n ωs f p).leadingCoeff = 1 := by
  induction n with
  | zero => simp
  | succ n _ => aesop

section

open Fin

protected lemma elocPoly_congr {ωs' f' : ℕ → F}
  (h₁ : ∀ {m}, m < n → ωs m = ωs' m) (h₂ : ∀ {m}, m < n → f m = f' m) :
  ElocPoly n ωs f = ElocPoly n ωs' f' := by
  ext p
  unfold ElocPoly
  rw [
    ←List.pmap_eq_map (p := (·<n)) (H := by simp),
    ←List.pmap_eq_map (p := (·<n)) (H := by simp),
    List.pmap_eq_map_attach, List.pmap_eq_map_attach
  ]
  aesop (add simp List.mem_range)

open BerlekampWelch (elocPoly_congr)

noncomputable def ElocPolyF (ωs f : Fin n → F) (p : Polynomial F) : Polynomial F :=
  ElocPoly n (liftF ωs) (liftF f) p

@[simp]
protected lemma elocPolyF_eq_elocPoly :
  ElocPolyF (n := n) (liftF' ωs) (liftF' f) = ElocPoly n ωs f :=
  elocPoly_congr liftF_liftF'_of_lt liftF_liftF'_of_lt

@[simp]
protected lemma elocPolyF_eq_elocPoly' {ωs f : Fin n → F} :
  ElocPolyF ωs f p = ElocPoly n (liftF ωs) (liftF f) p := rfl

protected lemma elocPoly_leftF_leftF_eq_contract {ωs f : Fin m → F} :
  ElocPoly n (liftF ωs) (liftF f) =
  ElocPoly n (contract n ωs) (contract n f) := by
  rw [elocPoly_congr contract_eq_liftF_of_lt contract_eq_liftF_of_lt]

protected lemma elocPolyF_ne_zero {ωs f : Fin m → F} :
  ElocPolyF ωs f p ≠ 0 := by
  aesop (add simp [BerlekampWelch.elocPoly_ne_zero])

protected lemma errors_are_roots_of_elocPolyF {i : Fin n} {ωs f : Fin n → F}
  (h : f i ≠ p.eval (ωs i)) : (ElocPolyF ωs f p).eval (ωs i) = 0 := by
  rw [←liftF_eval (f := ωs)]
  aesop (config := {warnOnNonterminal := false})
  rw [BerlekampWelch.errors_are_roots_of_elocPoly
    (i.isLt)
    (by aesop (add simp [liftF_eval]))]

@[simp]
protected lemma elocPolyF_leading_coeff_one {ωs f : Fin n → F}
  : (ElocPolyF ωs f p).leadingCoeff = 1 := by
  aesop

open BerlekampWelch
  (elocPolyF_eq_elocPoly' elocPoly_leftF_leftF_eq_contract
   elocPoly_zero elocPoly_succ)
open Fin

@[simp]
lemma elocPolyF_deg {ωs f : Fin n → F} : (ElocPolyF ωs f p).natDegree = Δ₀(f, p.eval ∘ ωs) := by
  rw [elocPolyF_eq_elocPoly']
  induction n with
  | zero =>
    simp only [elocPoly_zero, natDegree_one, hamming_zero_eq_dist]
    exact funext_iff.2 (Fin.elim0 ·)
  | succ n ih =>
    rw [
      elocPoly_succ,
      natDegree_mul (by simp)
                    (by aesop (erase simp liftF_succ)
                              (add simp [sub_eq_zero])
                              (add safe forward (X_ne_C (liftF ωs n)))),
      elocPoly_leftF_leftF_eq_contract
    ]
    aesop (config := {warnOnNonterminal := false}) (add simp [
      hammingDist.eq_def, Finset.card_filter, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ
    ]) <;> (apply Finset.sum_congr rfl; aesop (add safe (by omega)))

end

end

end ElocPoly

end BerlekampWelch
