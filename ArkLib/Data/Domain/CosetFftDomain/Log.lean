/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Fintype.Defs

import ArkLib.Data.Domain.CosetFftDomain.Mem
import ArkLib.Data.Domain.FftDomain.Mem

/-!
# Discrete logarithms in smooth FFT domains

This file defines a logarithm operation for smooth FFT domains and smooth coset
FFT domains.

Given an element of the image of a domain, `log` recovers the unique index that
maps to it.

## Main definitions

- `CosetFftDomainClass.log`: Inverse to the domain parametrization.
- `CosetFftDomain.log`: Concrete logarithm for smooth coset FFT domains.
- `FftDomain.log`: Concrete logarithm for smooth FFT domains.

## Main results

- `log_right_inverse'`: Evaluating at `log` recovers the original element.
- `log_right_inverse`: `log` is a right inverse.
- `log_left_inverse`: `log` is a left inverse.

-/

namespace Domain

variable {n : ℕ}
variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomainClass

variable {D : Type} [FunLike D (Fin (2 ^ n)) F]
variable [CosetFftDomainClass D (Fin (2 ^ n)) F]

/-- Auxiliary bounded search for the index of `x` in a smooth coset FFT domain.
  The `fuel` parameter bounds the search through `Fin (2 ^ n)`. -/
private def logAux (ω : D)
  (x : ω) (fuel : ℕ) : Fin (2 ^ n) :=
  match fuel with
  | 0 => default
  | fuel + 1 =>
    if h : fuel < 2 ^ n then
      if ω ⟨fuel, h⟩ = x then ⟨fuel, h⟩ else logAux ω x fuel
    else logAux ω x fuel

/-- Finds a preimage of `x` under the mapping `ω`. -/
def log (ω : D) (x : ω) : Fin (2 ^ n) := logAux ω x (2 ^ n)

/-- Evaluating `ω` at the index found by `log` recovers `x`. -/
@[simp]
lemma log_right_inverse' {ω : D} {x : ω} :
  ω (log ω x) = x := by
  have h_log : ∃ i : Fin (2 ^ n), ω i = x := by
    exact Finset.mem_image.mp x.2 |> fun ⟨i, _, hi⟩ ↦ ⟨i, hi⟩
  obtain ⟨i, hi⟩ := h_log
  have h_log_aux :
    ∀ (fuel : ℕ) (i : Fin (2 ^ n)),
      i.val < fuel → ω i = x → ω (logAux ω x fuel) = x := by
    intro fuel i hi hx
    induction fuel generalizing i with
    | zero => simp_all
    | succ fuel ih =>
      simp [logAux]
      grind
  exact h_log_aux _ _ (Fin.is_lt i) hi

/-- The logarithm is a right inverse to the subtype-valued parametrization of the domain. -/
lemma log_right_inverse {ω : D} :
  Function.RightInverse (log ω) (fun x ↦ ⟨ω x, by simp⟩) := fun x ↦ by simp

/-- The logarithm is a left inverse to the subtype-valued parametrization of the domain. -/
lemma log_left_inverse {ω : D} :
  Function.LeftInverse (log ω) (fun x ↦ ⟨ω x, by simp⟩) :=
    fun x ↦ CosetFftDomainClass.injective (ω := ω) (by simp)

end CosetFftDomainClass

namespace CosetFftDomain

/-- Concrete notation for the logarithm on a smooth coset FFT domain. -/
abbrev log {n : ℕ} (ω : SmoothCosetFftDomain n F) (x : ω) : Fin (2 ^ n) :=
  CosetFftDomainClass.log ω x

end CosetFftDomain

namespace FftDomain

/-- Concrete notation for the logarithm on a smooth FFT domain. -/
abbrev log {n : ℕ} (ω : SmoothFftDomain n F) (x : ω) : Fin (2 ^ n) :=
  CosetFftDomainClass.log ω x

end FftDomain

end Domain
