/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.BerlekampWelch.Condition
import ArkLib.Data.CodingTheory.BerlekampWelch.Existence
import ArkLib.Data.CodingTheory.BerlekampWelch.Sorries

/-!
  # Berlekamp-Welch decoder algorithm for Reed-Solomon codes.

  Given a codeword `f : F [X], deg f ≤ n`, Berlekamp-Welch decoder
  allows to correct up to `(n - k - 1) / 2` errors and obtain a unique source message.
-/

namespace BerlekampWelch

variable {α : Type} {F : Type} [Field F]
         {m n : ℕ} {p : Polynomial F}
         {e k : ℕ} {ωs f : Polynomial F}

open Polynomial

section

variable [DecidableEq F]

/-- Berlekamp-Welch decoder for Reed-Solomon codes.

  Given received codeword evaluations with potential errors, attempts to recover the original
  polynomial message or returns `none` if decoding fails.

  ### Parameters:
  - `e : ℕ` - Maximum number of correctable errors
  - `k : ℕ` - Degree bound of message polynomial (`<k`)
  - `[NeZero n]` - Instance that codeword length `n` is non-zero
  - `ωs : Fin n → F` - Evaluation points used during encoding
  - `f : Fin n → F` - Received (possibly corrupted) codeword evaluations

  ### Returns:
  - `some p` if successful (where `p : Polynomial F` is the recovered polynomial)
  - `none` if decoding fails (too many errors or unsolvable system)
-/
noncomputable def decoder (e k : ℕ) [NeZero n] (ωs f : Fin n → F) : Option (Polynomial F) :=
  if ‖f‖₀ ≤ e
  then some 0
  else
    let x := linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f)
    match x with
    | none => none
    | some x =>
      let E := solutionToE e k x
      let Q := solutionToQ e k x
      if Q % E = 0 then
        let p := Q / E
        if Δ₀(f, p.eval ∘ ωs) ≤ e then
          some p
        else
          none
      else
        none

/--
If the Berlekamp-Welch decoder succeeds, the decoded polynomial is within the error bound.

### Parameters:
- `[NeZero n]` - Typeclass ensuring non-zero codeword length
- `ωs : Fin n → F` - Evaluation points used in encoding
- `f : Fin n → F` - Received (possibly corrupted) codeword
- `h` - Hypothesis that decoder succeeded (returns `some p`)
-/
theorem hammingDist_le_of_decoder_eq_some [NeZero n] {ωs f : Fin n → F}
  (h : decoder e k ωs f = some p) : Δ₀(f, p.eval ∘ ωs) ≤ e :=
  by aesop (add simp decoder)

/--
**Correctness theorem for Berlekamp-Welch decoder**:
If a codeword is close to a polynomial `p` of degree `< k`
then the decoder succeeds and returns `some p`.

### Parameters:
- `e k : ℕ` - Error capacity and degree bound
- `[NeZero n]` - Non-zero codeword length
- `ωs : Fin n → F` - Distinct evaluation points (injective mapping)
- `f : Fin n → F` - Received word
- `p : Polynomial F` - Original polynomial message
-/
theorem decoder_eq_some {e k : ℕ} [NeZero n] {ωs f : Fin n → F} {p : Polynomial F}
  (he : 2 * e < n - k + 1)
  (hn : k ≤ n)
  (h_inj : Function.Injective ωs)
  (h_deg : p.natDegree < k)
  (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e)
  : decoder e k ωs f = some p := by
  simp only [decoder]
  split_ifs with hif
  · suffices p = 0 from Option.some_inj.2 this.symm
    refine poly_eq_zero_of_dist_lt h_deg hn h_inj (lt_of_le_of_lt ?p₁ he)
    transitivity ‖f‖₀ + Δ₀(f, p.eval ∘ ωs)
    · convert hammingDist_triangle 0 f (p.eval ∘ ωs) using 1 <;> simp
    · omega
  · rcases hlinsolve : linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f)
    · simp only [reduceCtorEq]; exact linsolve_always_some_berlekamp_welch h_deg h_dist hlinsolve
    · by_cases hp : p = 0
      · have : ‖f‖₀ ≤ e := by aesop
        omega
      · have h_cond := linsolve_to_BerlekampWelch_condition hlinsolve
        have h :=
          Q'_div_E'_eq_p
            h_deg he hn h_dist h_inj
            (solutionToQ_ne_zero (not_le.1 hif)
                                (BerlekampWelchCondition_iff_Solution.2 h_cond) h_inj) hp h_cond
        simp_all

/--
**Decoding failure characterization**:
When the decoder returns `none`, no valid polynomial exists within the error bound.

### Theorem Statement:
Given the decoder fails (`decoder e k ωs f = none`),
there cannot exist any polynomial `p` of degree < `k` that is
within `e` Hamming errors of the received word `f`.

### Parameters:
- `e k : ℕ` - Error capacity and degree bound
- `[NeZero n]` - Non-zero codeword length
- `ωs : Fin n → F` - Evaluation points
- `f : Fin n → F` - Received word
-/
theorem not_exists_of_decoder_eq_none {e k : ℕ} [NeZero n] {ωs f : Fin n → F}
  (he : 2 * e < n - k + 1)
  (hn : k ≤ n)
  (h_inj : Function.Injective ωs)
  (h_none : decoder e k ωs f = none)
  : ¬∃p : F[X], Δ₀(f, p.eval ∘ ωs) ≤ e ∧ p.natDegree < k := by
  intro contr
  aesop (add safe forward (decoder_eq_some))

end

end BerlekampWelch
