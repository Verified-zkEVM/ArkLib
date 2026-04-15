/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Stefano Rocca
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Sqrt

import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic
/-! # Guruswami-Sudan Decoder -/



open Finset Finsupp Polynomial Polynomial.Bivariate ReedSolomon

--Let `F` be a field (finite).
variable {F : Type} [Field F] [DecidableEq F]
--Let `k + 1` be the **dimension** of the code.
variable {k : ℕ}
--Let `n` be the **blocklength** of the code.
variable {n : ℕ}
--Let `m` be a natural number, serving as the **multiplicity parameter**.
variable {m : ℕ}
--Let `ωs` be the **domain of evaluation**, i.e. the interpolation points.
variable {ωs : Fin n ↪ F}
--Let `f` be the **received word**, possibly corrupted.
variable {f : Fin n → F}

namespace GuruswamiSudan

variable (k m) in
/--
Guruswami–Sudan conditions for the polynomial searched by the decoder.

These conditions characterize a nonzero bivariate polynomial `Q(X,Y)`
with bounded weighted degree that vanishes with sufficiently high
multiplicity at all interpolation points `(ωs i, f i)`. As in the
Berlekamp–Welch case, finding such a polynomial can be shown to be
equivalent to solving a system of linear equations.

Here:
* `D : ℕ` — the **degree bound** for `Q` under the weighted degree measure.
* `ωs : Fin n ↪ F` — the **domain of evaluation**, i.e. the interpolation points.
* `f : Fin n → F` — the **received word**.
  It is the evaluation of the encoded polynomial, possibly corrupted.
* `Q : F[X][Y]` — The candidate bivariate polynomial.
-/
structure Conditions (D : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) (Q : F[X][Y]) where
  /-- The polynomial is non-zero. -/
  Q_ne_0 : Q ≠ 0
  /-- (1, k-1)-weighted degree of the polynomial is bounded. -/
  Q_deg : weightedDegree Q 1 (k - 1) ≤ D
  /-- (ωs i, f i) must be root of the polynomial Q. -/
  Q_roots : ∀ i, (Q.eval (C <| f i)).eval (ωs i) = 0
  /-- Multiplicity of the roots is at least m. -/
  Q_multiplicity : ∀ i, m ≤ rootMultiplicity Q (ωs i) (f i)

/-- Guruswami-Sudan decoder. -/
opaque decoder (k r D e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) : List F[X] := sorry

/-- Each decoded codeword has to be e-far from the received message. -/
theorem decoder_mem_impl_dist
    {k r D e : ℕ}
  (h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_in : p ∈ decoder k r D e ωs f) :
  Δ₀(f, p.eval ∘ ωs) ≤ e := by sorry

/-- If a codeword is e-far from the received message it appears in the output of
    the decoder. -/
theorem decoder_dist_impl_mem
    {k r D e : ℕ}
  (h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e) :
  p ∈ decoder k r D e ωs f := by sorry

/-- Existence of a solution to the Guruswami-Sudan decoder.
    It is the first part of Lemma 5.3 from [BCIKS20]. -/
theorem proximity_gap_existence (k n : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) (hm : 1 ≤ m) :
    ∃ Q, Conditions k m (proximity_gap_degree_bound k n m) ωs f Q := by
  use polySol k n m ωs f
  exact ⟨polySol_ne_zero, polySol_weightedDegree_le, polySol_roots hm, polySol_multiplicity⟩

/-- Given any Reed-Solomon code `p`, any solution of the Guruswami-Sudan decoder is
    divisible by `Y - P(X)`, where `P(X)` is the polynomial corresponding to the codeword `p`.
    It is the first part of Lemma 5.3 from [BCIKS20]. -/
theorem proximity_gap_divisibility (hk : k + 1 ≤ n) (hm : 1 ≤ m) (p : code ωs k)
    {Q : F[X][Y]} (hQ : Conditions k m (proximity_gap_degree_bound k n m) ωs f Q)
    (h_dist : (hammingDist f (fun i ↦ (codewordToPoly p).eval (ωs i)) : ℝ) / n <
      proximity_gap_johnson k n m) :
    X - C (codewordToPoly p) ∣ Q :=
  dvd_property (f := f) hk hm p hQ.Q_deg hQ.Q_multiplicity h_dist

end GuruswamiSudan
