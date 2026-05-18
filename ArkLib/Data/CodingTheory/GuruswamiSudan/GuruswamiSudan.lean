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

/-- GS existence with rate-corrected degree bound (ρ = k/n). Requires k > 1
    for the counting argument and m ≥ 1 for multiplicity. -/
theorem gs_existence (k n : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F)
    (hk : 1 < k) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ Q, Conditions k m (gs_degree_bound k n m) ωs f Q := by
  set D := gs_degree_bound k n m
  have hcount := gs_numVars_gt_numConstraints_of_gt_one hn hk hm
  obtain ⟨c, hc_ne, hc_zero⟩ := exists_nonzero_solution_gen k n m ωs f D hcount
  use coeffsToPoly k D c
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- ne_zero
    have h_inj : Function.Injective (coeffsToPoly (F := F) k D) := by
      have : Function.Injective (linearCombination F
        (fun p : weigthBoundIndices k D ↦ monomial (F := F) p.1.1 p.1.2)) :=
        linearIndependent_monomials.comp _ (fun p q h ↦ by aesop)
      exact this.comp (LinearEquiv.injective _)
    exact fun h ↦ hc_ne <| h_inj <| by simpa using h
  · -- weightedDegree
    convert Option.some_le_some.mpr (natWeightedDegree_coeffsToPoly_le k D c) using 1
    exact weightedDegree_eq_natWeightedDegree
  · -- roots
    intro i
    exact eval_eq_zero_of_constraint_zero hm fun s t hst ↦ by
      simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk] at hc_zero
      have := congr_fun (congr_fun hc_zero i) ⟨(s, t), Finset.mem_filter.2
        ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by linarith),
          Finset.mem_range.mpr (by linarith)⟩, by linarith⟩⟩
      aesop
  · -- multiplicity
    intro i
    apply rootMultiplicity_ge_of_shift_zero
    · have h_inj : Function.Injective (coeffsToPoly (F := F) k D) := by
        have : Function.Injective (linearCombination F
          (fun p : weigthBoundIndices k D ↦ monomial (F := F) p.1.1 p.1.2)) :=
          linearIndependent_monomials.comp _ (fun p q h ↦ by aesop)
        exact this.comp (LinearEquiv.injective _)
      exact fun h ↦ hc_ne <| h_inj <| by simpa using h
    · intro s t hst
      have h := congr_fun (congr_fun hc_zero i) ⟨(s, t), by
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by linarith),
          Finset.mem_range.mpr (by linarith)⟩, by linarith⟩⟩
      -- Mirror the approach in polySol_multiplicity:
      -- unfold constraintMap in hc_zero, extract component
      simp only [constraintMap, LinearMap.coe_mk, AddHom.coe_mk] at hc_zero
      have := congr_fun (congr_fun hc_zero i) ⟨(s, t), by
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by linarith),
          Finset.mem_range.mpr (by linarith)⟩, by linarith⟩⟩
      aesop

/-- GS divisibility with rate-corrected Johnson radius (ρ = k/n). -/
theorem gs_divisibility (hk : k + 1 ≤ n) (hm : 1 ≤ m) (p : code ωs k)
    {Q : F[X][Y]} (hQ : Conditions k m (gs_degree_bound k n m) ωs f Q)
    (h_dist : (hammingDist f (fun i ↦ (codewordToPoly p).eval (ωs i)) : ℝ) / n <
      gs_johnson k n m) :
    X - C (codewordToPoly p) ∣ Q :=
  gs_dvd_property (f := f) hk hm p hQ.Q_deg hQ.Q_multiplicity h_dist

end GuruswamiSudan
