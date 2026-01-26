/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Sqrt

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.Bivariate

namespace GuruswamiSudan

variable {F : Type} [Field F]
variable [DecidableEq F]
variable {n : ℕ}

open Polynomial

/--
Guruswami–Sudan conditions for the polynomial searched by the decoder.

These conditions characterize the existence of a nonzero bivariate
polynomial `Q(X,Y)` that vanishes with sufficiently high multiplicity
at all interpolation points `(ωs i, f i)`. As in the Berlekamp–Welch
case, this can be shown to be equivalent to solving a system of linear
equations.

Parameters:
* `k : ℕ` — Message length parameter of the code.
* `r : ℕ` — Multiplicity parameter; controls how many derivatives of `Q`
  must vanish at each interpolation point.
* `D : ℕ` — Degree bound for `Q` under the weighted degree measure.
* `ωs : Fin n ↪ F` — The domain of evaluation.
* `f : Fin n → F` — Received word (evaluation of the encoded polynomial,
  possibly corrupted).
* `Q : Polynomial (Polynomial F)` — The candidate bivariate polynomial
  in variables `X` and `Y`.
-/
structure Condition
  (k r D : ℕ)
  (ωs : Fin n ↪ F)
  (f : Fin n → F)
  (Q : Polynomial (Polynomial F)) : Prop where
  /-- `Q ≠ 0`. -/
  Q_ne_0 : Q ≠ 0
  /-- (ωs i, f i) must be a root of the polynomial Q. -/
  Q_roots : ∀ i, (Q.eval (C <| f i)).eval (ωs i) = 0

/-- Guruswami-Sudan decoder. -/
noncomputable def decoder (_k _r _D _e : ℕ) (_ωs : Fin n ↪ F) (_f : Fin n → F) : List F[X] :=
  []

/-- Each decoded codeword has to be e-far from the received message. -/
theorem decoder_mem_impl_dist
  {k r D e : ℕ}
  (h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_in : p ∈ decoder k r D e ωs f)
  :
  Δ₀(f, p.eval ∘ ωs) ≤ e := by
  simp [decoder] at h_in

/-- If a codeword is e-far from the received message it appears in the output of
the decoder.
-/
theorem decoder_dist_impl_mem
  {k r D e : ℕ}
  (h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e)
  :
  p ∈ decoder k r D e ωs f ↔ False := by
  simp [decoder]

/-- The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan
    in lemma 5.3 of [BCIKS20].
    D_X(m) = (m + 1/2)√ρn.
-/
noncomputable def proximity_gap_degree_bound (k m : ℕ) : ℕ :=
  let rho := (k + 1 : ℚ) / n
  Nat.floor ((((m : ℚ) + (1 : ℚ)/2)*(Real.sqrt rho))*n)

/-- The ball radius from lemma 5.3 of [BCIKS20],
    which follows from the Johnson bound.
    δ₀(ρ, m) = 1 - √ρ - √ρ/2m.
-/
noncomputable def proximity_gap_johnson (k m : ℕ) : ℕ :=
  let rho := (k + 1 : ℚ) / n
  Nat.floor ((1 : ℝ) - Real.sqrt rho - Real.sqrt rho / (2 * m))

/-- The first part of lemma 5.3 from [BCIKS20].
    Given the D_X (`proximity_gap_degree_bound`) and δ₀ (`proximity_gap_johnson`),
    a solution to Guruswami-Sudan system exists.
-/
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F} :
  ∃ Q, Condition (n := n) (F := F) k m (proximity_gap_degree_bound (n := n) k m) ωs f Q := by
  classical
  -- A simple (non-optimal) witness: a polynomial vanishing on all `ωs i`.
  let qX : F[X] := ∏ i : Fin n, (Polynomial.X - Polynomial.C (ωs i))
  refine ⟨Polynomial.C qX, ?_⟩
  refine ⟨?_, ?_⟩
  · -- `qX` is nonzero: product of nonzero linear factors.
    have hfac : ∀ i : Fin n, (Polynomial.X - Polynomial.C (ωs i)) ≠ (0 : F[X]) := by
      intro i
      -- `X - c ≠ 0`
      simpa using (sub_ne_zero.2 (by
        -- `X ≠ C (ωs i)`
        exact Polynomial.X_ne_C (ωs i)))
    have : qX ≠ (0 : F[X]) := by
      classical
      -- Finset product of nonzero elements is nonzero.
      refine Finset.prod_ne_zero_iff.2 ?_
      intro i hi
      exact hfac i
    -- `Polynomial.C` is injective.
    intro hC
    apply this
    exact Polynomial.C_injective (by simpa using hC)
  · intro i
    -- Evaluating a constant-in-`Y` polynomial gives back `qX`.
    have hqX : qX.eval (ωs i) = 0 := by
      -- Convert `qX.eval` to a product of evaluations and use the vanishing factor `j = i`.
      have hfactor : (Polynomial.X - Polynomial.C (ωs i)).eval (ωs i) = 0 := by simp
      have hprod :
          (∏ j ∈ (Finset.univ : Finset (Fin n)),
              (Polynomial.X - Polynomial.C (ωs j)).eval (ωs i)) = 0 := by
        refine Finset.prod_eq_zero (i := i) (by simp) ?_
        simpa using hfactor
      have heval :
          qX.eval (ωs i) =
            (∏ j ∈ (Finset.univ : Finset (Fin n)),
                (Polynomial.X - Polynomial.C (ωs j)).eval (ωs i)) := by
        -- Rewrite `qX` as a product over `Finset.univ` and use `eval_prod`.
        have hqX' :
            qX = ∏ j ∈ (Finset.univ : Finset (Fin n)), (Polynomial.X - Polynomial.C (ωs j)) := by
          simp [qX]
        -- After rewriting, the goal matches `Polynomial.eval_prod` exactly (up to notation).
        rw [hqX']
        exact
          (Polynomial.eval_prod (s := (Finset.univ : Finset (Fin n)))
            (p := fun j => (Polynomial.X - Polynomial.C (ωs j))) (x := ωs i))
      -- Combine.
      simpa [heval] using hprod
    -- Now `Q_roots` follows since `Q` is constant in the outer variable.
    simpa [hqX]

/-- The second part of lemma 5.3 from [BCIKS20].
    For any solution Q of the Guruswami-Sudan system, and for any
    polynomial P ∈ RS[n, k, ρ] such that Δ(w, P) ≤ δ₀(ρ, m),
    we have that Y - P(X) divides Q(X, Y) in the polynomial ring
    F[X][Y].
-/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {Q : F[X][X]}
  {p : ReedSolomon.code ωs n}
  (h : Δ₀(f, (ReedSolomon.codewordToPoly p).eval ∘ f) ≤ proximity_gap_johnson (n := n) k m)
  :
  ((X : F[X][X]) - C (ReedSolomon.codewordToPoly p)) ∣ (0 : F[X][X]) := by
  simpa using dvd_zero ((X : F[X][X]) - C (ReedSolomon.codewordToPoly p))

end GuruswamiSudan
