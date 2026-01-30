/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.RatFunc.Basic

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.JohnsonBound.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.Bivariate

namespace GuruswamiSudan

variable {F : Type} [Field F]
variable [DecidableEq F]
variable {n : ℕ}

open Polynomial
open scoped BigOperators
open scoped Polynomial.Bivariate

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

/-- The set of derivative-index pairs `(a,b)` with `a + b < m` used in multiplicity-`m`
interpolation constraints. -/
def multiplicityPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.product (Finset.range m) (Finset.range m)).filter fun ab => ab.1 + ab.2 < m

lemma mem_multiplicityPairs_of_add_lt {m a b : ℕ} (h : a + b < m) :
    (a, b) ∈ multiplicityPairs m := by
  classical
  have ha : a < m := lt_of_le_of_lt (Nat.le_add_right a b) h
  have hb : b < m := lt_of_le_of_lt (Nat.le_add_left b a) (by simpa [Nat.add_comm] using h)
  refine Finset.mem_filter.2 ?_
  refine ⟨?_, h⟩
  exact Finset.mem_product.2 ⟨Finset.mem_range.2 ha, Finset.mem_range.2 hb⟩

private def multiplicityPairsRowEmbedding (a : ℕ) : ℕ ↪ ℕ × ℕ :=
  ⟨fun b => (a, b), by intro b₁ b₂ h; cases h; rfl⟩

private def multiplicityPairsRow (m a : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (m - a)).map (multiplicityPairsRowEmbedding a)

private lemma multiplicityPairs_eq_disjiUnion (m : ℕ) :
    multiplicityPairs m =
      (Finset.range m).disjiUnion (multiplicityPairsRow m) (by
        classical
        intro a₁ _ a₂ _ hne
        refine Finset.disjoint_left.2 ?_
        intro x hx₁ hx₂
        rcases x with ⟨a, b⟩
        have ha₁' : a₁ = a := (by
          have : b < m - a₁ ∧ a₁ = a := by
            simpa [multiplicityPairsRow, multiplicityPairsRowEmbedding] using hx₁
          exact this.2)
        have ha₂' : a₂ = a := (by
          have : b < m - a₂ ∧ a₂ = a := by
            simpa [multiplicityPairsRow, multiplicityPairsRowEmbedding] using hx₂
          exact this.2)
        exact hne (ha₁'.trans ha₂'.symm)) := by
  classical
  ext x
  rcases x with ⟨a, b⟩
  constructor
  · intro hx
    have hxprod : (a, b) ∈ Finset.product (Finset.range m) (Finset.range m) :=
      (Finset.mem_filter.1 hx).1
    have ha : a < m := Finset.mem_range.1 (Finset.mem_product.1 hxprod).1
    have hab : a + b < m := (Finset.mem_filter.1 hx).2
    have ha_le : a ≤ m := Nat.le_of_lt ha
    have hadd : a + (m - a) = m := by
      -- `m - a + a = m`, then commute.
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.sub_add_cancel ha_le)
    have hb : b < m - a := by
      have hab' : a + b < a + (m - a) := by simpa [hadd] using hab
      exact Nat.lt_of_add_lt_add_left hab'
    refine Finset.mem_disjiUnion.2 ?_
    refine ⟨a, Finset.mem_range.2 ha, ?_⟩
    simpa [multiplicityPairsRow, multiplicityPairsRowEmbedding] using hb
  · intro hx
    rcases Finset.mem_disjiUnion.1 hx with ⟨a₀, ha₀, hxrow⟩
    have hxrow' : b < m - a₀ ∧ a₀ = a := by
      simpa [multiplicityPairsRow, multiplicityPairsRowEmbedding] using hxrow
    rcases hxrow' with ⟨hb, ha₀a⟩
    cases ha₀a
    have ha : a < m := Finset.mem_range.1 ha₀
    have hb' : b < m := lt_of_lt_of_le hb (Nat.sub_le _ _)
    have hadd : a + (m - a) = m := by
      have ha_le : a ≤ m := Nat.le_of_lt ha
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.sub_add_cancel ha_le)
    have hab : a + b < m := by
      have : a + b < a + (m - a) := Nat.add_lt_add_left hb a
      simpa [hadd] using this
    refine Finset.mem_filter.2 ?_
    refine ⟨Finset.mem_product.2 ⟨Finset.mem_range.2 ha, Finset.mem_range.2 hb'⟩, hab⟩

private lemma sum_range_sub (m : ℕ) : (∑ a ∈ Finset.range m, (m - a)) = m * (m + 1) / 2 := by
  classical
  cases m with
  | zero => simp
  | succ m =>
      have hreflect :
          (∑ j ∈ Finset.range m.succ, (m.succ - 1 - j + 1)) =
            ∑ j ∈ Finset.range m.succ, (j + 1) := by
        simpa using (Finset.sum_range_reflect (fun t : ℕ => t + 1) m.succ)
      have hleft :
          (∑ j ∈ Finset.range m.succ, (m.succ - 1 - j + 1)) =
            ∑ j ∈ Finset.range m.succ, (m.succ - j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hjle : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
        -- `m.succ - 1 - j + 1 = m.succ - j`.
        simp [Nat.succ_sub hjle, Nat.succ_eq_add_one]
      have hsum_eq :
          (∑ j ∈ Finset.range m.succ, (m.succ - j)) = ∑ j ∈ Finset.range m.succ, (j + 1) :=
        hleft.symm.trans hreflect
      have hsum_succ :
          (∑ j ∈ Finset.range m.succ, (j + 1)) =
            (∑ j ∈ Finset.range m.succ, j) + m.succ := by
        calc
          ∑ j ∈ Finset.range m.succ, (j + 1) =
              (∑ j ∈ Finset.range m.succ, j + ∑ _j ∈ Finset.range m.succ, 1) := by
                simp [Finset.sum_add_distrib, Nat.add_assoc, Nat.add_comm]
          _ = (∑ j ∈ Finset.range m.succ, j) + m.succ := by
                simp
      -- Reduce to the Gauss formula and a small division identity.
      have hdiv :
          (m + 1) * m / 2 + (m + 1) = (m + 1) * (m + 1 + 1) / 2 := by
        have h :=
          Nat.add_mul_div_right ((m + 1) * m) (m + 1) (z := 2) (by decide : 0 < 2)
        have hrewrite :
            (m + 1) * m / 2 + (m + 1) = ((m + 1) * m + (m + 1) * 2) / 2 := by
          simpa using h.symm
        have hn : (m + 1) * m + (m + 1) * 2 = (m + 1) * (m + 2) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (Nat.mul_add (m + 1) m 2).symm
        simp [hrewrite, hn, Nat.add_left_comm, Nat.add_comm]
      -- Finish.
      have : (∑ a ∈ Finset.range m.succ, (m.succ - a)) = m.succ * (m.succ + 1) / 2 := by
        rw [hsum_eq, hsum_succ, Finset.sum_range_id]
        -- `m.succ * (m.succ - 1) / 2 + m.succ = m.succ * (m.succ + 1) / 2`.
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hdiv
      simpa [Nat.succ_eq_add_one] using this

lemma card_multiplicityPairs (m : ℕ) : (multiplicityPairs m).card = m * (m + 1) / 2 := by
  classical
  rw [multiplicityPairs_eq_disjiUnion (m := m)]
  rw [Finset.card_disjiUnion]
  -- Each row has size `m - a`.
  simp [multiplicityPairsRow, multiplicityPairsRowEmbedding, sum_range_sub (m := m)]

lemma card_multiplicityPairs_cast (m : ℕ) :
    ((multiplicityPairs m).card : ℝ) = (m : ℝ) * (m + 1) / 2 := by
  classical
  have hdiv : (2 : ℕ) ∣ m * (m + 1) := by
    exact (even_iff_two_dvd).1 (Nat.even_mul_succ_self m)
  have hcard : (multiplicityPairs m).card = m * (m + 1) / 2 := card_multiplicityPairs (m := m)
  calc
    ((multiplicityPairs m).card : ℝ) = (m * (m + 1) / 2 : ℝ) := by
      exact_mod_cast hcard
    _ = (m * (m + 1) : ℝ) / 2 := by
      simp
    _ = (m : ℝ) * (m + 1) / 2 := by
      simp

/-- The ring hom shifting a bivariate polynomial by `(x,y)`: `Q(X+x, Y+y)`. -/
noncomputable def shiftAtRingHom (x y : F) : F[X][Y] →+* F[X][Y] :=
  (Polynomial.mapRingHom (Polynomial.compRingHom (Polynomial.X + Polynomial.C x))).comp
    (Polynomial.compRingHom (Y + Polynomial.C (Polynomial.C y)))

/-- Shift a bivariate polynomial so that `(x,y)` becomes the origin: `Q(X+x, Y+y)`. -/
noncomputable def shiftAt (Q : F[X][Y]) (x y : F) : F[X][Y] :=
  shiftAtRingHom (F := F) x y Q

/-- `shiftAtRingHom` as an `F`-algebra homomorphism (hence `F`-linear). -/
noncomputable def shiftAtAlgHom (x y : F) : F[X][Y] →ₐ[F] F[X][Y] where
  toRingHom := shiftAtRingHom (F := F) x y
  commutes' a := by
    -- `shiftAtRingHom` is built from `mapRingHom` and `compRingHom`, both of which fix constants.
    simp [shiftAtRingHom]

/--
A multiplicity-aware Guruswami–Sudan interpolation condition.

We encode multiplicity `m` by requiring that after shifting the polynomial to each interpolation
point `(ωs i, f i)`, all bivariate coefficients of total degree `< m` vanish. This is equivalent
to vanishing of all Hasse derivatives of total order `< m`, but is more convenient for a linear
algebra construction.
-/
structure GSCondition
  (k m D : ℕ)
  (ωs : Fin n ↪ F)
  (f : Fin n → F)
  (Q : Polynomial (Polynomial F)) : Prop where
  /-- `Q ≠ 0`. -/
  Q_ne_0 : Q ≠ 0
  /-- Weighted-degree bound `wdeg_{1,k-1}(Q) ≤ D`. -/
  Q_deg : Polynomial.Bivariate.natWeightedDegree Q 1 (k - 1) ≤ D
  /-- Multiplicity constraints at each interpolation point. -/
  Q_vanish :
    ∀ i a b, a + b < m →
      Polynomial.Bivariate.coeff
          (shiftAt Q (ωs i) (f i))
          a b = 0

section Sudan

open Polynomial.Bivariate

omit [DecidableEq F] in
private lemma eval_eval_eq_eval₂_evalRingHom (Q : Polynomial (Polynomial F)) (p : F[X]) (x : F) :
    (Q.eval p).eval x = Q.eval₂ (Polynomial.evalRingHom x) (p.eval x) := by
  simpa [Polynomial.eval, Polynomial.eval₂] using
    (Polynomial.hom_eval₂ (p := Q) (f := RingHom.id (Polynomial F))
      (g := Polynomial.evalRingHom x) (x := p))

omit [DecidableEq F] in
private lemma eval_eval_C_eq_eval₂_evalRingHom (Q : Polynomial (Polynomial F)) (a x : F) :
    (Q.eval (Polynomial.C a)).eval x = Q.eval₂ (Polynomial.evalRingHom x) a := by
  simpa [Polynomial.eval, Polynomial.eval₂] using
    (Polynomial.hom_eval₂ (p := Q) (f := RingHom.id (Polynomial F))
      (g := Polynomial.evalRingHom x) (x := Polynomial.C a))

private lemma natDegree_eval_le_natWeightedDegree (Q : Polynomial (Polynomial F)) {k : ℕ}
    {p : F[X]} (hp : p.natDegree < k) :
    (Q.eval p).natDegree ≤ natWeightedDegree Q 1 (k - 1) := by
  classical
  by_cases hQ : Q = 0
  · subst hQ
    simp [natWeightedDegree]
  -- Expand `Q.eval p` as a sum over its support.
  have hp_le : p.natDegree ≤ k - 1 := Nat.le_pred_of_lt hp
  -- The degree of the evaluation is bounded by the maximum degree of its summands.
  calc
    (Q.eval p).natDegree =
        (∑ e ∈ Q.support, Q.coeff e * p ^ e).natDegree := by
          simp [Polynomial.eval_eq_sum, Polynomial.sum]
    _ ≤ (Q.support.sup fun e => (Q.coeff e * p ^ e).natDegree) := by
          exact Polynomial.natDegree_sum_le _ _
    _ ≤ natWeightedDegree Q 1 (k - 1) := by
          -- Compare each summand to the weighted-degree bound and take `sup`.
          refine (Finset.sup_le_iff).2 ?_
          intro e he
          have hmul :
              (Q.coeff e * p ^ e).natDegree ≤ (Q.coeff e).natDegree + (k - 1) * e := by
            have hpow : (p ^ e).natDegree ≤ e * (k - 1) := by
              have hpow' : (p ^ e).natDegree ≤ e * p.natDegree := Polynomial.natDegree_pow_le
              exact le_trans hpow' (Nat.mul_le_mul_left e hp_le) |>.trans_eq (by ac_rfl)
            calc
              (Q.coeff e * p ^ e).natDegree ≤ (Q.coeff e).natDegree + (p ^ e).natDegree :=
                Polynomial.natDegree_mul_le
              _ ≤ (Q.coeff e).natDegree + (k - 1) * e := by
                exact Nat.add_le_add_left (by simpa [Nat.mul_comm] using hpow) _
          -- `f e ≤ sup f`.
          exact le_trans hmul (by
            simpa [natWeightedDegree] using
              (Finset.le_sup (s := Q.support)
                (f := fun m => 1 * (Q.coeff m).natDegree + (k - 1) * m) he))

omit [DecidableEq F] in
private lemma shiftAt_eval_eq_comp_eval (Q : Polynomial (Polynomial F)) (p : F[X]) (x y : F) :
    (shiftAt Q x y).eval (p.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y) =
      (Q.eval p).comp (Polynomial.X + Polynomial.C x) := by
  classical
  let φ : F[X] →+* F[X] := Polynomial.compRingHom (Polynomial.X + Polynomial.C x)
  -- First commute the coefficient-map `map` with evaluation.
  have hmap :
      (shiftAt Q x y).eval (p.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y) =
        (Q.comp (Y + Polynomial.C (Polynomial.C y))).eval₂ φ
          (p.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y) := by
    -- `shiftAt` is `map` after `comp`, and `eval` is `eval₂` with the identity hom.
    simpa [shiftAt, shiftAtRingHom, φ, Polynomial.eval] using
      (Polynomial.eval₂_map (p := Q.comp (Y + Polynomial.C (Polynomial.C y)))
        (f := φ) (g := RingHom.id (F[X]))
        (x := (p.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y)))
  -- Use `eval₂_comp` to push evaluation through the `Y`-shift.
  have hcomp :
      (Q.comp (Y + Polynomial.C (Polynomial.C y))).eval₂ φ
            (p.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y) =
          Q.eval₂ φ
            ((p.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y) + Polynomial.C y) := by
    -- `eval₂` of a composition is evaluation at the evaluated inner polynomial.
    rw [
      Polynomial.eval₂_comp (f := φ) (p := Q) (q := (Y + Polynomial.C (Polynomial.C y)))
        (x := (p.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y)),
    ]
    -- Evaluate `Y + y` at `p(X+x) - y`.
    simp [φ, sub_eq_add_neg, add_comm]
  -- Simplify the shifted evaluation point and apply `eval₂_hom` for the `X`-shift.
  calc
    (shiftAt Q x y).eval (p.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y)
        = (Q.comp (Y + Polynomial.C (Polynomial.C y))).eval₂ φ
            (p.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y) := hmap
    _ =
        Q.eval₂ φ
          ((p.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y) + Polynomial.C y) := hcomp
    _ = Q.eval₂ φ (p.comp (Polynomial.X + Polynomial.C x)) := by simp [sub_eq_add_neg, add_assoc]
    _ = φ (Q.eval p) := by
      -- `p.comp (X + C x)` is exactly `φ p`.
      simpa [Polynomial.eval, φ] using (Polynomial.eval₂_hom (f := φ) (p := Q) (x := p))
    _ = (Q.eval p).comp (Polynomial.X + Polynomial.C x) := by rfl

omit [DecidableEq F] in
private lemma pow_X_sub_C_dvd_eval_of_vanish {m : ℕ} {Q : F[X][Y]} {x y : F}
    (hvanish :
      ∀ a b, a + b < m → Polynomial.Bivariate.coeff (shiftAt Q x y) a b = 0)
    {p : F[X]} (hagree : y = p.eval x) :
    ((Polynomial.X - Polynomial.C x) ^ m) ∣ Q.eval p := by
  classical
  let g : F[X][Y] := shiftAt Q x y
  let r : F[X] := p.comp (Polynomial.X + Polynomial.C x) - Polynomial.C y
  have hXr : (Polynomial.X : F[X]) ∣ r := by
    refine (Polynomial.X_dvd_iff).2 ?_
    have : r.eval 0 = 0 := by
      -- `r(0) = p(x) - y`.
      simp [r, Polynomial.eval_comp, hagree]
    simpa [Polynomial.coeff_zero_eq_eval_zero] using this

  have hterm : ∀ b ∈ g.support, (Polynomial.X ^ m : F[X]) ∣ g.coeff b * r ^ b := by
    intro b hb
    -- From the coefficient-vanishing condition, `g.coeff b` is divisible by `X^(m-b)`.
    have hcoeff : (Polynomial.X ^ (m - b) : F[X]) ∣ g.coeff b := by
      refine (Polynomial.X_pow_dvd_iff).2 ?_
      intro d hd
      have hdb : d + b < m := by omega
      have := hvanish d b hdb
      simpa [Polynomial.Bivariate.coeff, g] using this
    -- Since `X ∣ r`, we also have `X^b ∣ r^b`.
    have hrpow : (Polynomial.X ^ b : F[X]) ∣ r ^ b := pow_dvd_pow_of_dvd hXr b
    -- Combine the two divisibility statements and adjust the exponent to `m`.
    have hmul : (Polynomial.X ^ (m - b) * Polynomial.X ^ b : F[X]) ∣ g.coeff b * r ^ b :=
      mul_dvd_mul hcoeff hrpow
    have hmul' : (Polynomial.X ^ (m - b + b) : F[X]) ∣ g.coeff b * r ^ b := by
      convert hmul using 1
      · simp [pow_add, mul_comm]
    have hm_le : m ≤ m - b + b := by
      by_cases hb' : b ≤ m
      · simp [Nat.sub_add_cancel hb']
      · have hm_le_b : m ≤ b := Nat.le_of_not_ge hb'
        have hsub : m - b = 0 := Nat.sub_eq_zero_of_le hm_le_b
        simp [hsub]
        exact hm_le_b
    have : (Polynomial.X ^ m : F[X]) ∣ Polynomial.X ^ (m - b + b) := pow_dvd_pow _ hm_le
    exact this.trans hmul'

  have hdiv : (Polynomial.X ^ m : F[X]) ∣ g.eval r := by
    have : g.eval r = ∑ b ∈ g.support, g.coeff b * r ^ b := by
      simp [Polynomial.eval_eq_sum, Polynomial.sum, g]
    rw [this]
    exact Finset.dvd_sum hterm

  have hcomp : (Polynomial.X ^ m : F[X]) ∣ (Q.eval p).comp (Polynomial.X + Polynomial.C x) := by
    have : g.eval r = (Q.eval p).comp (Polynomial.X + Polynomial.C x) := by
      simpa [g, r] using shiftAt_eval_eq_comp_eval (Q := Q) (p := p) (x := x) (y := y)
    simpa [this] using hdiv

  -- Translate divisibility at `0` back to divisibility at `x`.
  exact (Polynomial.X_sub_C_pow_dvd_iff (p := Q.eval p) (t := x) (n := m)).2 hcomp

theorem divides_of_close_of_roots {k D e : ℕ} [NeZero k] {ωs : Fin n ↪ F} {f : Fin n → F}
    {Q : Polynomial (Polynomial F)}
    (hQdeg : natWeightedDegree Q 1 (k - 1) ≤ D)
    (hQroots : ∀ i, (Q.eval (Polynomial.C (f i))).eval (ωs i) = 0)
    {p : F[X]} (hpdeg : p.natDegree < k)
    (hdist : Δ₀(f, p.eval ∘ ωs) ≤ e)
    (hD : D < n - e) :
    (Polynomial.X - Polynomial.C p) ∣ Q := by
  classical
  -- Let `A` be the set of agreement positions between `f` and `p.eval ∘ ωs`.
  let A : Finset (Fin n) := Finset.filter (fun i => f i = p.eval (ωs i)) Finset.univ
  have hA_card : D < A.card := by
    have hcard_univ : (Finset.univ : Finset (Fin n)).card = n := by simp
    have hA :
        A.card = n - Δ₀(f, p.eval ∘ ωs) := by
      -- `A` and the disagreement set partition `univ`.
      have hpartition :
          A.card + (Finset.filter (fun i => ¬ f i = p.eval (ωs i)) Finset.univ).card = n := by
        have h :=
          (Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin n)))
            (p := fun i => f i = p.eval (ωs i)))
        simp [hcard_univ] at h
        exact h
      -- `Δ₀` is the disagreement count.
      have hdist_def :
          (Finset.filter (fun i => ¬ f i = p.eval (ωs i)) Finset.univ).card =
            Δ₀(f, p.eval ∘ ωs) := by
        -- `hammingDist` uses the predicate `≠`.
        simp [hammingDist]
      -- Solve for `A.card`.
      have h' := Nat.eq_sub_of_add_eq hpartition
      simp [hdist_def] at h'
      exact h'
    have hA_ge : n - e ≤ A.card := by
      -- Since `Δ₀ ≤ e`, the agreement count is at least `n - e`.
      have : n - e ≤ n - Δ₀(f, p.eval ∘ ωs) := Nat.sub_le_sub_left hdist n
      simpa [hA] using this
    exact lt_of_lt_of_le hD hA_ge

  -- Consider the univariate polynomial `R(X) = Q(X, p(X))`.
  let R : F[X] := Q.eval p
  have hRdeg : R.natDegree ≤ D := by
    have hRdeg' : R.natDegree ≤ natWeightedDegree Q 1 (k - 1) :=
      natDegree_eval_le_natWeightedDegree (F := F) (Q := Q) (k := k) (p := p) hpdeg
    exact le_trans hRdeg' hQdeg

  -- `R` vanishes on all agreement points.
  have hvanish : ∀ i ∈ A, R.eval (ωs i) = 0 := by
    intro i hiA
    have hfi : f i = p.eval (ωs i) := by simpa [A] using (Finset.mem_filter.1 hiA).2
    -- Rewrite both evaluations as `eval₂` over `evalRingHom`.
    have hQ0 : Q.eval₂ (Polynomial.evalRingHom (ωs i)) (f i) = 0 := by
      -- `hQroots` is exactly `Q(X, f(i)) = 0` at `X = ωs i`.
      have := hQroots i
      -- Convert `(Q.eval (C (f i))).eval (ωs i)` into `eval₂`.
      simpa [eval_eval_C_eq_eval₂_evalRingHom (F := F) (Q := Q) (a := f i) (x := ωs i)] using this
    have : Q.eval₂ (Polynomial.evalRingHom (ωs i)) (p.eval (ωs i)) = 0 := by simpa [hfi] using hQ0
    -- Now convert back to `(Q.eval p).eval (ωs i)`.
    simpa [R, eval_eval_eq_eval₂_evalRingHom (F := F) (Q := Q) (p := p) (x := ωs i)] using this

  -- If `R ≠ 0` then it has too many distinct roots.
  by_cases hR0 : R = 0
  · -- Factor theorem: `Q.eval p = 0` implies `(Y - p(X)) ∣ Q`.
    have : Polynomial.IsRoot Q p := by simpa [Polynomial.IsRoot, R] using hR0
    exact (Polynomial.dvd_iff_isRoot).2 this
  · have hsubset : (A.image ωs) ⊆ R.roots.toFinset := by
      intro x hx
      rcases Finset.mem_image.1 hx with ⟨i, hiA, rfl⟩
      have hx0 : R.eval (ωs i) = 0 := hvanish i hiA
      have hroot : R.IsRoot (ωs i) := hx0
      have : ωs i ∈ R.roots := (Polynomial.mem_roots hR0).2 hroot
      simpa [Multiset.mem_toFinset] using this
    have hcard_image : (A.image ωs).card = A.card := by
      simpa using (Finset.card_image_of_injective (s := A) ωs.injective)
    have hn_le : A.card ≤ R.roots.toFinset.card := by
      have := Finset.card_le_card hsubset
      simpa [hcard_image] using this
    have hn_le_natDegree : A.card ≤ R.natDegree := by
      have hroots_le : R.roots.toFinset.card ≤ R.roots.card :=
        Multiset.toFinset_card_le R.roots
      exact le_trans hn_le (le_trans hroots_le (Polynomial.card_roots' R))
    have : ¬ D < A.card := not_lt_of_ge (le_trans hn_le_natDegree hRdeg)
    exact (this hA_card).elim

theorem divides_of_close_of_vanish {k m D e : ℕ} [NeZero k] {ωs : Fin n ↪ F} {f : Fin n → F}
    {Q : Polynomial (Polynomial F)}
    (hQ : GSCondition k m D ωs f Q)
    {p : F[X]} (hpdeg : p.natDegree < k)
    (hdist : Δ₀(f, p.eval ∘ ωs) ≤ e)
    (hD : D < m * (n - e)) :
    (Polynomial.X - Polynomial.C p) ∣ Q := by
  classical
  cases m with
  | zero =>
      -- `D < 0` is impossible.
      have hD0 : False := by
        have hD0' := hD
        simp at hD0'
      exact hD0.elim
  | succ m =>
      -- Let `A` be the set of agreement positions between `f` and `p.eval ∘ ωs`.
      let A : Finset (Fin n) := Finset.filter (fun i => f i = p.eval (ωs i)) Finset.univ
      have hA_ge : n - e ≤ A.card := by
        have hcard_univ : (Finset.univ : Finset (Fin n)).card = n := by simp
        have hA :
            A.card = n - Δ₀(f, p.eval ∘ ωs) := by
          have hpartition :
              A.card + (Finset.filter (fun i => ¬ f i = p.eval (ωs i)) Finset.univ).card = n := by
            have h :=
              (Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin n)))
                (p := fun i => f i = p.eval (ωs i)))
            simp [hcard_univ] at h
            exact h
          have hdist_def :
              (Finset.filter (fun i => ¬ f i = p.eval (ωs i)) Finset.univ).card =
                Δ₀(f, p.eval ∘ ωs) := by
            simp [hammingDist]
          have h' := Nat.eq_sub_of_add_eq hpartition
          simp [hdist_def] at h'
          exact h'
        have : n - e ≤ n - Δ₀(f, p.eval ∘ ωs) := Nat.sub_le_sub_left hdist n
        simpa [hA] using this

      have hD' : D < Nat.succ m * A.card := by
        have : D < Nat.succ m * (n - e) := by simpa using hD
        exact lt_of_lt_of_le this (Nat.mul_le_mul_left (Nat.succ m) hA_ge)

      -- Consider the univariate polynomial `R(X) = Q(X, p(X))`.
      let R : F[X] := Q.eval p
      have hRdeg : R.natDegree ≤ D := by
        have hRdeg' : R.natDegree ≤ natWeightedDegree Q 1 (k - 1) :=
          natDegree_eval_le_natWeightedDegree (F := F) (Q := Q) (k := k) (p := p) hpdeg
        exact le_trans hRdeg' hQ.Q_deg

      -- If `R = 0`, we are done.
      by_cases hR0 : R = 0
      · have : Polynomial.IsRoot Q p := by simpa [Polynomial.IsRoot, R] using hR0
        exact (Polynomial.dvd_iff_isRoot).2 this
      · -- Each agreement point contributes a root of multiplicity ≥ `m+1` to `R`.
        have hrootMult :
            ∀ x ∈ A.image ωs, Nat.succ m ≤ Polynomial.rootMultiplicity x R := by
          intro x hx
          rcases Finset.mem_image.1 hx with ⟨i, hiA, rfl⟩
          have hfi : f i = p.eval (ωs i) := by simpa [A] using (Finset.mem_filter.1 hiA).2
          have hdiv : ((Polynomial.X - Polynomial.C (ωs i)) ^ Nat.succ m) ∣ R := by
            have := pow_X_sub_C_dvd_eval_of_vanish (m := Nat.succ m) (Q := Q) (x := ωs i)
              (y := f i) (hvanish := hQ.Q_vanish i) (p := p) (hagree := hfi)
            simpa [R] using this
          exact (Polynomial.le_rootMultiplicity_iff hR0).2 hdiv

        have hsubset : (A.image ωs) ⊆ R.roots.toFinset := by
          intro x hx
          rcases Finset.mem_image.1 hx with ⟨i, hiA, rfl⟩
          have hfi : f i = p.eval (ωs i) := by simpa [A] using (Finset.mem_filter.1 hiA).2
          have hdiv : (Polynomial.X - Polynomial.C (ωs i)) ∣ R := by
            have hpow : ((Polynomial.X - Polynomial.C (ωs i)) ^ Nat.succ m) ∣ R := by
              have := pow_X_sub_C_dvd_eval_of_vanish (m := Nat.succ m) (Q := Q) (x := ωs i)
                (y := f i) (hvanish := hQ.Q_vanish i) (p := p) (hagree := hfi)
              simpa [R] using this
            exact dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) hpow
          have hroot : R.IsRoot (ωs i) := (Polynomial.dvd_iff_isRoot).1 hdiv
          have : ωs i ∈ R.roots := (Polynomial.mem_roots hR0).2 hroot
          simpa [Multiset.mem_toFinset] using this

        have hsum_roots :
            (∑ x ∈ R.roots.toFinset, Polynomial.rootMultiplicity x R) = R.roots.card := by
          classical
          have : (∑ x ∈ R.roots.toFinset, R.roots.count x) = R.roots.card := by
            exact Multiset.toFinset_sum_count_eq R.roots
          simpa [Polynomial.count_roots] using this

        have hconst_le :
            Nat.succ m * (A.image ωs).card ≤ ∑ x ∈ A.image ωs, Polynomial.rootMultiplicity x R := by
          have hpoint :
              (∑ x ∈ A.image ωs, Nat.succ m) ≤
                ∑ x ∈ A.image ωs, Polynomial.rootMultiplicity x R := by
            refine Finset.sum_le_sum ?_
            intro x hx
            exact hrootMult x hx
          have hconst :
              (∑ x ∈ A.image ωs, Nat.succ m) = (A.image ωs).card * Nat.succ m := by
            simp [Finset.sum_const, mul_comm]
          calc
            Nat.succ m * (A.image ωs).card = (A.image ωs).card * Nat.succ m := by ac_rfl
            _ = ∑ x ∈ A.image ωs, Nat.succ m := by simp [hconst]
            _ ≤ ∑ x ∈ A.image ωs, Polynomial.rootMultiplicity x R := hpoint

        have hsum_le :
            (∑ x ∈ A.image ωs, Polynomial.rootMultiplicity x R) ≤
              ∑ x ∈ R.roots.toFinset, Polynomial.rootMultiplicity x R := by
          exact Finset.sum_le_sum_of_subset hsubset

        have hmul_roots : Nat.succ m * (A.image ωs).card ≤ R.roots.card := by
          have :
              Nat.succ m * (A.image ωs).card ≤
                ∑ x ∈ R.roots.toFinset, Polynomial.rootMultiplicity x R :=
            le_trans hconst_le hsum_le
          simpa [hsum_roots] using this

        have hmD : Nat.succ m * (A.image ωs).card ≤ D := by
          exact le_trans (le_trans hmul_roots (Polynomial.card_roots' R)) hRdeg

        have hcard_image : (A.image ωs).card = A.card := by
          simpa using (Finset.card_image_of_injective (s := A) ωs.injective)
        have hmD' : Nat.succ m * A.card ≤ D := by simpa [hcard_image] using hmD
        exfalso
        exact (not_lt_of_ge hmD') hD'

/-!
## Linear-algebra existence (Sudan-level)

We build the finite-dimensional space of bivariate polynomials spanned by monomials
`X^i Y^j` of weighted degree `i + (k-1)j ≤ D`, and show that if the number of such monomials
exceeds the number of interpolation constraints (`n`), then a nonzero solution to the
homogeneous interpolation system exists.
-/

/-- The finite set of exponent pairs `(i,j)` with weighted degree `i + (k-1)j ≤ D`. -/
def monomials (k D : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.product (Finset.range (D + 1)) (Finset.range (D / (k - 1) + 1))).filter fun ij =>
    ij.1 + (k - 1) * ij.2 ≤ D

/-- The number of admissible monomials. -/
def monomialCount (k D : ℕ) : ℕ :=
  (monomials k D).card

private def monomialRowEmbedding (j : ℕ) : ℕ ↪ ℕ × ℕ :=
  ⟨fun i => (i, j), by intro i₁ i₂ h; cases h; rfl⟩

private def monomialRow (k D j : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (D - (k - 1) * j + 1)).map (monomialRowEmbedding j)

private lemma monomials_eq_disjiUnion (k D : ℕ) :
    monomials k D =
      (Finset.range (D / (k - 1) + 1)).disjiUnion (monomialRow k D) (by
        classical
        intro j₁ _ j₂ _ hne
        refine Finset.disjoint_left.2 ?_
        intro x hx₁ hx₂
        rcases x with ⟨i, j⟩
        have hj₁' : j₁ = j := (by
          have : i < D - (k - 1) * j₁ + 1 ∧ j₁ = j := by
            simpa [monomialRow, monomialRowEmbedding] using hx₁
          exact this.2)
        have hj₂' : j₂ = j := (by
          have : i < D - (k - 1) * j₂ + 1 ∧ j₂ = j := by
            simpa [monomialRow, monomialRowEmbedding] using hx₂
          exact this.2)
        exact hne (hj₁'.trans hj₂'.symm)) := by
  classical
  ext x
  rcases x with ⟨i, j⟩
  constructor
  · intro hx
    have hj : j < D / (k - 1) + 1 := by
      have hxprod :
          (i, j) ∈ Finset.product (Finset.range (D + 1)) (Finset.range (D / (k - 1) + 1)) :=
        (Finset.mem_filter.1 hx).1
      have : j ∈ Finset.range (D / (k - 1) + 1) := (Finset.mem_product.1 hxprod).2
      exact Finset.mem_range.1 this
    refine Finset.mem_disjiUnion.2 ?_
    refine ⟨j, Finset.mem_range.2 hj, ?_⟩
    have hij : i + (k - 1) * j ≤ D := (Finset.mem_filter.1 hx).2
    have hi : i ≤ D - (k - 1) * j := Nat.le_sub_of_add_le hij
    have hi' : i < D - (k - 1) * j + 1 := Nat.lt_succ_iff.2 hi
    simpa [monomialRow, monomialRowEmbedding] using hi'
  · intro hx
    rcases Finset.mem_disjiUnion.1 hx with ⟨j₀, hj₀, hxrow⟩
    have hxrow' : i < D - (k - 1) * j₀ + 1 ∧ j₀ = j := by
      simpa [monomialRow, monomialRowEmbedding] using hxrow
    rcases hxrow' with ⟨hi', hj₀j⟩
    have hj₀lt : j₀ < D / (k - 1) + 1 := Finset.mem_range.1 hj₀
    have hj₀le : j₀ ≤ D / (k - 1) := Nat.le_of_lt_succ hj₀lt
    have hmul : (k - 1) * j₀ ≤ D := by
      have : j₀ * (k - 1) ≤ D := Nat.mul_le_of_le_div (k := k - 1) (x := j₀) (y := D) hj₀le
      simpa [Nat.mul_comm] using this
    have hi : i ≤ D - (k - 1) * j₀ := Nat.le_of_lt_succ hi'
    have hij : i + (k - 1) * j₀ ≤ D := by
      have := Nat.add_le_add_right hi ((k - 1) * j₀)
      have hsub : D - (k - 1) * j₀ + (k - 1) * j₀ = D := Nat.sub_add_cancel hmul
      simpa [Nat.add_assoc, hsub, Nat.add_left_comm, Nat.add_comm] using this
    have hiD : i ≤ D := le_trans hi (Nat.sub_le _ _)
    refine Finset.mem_filter.2 ?_
    refine ⟨?_, ?_⟩
    · refine Finset.mem_product.2 ?_
      refine ⟨Finset.mem_range.2 (Nat.lt_succ_iff.2 hiD), ?_⟩
      simpa [hj₀j] using hj₀
    · simpa [hj₀j] using hij

lemma monomialCount_eq_sum (k D : ℕ) :
    monomialCount k D =
      ∑ j ∈ Finset.range (D / (k - 1) + 1), (D - (k - 1) * j + 1) := by
  classical
  unfold monomialCount
  rw [monomials_eq_disjiUnion (k := k) (D := D)]
  rw [Finset.card_disjiUnion]
  simp [monomialRow, monomialRowEmbedding]

lemma monomialCount_ge_sq {k D : ℕ} (hk : 2 ≤ k) :
    (((D + 1 : ℕ) : ℝ) ^ 2) / (2 * ((k - 1 : ℕ) : ℝ)) ≤ (monomialCount (k := k) D : ℝ) := by
  classical
  let q : ℕ := D / (k - 1)
  have hkpos : 0 < k - 1 := by omega
  have hkposR : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) :=
    (Nat.cast_pos.mpr hkpos)

  have hsumNat :
      monomialCount (k := k) D = ∑ j ∈ Finset.range (q + 1), (D - (k - 1) * j + 1) := by
    simpa [q] using monomialCount_eq_sum (k := k) D

  have hsum :
      (monomialCount (k := k) D : ℝ) =
        ∑ j ∈ Finset.range (q + 1), ((D - (k - 1) * j + 1 : ℕ) : ℝ) := by
    have := congrArg (fun t : ℕ => (Nat.castRingHom ℝ) t) hsumNat
    change (Nat.castRingHom ℝ) (monomialCount (k := k) D) =
        (Nat.castRingHom ℝ) (∑ j ∈ Finset.range (q + 1), (D - (k - 1) * j + 1)) at this
    simpa [map_sum] using this

  have hq_mul_le : (k - 1) * q ≤ D := by
    simpa [q, Nat.mul_comm] using (Nat.mul_div_le D (k - 1))

  have hterm_le : ∀ j ∈ Finset.range (q + 1), (k - 1) * j ≤ D := by
    intro j hj
    have hjle : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.1 hj)
    have : (k - 1) * j ≤ (k - 1) * q := Nat.mul_le_mul_left (k - 1) hjle
    exact le_trans this hq_mul_le

  have hcast_term :
      ∀ j ∈ Finset.range (q + 1),
        ((D - (k - 1) * j + 1 : ℕ) : ℝ) =
          ((D + 1 : ℕ) : ℝ) - ((k - 1 : ℕ) : ℝ) * (j : ℝ) := by
    intro j hj
    have hjle : (k - 1) * j ≤ D := hterm_le j hj
    have hsub : ((D - (k - 1) * j : ℕ) : ℝ) = (D : ℝ) - ((k - 1 : ℕ) : ℝ) * (j : ℝ) := by
      have h' : ((D - (k - 1) * j : ℕ) : ℝ) = (D : ℝ) - (((k - 1) * j : ℕ) : ℝ) := by
        simpa using (Nat.cast_sub (R := ℝ) (m := (k - 1) * j) (n := D) hjle)
      simpa [Nat.cast_mul, mul_assoc] using h'
    calc
      ((D - (k - 1) * j + 1 : ℕ) : ℝ)
          = ((D - (k - 1) * j : ℕ) : ℝ) + 1 := by
              simp [Nat.cast_add]
      _ = (D : ℝ) - ((k - 1 : ℕ) : ℝ) * (j : ℝ) + 1 := by simp [hsub]
      _ = ((D + 1 : ℕ) : ℝ) - ((k - 1 : ℕ) : ℝ) * (j : ℝ) := by
            simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

  have hsum_closed :
      (∑ j ∈ Finset.range (q + 1), ((D - (k - 1) * j + 1 : ℕ) : ℝ)) =
        ((q + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) -
          ((k - 1 : ℕ) : ℝ) * (∑ j ∈ Finset.range (q + 1), (j : ℝ)) := by
    have hrewrite :
        (∑ j ∈ Finset.range (q + 1), ((D - (k - 1) * j + 1 : ℕ) : ℝ)) =
          ∑ j ∈ Finset.range (q + 1),
            (((D + 1 : ℕ) : ℝ) - ((k - 1 : ℕ) : ℝ) * (j : ℝ)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simpa using hcast_term j hj

    have hmul :
        (∑ j ∈ Finset.range (q + 1), ((k - 1 : ℕ) : ℝ) * (j : ℝ)) =
          ((k - 1 : ℕ) : ℝ) * (∑ j ∈ Finset.range (q + 1), (j : ℝ)) := by
      simpa using
        (Finset.mul_sum (s := Finset.range (q + 1)) (f := fun j : ℕ => (j : ℝ))
          ((k - 1 : ℕ) : ℝ)).symm

    -- Sum of an affine function.
    rw [hrewrite]
    have :
        (∑ j ∈ Finset.range (q + 1),
              (((D + 1 : ℕ) : ℝ) - ((k - 1 : ℕ) : ℝ) * (j : ℝ))) =
          (∑ _j ∈ Finset.range (q + 1), ((D + 1 : ℕ) : ℝ)) -
            ∑ j ∈ Finset.range (q + 1), ((k - 1 : ℕ) : ℝ) * (j : ℝ) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hmul]
    ring

  have hsumj' :
      (∑ j ∈ Finset.range (q + 1), (j : ℝ)) = ((q + 1 : ℕ) : ℝ) * (q : ℝ) / 2 := by
    have hnat : (∑ j ∈ Finset.range (q + 1), j) = (q + 1) * q / 2 := by
      exact (Finset.sum_range_id (n := q + 1))
    have hcast := congrArg (fun t : ℕ => (Nat.castRingHom ℝ) t) hnat
    have hL :
        (Nat.castRingHom ℝ) (∑ j ∈ Finset.range (q + 1), j) =
          ∑ j ∈ Finset.range (q + 1), (j : ℝ) := by
      simp
    have hdiv : 2 ∣ (q + 1) * q := by
      rcases Nat.even_mul_succ_self q with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      calc
        (q + 1) * q = q * (q + 1) := by simp [Nat.mul_comm]
        _ = t + t := ht
        _ = 2 * t := by simp [Nat.two_mul]
    have hR : (Nat.castRingHom ℝ) ((q + 1) * q / 2) = ((q + 1 : ℕ) : ℝ) * (q : ℝ) / 2 := by
      have :
          ((Nat.castRingHom ℝ) ((q + 1) * q / 2) : ℝ) =
            ((Nat.castRingHom ℝ) ((q + 1) * q) : ℝ) / (2 : ℝ) := by
        simpa using (Nat.cast_div_charZero (K := ℝ) (m := (q + 1) * q) (n := 2) hdiv)
      simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, this, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm]
    simpa [hL, hR] using hcast

  have hneg_le :
      ((k - 1 : ℕ) : ℝ) * (((q + 1 : ℕ) : ℝ) * (q : ℝ) / 2) ≤
        ((q + 1 : ℕ) : ℝ) * ((D : ℕ) : ℝ) / 2 := by
    have hqR : ((k - 1 : ℕ) : ℝ) * (q : ℝ) ≤ (D : ℝ) := by
      have : ((k - 1) * q : ℕ) ≤ D := hq_mul_le
      have : (((k - 1) * q : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast this
      simpa [Nat.cast_mul, mul_assoc] using this
    have hnonneg : (0 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) / 2 := by
      have : (0 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := Nat.cast_nonneg (q + 1)
      exact div_nonneg this (by norm_num)
    have := mul_le_mul_of_nonneg_left hqR hnonneg
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using this

  have hsum_lb :
      ((q + 1 : ℕ) : ℝ) * (((D + 1 : ℕ) : ℝ) / 2) ≤
        ∑ j ∈ Finset.range (q + 1), ((D - (k - 1) * j + 1 : ℕ) : ℝ) := by
    -- Put everything in closed form and compare.
    rw [hsum_closed, hsumj']
    have hsub_le :
        ((q + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) - ((q + 1 : ℕ) : ℝ) * ((D : ℕ) : ℝ) / 2 ≤
          ((q + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) -
            ((k - 1 : ℕ) : ℝ) * (((q + 1 : ℕ) : ℝ) * (q : ℝ) / 2) :=
      sub_le_sub_left hneg_le _
    have hstep :
        ((q + 1 : ℕ) : ℝ) * (((D + 1 : ℕ) : ℝ) / 2) ≤
          ((q + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) - ((q + 1 : ℕ) : ℝ) * ((D : ℕ) : ℝ) / 2 := by
      -- Rewrite the RHS as `(q+1)*(D+2)/2` and use monotonicity.
      have hEq :
          ((q + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) - ((q + 1 : ℕ) : ℝ) * ((D : ℕ) : ℝ) / 2 =
            ((q + 1 : ℕ) : ℝ) * ((D + 2 : ℕ) : ℝ) / 2 := by
        simp [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, sub_eq_add_neg, div_eq_mul_inv, mul_assoc,
          mul_comm]
        ring
      have hDle : ((D + 1 : ℕ) : ℝ) / 2 ≤ ((D + 2 : ℕ) : ℝ) / 2 := by
        have : ((D + 1 : ℕ) : ℝ) ≤ ((D + 2 : ℕ) : ℝ) := by
          exact_mod_cast (Nat.le_succ (D + 1))
        exact div_le_div_of_nonneg_right this (by norm_num)
      have hq1nonneg : (0 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := Nat.cast_nonneg (q + 1)
      have : ((q + 1 : ℕ) : ℝ) * (((D + 1 : ℕ) : ℝ) / 2) ≤
          ((q + 1 : ℕ) : ℝ) * (((D + 2 : ℕ) : ℝ) / 2) := mul_le_mul_of_nonneg_left hDle hq1nonneg
      -- Convert `((q+1)*((D+2)/2))` to `((q+1)*(D+2)/2)` and use `hEq`.
      have this' :
          ((q + 1 : ℕ) : ℝ) * (((D + 1 : ℕ) : ℝ) / 2) ≤
            ((q + 1 : ℕ) : ℝ) * ((D + 2 : ℕ) : ℝ) / 2 := by
        simpa [mul_div_assoc] using this
      calc
        ((q + 1 : ℕ) : ℝ) * (((D + 1 : ℕ) : ℝ) / 2) ≤
            ((q + 1 : ℕ) : ℝ) * ((D + 2 : ℕ) : ℝ) / 2 := this'
        _ =
            ((q + 1 : ℕ) : ℝ) * ((D + 1 : ℕ) : ℝ) -
              ((q + 1 : ℕ) : ℝ) * ((D : ℕ) : ℝ) / 2 := by
            simpa using hEq.symm
    exact le_trans hstep hsub_le

  have hD1 : D + 1 ≤ (q + 1) * (k - 1) := by
    have hmod : D % (k - 1) < k - 1 := Nat.mod_lt D hkpos
    have hmod1 : D % (k - 1) + 1 ≤ k - 1 := Nat.succ_le_of_lt hmod
    have hdecomp : (k - 1) * q + D % (k - 1) = D := by
      simpa [q] using (Nat.div_add_mod D (k - 1))
    have hrewrite : D + 1 = (k - 1) * q + (D % (k - 1) + 1) := by
      calc
        D + 1 = ((k - 1) * q + D % (k - 1)) + 1 := by simp [hdecomp]
        _ = (k - 1) * q + (D % (k - 1) + 1) := by omega
    have : (k - 1) * q + (D % (k - 1) + 1) ≤ (k - 1) * q + (k - 1) :=
      Nat.add_le_add_left hmod1 _
    have hrhs : (k - 1) * q + (k - 1) = (q + 1) * (k - 1) := by
      calc
        (k - 1) * q + (k - 1) = (k - 1) * q + 1 * (k - 1) := by simp
        _ = (q + 1) * (k - 1) := by
              simp [Nat.mul_add, Nat.mul_comm]
    convert this using 1
    · simp [hrhs]

  have hq1_ge :
      ((D + 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
    have hD1R : ((D + 1 : ℕ) : ℝ) ≤ ((q + 1) * (k - 1) : ℕ) := by exact_mod_cast hD1
    have hD1R' : ((D + 1 : ℕ) : ℝ) ≤ ((q + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) := by
      exact_mod_cast hD1R
    exact (div_le_iff₀ hkposR).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hD1R')

  have hquad :
      (((D + 1 : ℕ) : ℝ) ^ 2) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ((q + 1 : ℕ) : ℝ) * (((D + 1 : ℕ) : ℝ) / 2) := by
    have hD1nonneg : (0 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) / 2 := by
      have : (0 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) := Nat.cast_nonneg (D + 1)
      exact div_nonneg this (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hq1_ge hD1nonneg
    have hsimp :
        (((D + 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) * (((D + 1 : ℕ) : ℝ) / 2) =
          (((D + 1 : ℕ) : ℝ) ^ 2) / (2 * ((k - 1 : ℕ) : ℝ)) := by
      have hkposR' : ((k - 1 : ℕ) : ℝ) ≠ 0 := hkposR.ne'
      field_simp [hkposR']
      ring
    -- Rewrite the quadratic term into a product and apply `hmul`.
    calc
      (((D + 1 : ℕ) : ℝ) ^ 2) / (2 * ((k - 1 : ℕ) : ℝ))
          = (((D + 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) * (((D + 1 : ℕ) : ℝ) / 2) := by
              simpa using hsimp.symm
      _ ≤ ((q + 1 : ℕ) : ℝ) * (((D + 1 : ℕ) : ℝ) / 2) := hmul

  have :
      (((D + 1 : ℕ) : ℝ) ^ 2) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ∑ j ∈ Finset.range (q + 1), ((D - (k - 1) * j + 1 : ℕ) : ℝ) := by
    exact le_trans hquad hsum_lb
  simpa [hsum] using this

private lemma m_mul_m_add_one_mul_lt (m k : ℕ) :
    (m : ℝ) * (m + 1) * ((k - 1 : ℕ) : ℝ) <
      ((m : ℝ) + (1 : ℝ) / 2) ^ 2 * ((k + 1 : ℕ) : ℝ) := by
  have hk :
      ((k - 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    have hk' : k - 1 ≤ k := Nat.sub_le k 1
    have hk'' : k ≤ k + 1 := Nat.le_succ k
    exact_mod_cast (le_trans hk' hk'')
  have hmnonneg : 0 ≤ (m : ℝ) * (m + 1) := by nlinarith
  have hle :
      (m : ℝ) * (m + 1) * ((k - 1 : ℕ) : ℝ) ≤
        (m : ℝ) * (m + 1) * ((k + 1 : ℕ) : ℝ) := by
    exact mul_le_mul_of_nonneg_left hk hmnonneg
  have hsq :
      (m : ℝ) * (m + 1) + (1 : ℝ) / 4 = ((m : ℝ) + (1 : ℝ) / 2) ^ 2 := by
    ring
  have hquarter : (0 : ℝ) < (1 : ℝ) / 4 := by norm_num
  have hpos :
      (m : ℝ) * (m + 1) < ((m : ℝ) + (1 : ℝ) / 2) ^ 2 := by
    linarith [hsq, hquarter]
  have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_pos k)
  have hmul :
      (m : ℝ) * (m + 1) * ((k + 1 : ℕ) : ℝ) <
        ((m : ℝ) + (1 : ℝ) / 2) ^ 2 * ((k + 1 : ℕ) : ℝ) := by
    exact mul_lt_mul_of_pos_right hpos hkpos
  exact lt_of_le_of_lt hle hmul

private noncomputable def polyOfCoeffs (k D : ℕ) (c : monomials (k := k) D → F) :
    Polynomial (Polynomial F) :=
  ∑ ij ∈ (Finset.univ : Finset (monomials (k := k) D)),
    Polynomial.monomial ij.1.2 (Polynomial.monomial ij.1.1 (c ij))

private noncomputable def polyOfCoeffsLinear (k D : ℕ) :
    (monomials (k := k) D → F) →ₗ[F] Polynomial (Polynomial F) where
  toFun := polyOfCoeffs (F := F) k D
  map_add' c₁ c₂ := by
    classical
    simp [polyOfCoeffs, Finset.sum_add_distrib, Polynomial.monomial_add]
  map_smul' a c := by
    classical
    simp [polyOfCoeffs, Finset.smul_sum, Polynomial.smul_monomial]

omit [DecidableEq F] in
private lemma polyOfCoeffs_eval_at (k D : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F)
    (c : monomials (k := k) D → F) (i : Fin n) :
    ((polyOfCoeffs (F := F) k D c).eval (Polynomial.C (f i))).eval (ωs i) =
      ∑ ij ∈ (Finset.univ : Finset (monomials (k := k) D)),
        c ij * (f i) ^ ij.1.2 * (ωs i) ^ ij.1.1 := by
  classical
  -- Expand `polyOfCoeffs` and evaluate term-by-term.
  simp [polyOfCoeffs, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
    mul_assoc, mul_left_comm, mul_comm]

private noncomputable def constraintMap (k D : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    (monomials (k := k) D → F) →ₗ[F] (Fin n → F) where
  toFun c i := ∑ ij ∈ (Finset.univ : Finset (monomials (k := k) D)),
    c ij * (f i) ^ ij.1.2 * (ωs i) ^ ij.1.1
  map_add' c₁ c₂ := by
    classical
    funext i
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    classical
    funext i
    simp [mul_assoc, Finset.mul_sum]

private noncomputable def bCoeffLinear (a b : ℕ) : Polynomial (Polynomial F) →ₗ[F] F where
  toFun Q := Polynomial.Bivariate.coeff Q a b
  map_add' Q₁ Q₂ := by
    classical
    simp [Polynomial.Bivariate.coeff]
  map_smul' c Q := by
    classical
    simp [Polynomial.Bivariate.coeff]

private noncomputable def constraintMapMul (k D m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
    (monomials (k := k) D → F) →ₗ[F] (Fin n × (multiplicityPairs m) → F) :=
  LinearMap.pi fun idx =>
    let i : Fin n := idx.1
    let a : ℕ := idx.2.1.1
    let b : ℕ := idx.2.1.2
    (bCoeffLinear (F := F) a b).comp
      (((shiftAtAlgHom (F := F) (ωs i) (f i)).toLinearMap).comp
        (polyOfCoeffsLinear (F := F) (k := k) (D := D)))

omit [DecidableEq F] in
private lemma polyOfCoeffs_ne_zero_of_coeff_ne_zero {k D : ℕ} {c : monomials (k := k) D → F}
    (h : ∃ ij, c ij ≠ 0) :
    polyOfCoeffs (F := F) k D c ≠ 0 := by
  classical
  rcases h with ⟨ij, hij⟩
  -- Read off the corresponding bivariate coefficient.
  have hcoeff :
      ((polyOfCoeffs (F := F) k D c).coeff ij.1.2).coeff ij.1.1 = c ij := by
    -- Coefficients are computed term-by-term; only the summand at `ij` contributes.
    simp [polyOfCoeffs, Polynomial.coeff_monomial]
    -- The remaining goal is a finset sum with a single nonzero term at `ij`.
    have hsum :
        ∑ b ∈ (monomials (k := k) D).attach,
            (if b.1.2 = ij.1.2 then (Polynomial.monomial b.1.1 (c b)) else 0).coeff ij.1.1 =
          (if ij.1.2 = ij.1.2 then (Polynomial.monomial ij.1.1 (c ij)) else 0).coeff ij.1.1 := by
      refine Finset.sum_eq_single_of_mem (a := ij) (h := by simp) ?_
      intro b hb hbij
      by_cases hb₂ : b.1.2 = ij.1.2
      · have hb₁ : b.1.1 ≠ ij.1.1 := by
          intro hb₁
          apply hbij
          ext
          · exact hb₁
          · exact hb₂
        have hb₁' : ij.1.1 ≠ b.1.1 := by
          intro hb₁'
          exact hb₁ hb₁'.symm
        simp [hb₂, Polynomial.coeff_monomial, hb₁]
      · simp [hb₂]
    simpa using hsum
  intro h0
  have : c ij = 0 := by
    simpa [h0] using hcoeff.symm
  exact hij this

private lemma natWeightedDegree_polyOfCoeffs_le {k D : ℕ} [NeZero k]
    (hk : 2 ≤ k) (c : monomials (k := k) D → F) :
    natWeightedDegree (polyOfCoeffs (F := F) k D c) 1 (k - 1) ≤ D := by
  classical
  have _ := hk
  -- Expand the definition: show every support element respects the bound.
  unfold natWeightedDegree
  refine (Finset.sup_le_iff).2 ?_
  intro j hj
  have hj_coeff_ne : (polyOfCoeffs (F := F) k D c).coeff j ≠ 0 := by
    simpa using (Polynomial.mem_support_iff.1 hj)
  -- First, bound `(k-1) * j ≤ D`; otherwise no admissible monomial can have `Y`-degree `j`.
  have hj_mul_le : (k - 1) * j ≤ D := by
    by_contra hgt
    have hlt : D < (k - 1) * j := Nat.lt_of_not_ge hgt
    have hcoeff0 : (polyOfCoeffs (F := F) k D c).coeff j = 0 := by
      -- Expand `coeff j` and show all summands vanish.
      have hcoeff :
          (polyOfCoeffs (F := F) k D c).coeff j =
            ∑ ij ∈ (Finset.univ : Finset (monomials (k := k) D)),
              (if ij.1.2 = j then Polynomial.monomial ij.1.1 (c ij) else 0) := by
        ext i
        simp [polyOfCoeffs, Polynomial.coeff_monomial]
      rw [hcoeff]
      refine Finset.sum_eq_zero ?_
      intro ij hij
      have hij_ne : ij.1.2 ≠ j := by
        intro hEq
        have hij_mem' : ij.1.1 + (k - 1) * ij.1.2 ≤ D := by
          have : (ij.1.1, ij.1.2) ∈ monomials (k := k) D := ij.2
          simpa [monomials] using (Finset.mem_filter.1 this).2
        have hj_le : (k - 1) * j ≤ D := by
          have : (k - 1) * j ≤ ij.1.1 + (k - 1) * j := Nat.le_add_left _ _
          exact le_trans this (by simpa [hEq] using hij_mem')
        exact not_lt_of_ge hj_le hlt
      simp [hij_ne]
    exact hj_coeff_ne hcoeff0
  -- Next, bound the `X`-degree of the coefficient polynomial.
  have hdeg_le :
      ((polyOfCoeffs (F := F) k D c).coeff j).natDegree ≤ D - (k - 1) * j := by
    -- Expand `coeff j` into a finite sum of `X`-monomials and bound degrees termwise.
    -- (Only indices with `ij.1.2 = j` contribute.)
    have hcoeff :
        (polyOfCoeffs (F := F) k D c).coeff j =
          ∑ ij ∈ (Finset.univ : Finset (monomials (k := k) D)),
            (if ij.1.2 = j then Polynomial.monomial ij.1.1 (c ij) else 0) := by
      ext i
      simp [polyOfCoeffs, Polynomial.coeff_monomial]
    -- Use `natDegree` bound for a finite sum.
    have hsum :
        ((polyOfCoeffs (F := F) k D c).coeff j).natDegree ≤
          (Finset.univ : Finset (monomials (k := k) D)).sup fun ij =>
            if ij.1.2 = j then ij.1.1 else 0 := by
      -- Each summand has `natDegree ≤ ij.1.1`.
      rw [hcoeff]
      refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
      refine (Finset.sup_le_iff).2 ?_
      intro ij hij
      by_cases hEq : ij.1.2 = j
      · have hmon :
            (Polynomial.monomial ij.1.1 (c ij) : F[X]).natDegree ≤ ij.1.1 :=
          Polynomial.natDegree_monomial_le (a := c ij)
        have hij_le_sup :
            ij.1.1 ≤
              (Finset.univ : Finset (monomials (k := k) D)).sup fun ij =>
                if ij.1.2 = j then ij.1.1 else 0 := by
          have := Finset.le_sup (s := (Finset.univ : Finset (monomials (k := k) D)))
            (f := fun ij => if ij.1.2 = j then ij.1.1 else 0) hij
          simpa [hEq] using this
        exact le_trans (by simpa [hEq] using hmon) hij_le_sup
      · simp [hEq]
    -- Show the sup of `ij.1.1` over contributing indices is bounded by `D - (k-1) * j`.
    have hsup :
        (Finset.univ : Finset (monomials (k := k) D)).sup (fun ij =>
            if ij.1.2 = j then ij.1.1 else 0) ≤ D - (k - 1) * j := by
      refine (Finset.sup_le_iff).2 ?_
      intro ij hij
      by_cases hEq : ij.1.2 = j
      · have hij_mem : ij.1.1 + (k - 1) * j ≤ D := by
          have hij_mem' : ij.1.1 + (k - 1) * ij.1.2 ≤ D := by
            have : (ij.1.1, ij.1.2) ∈ monomials (k := k) D := ij.2
            simpa [monomials] using (Finset.mem_filter.1 this).2
          simpa [hEq] using hij_mem'
        have : ij.1.1 ≤ D - (k - 1) * j := by omega
        simpa [hEq] using this
      · simp [hEq]
    exact le_trans hsum hsup
  -- Combine: `natDegree + (k-1)j ≤ D`.
  have : ((polyOfCoeffs (F := F) k D c).coeff j).natDegree + (k - 1) * j ≤ D := by
    have :
        ((polyOfCoeffs (F := F) k D c).coeff j).natDegree + (k - 1) * j ≤
          (D - (k - 1) * j) + (k - 1) * j :=
      Nat.add_le_add_right hdeg_le _
    simpa [Nat.sub_add_cancel hj_mul_le] using this
  simpa using this

theorem exists_nonzero_interpolant {k D : ℕ} [NeZero k] (hk : 2 ≤ k) {ωs : Fin n ↪ F}
    (f : Fin n → F) (hcount : n < monomialCount (k := k) D) :
    ∃ Q : Polynomial (Polynomial F),
      Q ≠ 0 ∧
        natWeightedDegree Q 1 (k - 1) ≤ D ∧
        (∀ i, (Q.eval (Polynomial.C (f i))).eval (ωs i) = 0) := by
  classical
  -- Work in coefficient space indexed by admissible monomials.
  let S : Finset (ℕ × ℕ) := monomials (k := k) D
  let Φ : (S → F) →ₗ[F] (Fin n → F) := constraintMap (F := F) (k := k) (D := D) ωs f
  have hfinrank : Module.finrank F (Fin n → F) < Module.finrank F (S → F) := by
    -- `finrank F (Fin n → F) = n` and `finrank F (S → F) = S.card`.
    have h₁ : Module.finrank F (Fin n → F) = n := by
      simp
    have h₂ : Module.finrank F (S → F) = S.card := by
      -- `S` is a fintype via the `Finset` coercion.
      simp
    -- Convert `n < S.card` to the finrank inequality.
    have : n < S.card := by simpa [S, monomialCount] using hcount
    simpa [h₁, h₂] using this
  have hker : LinearMap.ker Φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) hfinrank
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hker with ⟨c, hcKer, hc0⟩
  -- Build the polynomial witness and prove its properties.
  refine ⟨polyOfCoeffs (F := F) (k := k) (D := D) c, ?_, ?_, ?_⟩
  · -- Nonzero: pick an index where `c` is nonzero and read off the coefficient.
    have : ∃ ij, c ij ≠ 0 := by
      by_contra h
      push_neg at h
      apply hc0
      funext ij
      simpa using h ij
    exact polyOfCoeffs_ne_zero_of_coeff_ne_zero (F := F) (k := k) (D := D) this
  · -- Weighted-degree bound.
    simpa using natWeightedDegree_polyOfCoeffs_le (F := F) (k := k) (D := D) hk c
  · intro i
    -- `c ∈ ker Φ` gives all interpolation constraints.
    have hΦ0 : Φ c = 0 := by simpa [LinearMap.mem_ker] using hcKer
    have : (Φ c) i = 0 := by simp [hΦ0]
    -- Unfold and identify with the polynomial evaluation.
    -- Rewrite the LHS via `polyOfCoeffs_eval_at`, then use the kernel condition.
    have hEval :
        ((polyOfCoeffs (F := F) (k := k) (D := D) c).eval (Polynomial.C (f i))).eval (ωs i) =
          ∑ ij ∈ (Finset.univ : Finset (monomials (k := k) D)),
            c ij * (f i) ^ ij.1.2 * (ωs i) ^ ij.1.1 :=
      polyOfCoeffs_eval_at (F := F) (k := k) (D := D) ωs f c i
    -- `constraintMap` computes the same sum.
    have : ∑ ij ∈ (Finset.univ : Finset (monomials (k := k) D)),
        c ij * (f i) ^ ij.1.2 * (ωs i) ^ ij.1.1 = 0 := by
      simpa [Φ, constraintMap] using this
    simpa [hEval] using this

theorem exists_nonzero_interpolant_mul {k D m : ℕ} [NeZero k] (hk : 2 ≤ k) {ωs : Fin n ↪ F}
    (f : Fin n → F) (hcount : n * (multiplicityPairs m).card < monomialCount (k := k) D) :
    ∃ Q : Polynomial (Polynomial F), GSCondition k m D ωs f Q := by
  classical
  -- Work in coefficient space indexed by admissible monomials.
  let S : Finset (ℕ × ℕ) := monomials (k := k) D
  let T : Finset (ℕ × ℕ) := multiplicityPairs m
  let Φ : (S → F) →ₗ[F] (Fin n × T → F) := constraintMapMul (F := F) (n := n) (k := k) (D := D)
    (m := m) ωs f
  have hfinrank : Module.finrank F (Fin n × T → F) < Module.finrank F (S → F) := by
    have h₁ : Module.finrank F (Fin n × T → F) = n * T.card := by
      simp [Fintype.card_prod, T]
    have h₂ : Module.finrank F (S → F) = S.card := by
      simp
    have : n * T.card < S.card := by simpa [S, T, monomialCount] using hcount
    simpa [h₁, h₂] using this
  have hker : LinearMap.ker Φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) hfinrank
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hker with ⟨c, hcKer, hc0⟩
  refine ⟨polyOfCoeffs (F := F) (k := k) (D := D) c, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Nonzero: pick an index where `c` is nonzero and read off the coefficient.
    have : ∃ ij, c ij ≠ 0 := by
      by_contra h
      push_neg at h
      apply hc0
      funext ij
      simpa using h ij
    exact polyOfCoeffs_ne_zero_of_coeff_ne_zero (F := F) (k := k) (D := D) this
  · -- Weighted-degree bound.
    simpa using natWeightedDegree_polyOfCoeffs_le (F := F) (k := k) (D := D) hk c
  · intro i a b hab
    -- Extract the constraint indexed by `(i,(a,b))`.
    have hab_mem : (a, b) ∈ T := by
      change (a, b) ∈ multiplicityPairs m
      exact mem_multiplicityPairs_of_add_lt (m := m) hab
    let ab : T := ⟨(a, b), hab_mem⟩
    have hΦ0 : Φ c = 0 := by simpa [LinearMap.mem_ker] using hcKer
    have : (Φ c) (i, ab) = 0 := by simp [hΦ0]
    -- Unfold `Φ` and identify the constraint with the shifted coefficient.
    simp [Φ, constraintMapMul, bCoeffLinear, polyOfCoeffsLinear] at this
    exact this

end Sudan

section Decoder

variable [Fintype F]

/-- Enumerate all message polynomials of degree `< k` (via coefficient vectors). -/
noncomputable def messagePolynomials (k : ℕ) : Finset F[X] :=
  (Finset.univ : Finset (Fin k → F)).image polynomialOfCoeffs

/-- A specification-level list decoder for Reed–Solomon messages: enumerate all polynomials of
degree `< k` (via coefficient vectors of length `k`) and filter by Hamming distance. -/
noncomputable def decoder (k _r _D e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) : List F[X] :=
  ((messagePolynomials (F := F) k).filter fun p => Δ₀(f, p.eval ∘ ωs) ≤ e).toList

/-- Each decoded codeword has to be e-far from the received message. -/
theorem decoder_mem_impl_dist
  {k r D e : ℕ}
  (_h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_in : p ∈ decoder k r D e ωs f)
  :
  Δ₀(f, p.eval ∘ ωs) ≤ e := by
  have hp_mem :
      p ∈ (messagePolynomials (F := F) k).filter fun p => Δ₀(f, p.eval ∘ ωs) ≤ e := by
    simpa [decoder] using (Finset.mem_toList.1 h_in)
  exact (Finset.mem_filter.1 hp_mem).2

/-- If a codeword is e-far from the received message it appears in the output of
the decoder.
-/
theorem decoder_dist_impl_mem
  {k r D e : ℕ}
  (_h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_deg : p.natDegree < k)
  (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e) :
  p ∈ decoder k r D e ωs f := by
  classical
  -- Show `p` appears in the enumeration via its coefficient vector.
  have hp_repr : polynomialOfCoeffs (Fin.liftF' (n := k) p.coeff) = p := by
    ext i
    by_cases hi : i < k
    · have h := Fin.liftF_liftF'_of_lt (f := p.coeff) (m := i) (n := k) hi
      simp [coeff_polynomialOfCoeffs_eq_coeffs''] at *
      exact h
    · have hpi : p.coeff i = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        exact lt_of_lt_of_le h_deg (Nat.le_of_not_gt hi)
      have hcoeff0 :
          (polynomialOfCoeffs (Fin.liftF' (n := k) p.coeff)).coeff i = 0 := by
        simp [coeff_polynomialOfCoeffs_eq_coeffs'', Fin.liftF, hi]
      simpa [hpi] using hcoeff0
  -- Now `p` is in the (multi)set of candidates and passes the distance filter.
  have hp_mem_candidates : p ∈ messagePolynomials (F := F) k := by
    refine Finset.mem_image.2 ?_
    refine ⟨Fin.liftF' (n := k) p.coeff, Finset.mem_univ _, hp_repr⟩
  have hp_mem_decoded :
      p ∈ (messagePolynomials (F := F) k).filter fun p => Δ₀(f, p.eval ∘ ωs) ≤ e := by
    exact Finset.mem_filter.2 ⟨hp_mem_candidates, h_dist⟩
  -- Convert to `List` membership.
  simpa [decoder] using (Finset.mem_toList.2 hp_mem_decoded)

lemma natDegree_lt_of_mem_messagePolynomials {k : ℕ} [NeZero k] {p : F[X]}
    (hp : p ∈ messagePolynomials (F := F) k) :
    p.natDegree < k := by
  rcases Finset.mem_image.1 hp with ⟨msg, _, rfl⟩
  exact natDegree_polynomialOfCoeffs_deg_lt_deg (F := F) (deg := k) (coeffs := msg)

lemma eval_mem_reedSolomon_code_of_mem_messagePolynomials {k : ℕ} [NeZero k] {ωs : Fin n ↪ F}
    {p : F[X]} (hp : p ∈ messagePolynomials (F := F) k) :
    p.eval ∘ ωs ∈ ReedSolomon.code ωs k := by
  rcases Finset.mem_image.1 hp with ⟨msg, _, rfl⟩
  simpa [ReedSolomonCode.encode] using
    (ReedSolomonCode.encode_mem_ReedSolomon_code (F := F) (deg := k) (domain := ωs) (msg := msg))

omit [Fintype F] in
private lemma eval_injective_of_natDegree_lt {k : ℕ} [NeZero k] (hk : k ≤ n) {ωs : Fin n ↪ F}
    {p q : F[X]} (hp : p.natDegree < k) (hq : q.natDegree < k)
    (h_eval : (p.eval ∘ ωs) = (q.eval ∘ ωs)) :
    p = q := by
  classical
  have hdeg_sub : (p - q).natDegree < k := by
    have hq_le : q.natDegree ≤ k - 1 := Nat.le_pred_of_lt hq
    have hp_le : p.natDegree ≤ k - 1 := Nat.le_pred_of_lt hp
    have hle : (p - q).natDegree ≤ k - 1 :=
      (Polynomial.natDegree_sub_le_iff_left (p := p) (q := q) (n := k - 1) hq_le).2 hp_le
    exact lt_of_le_of_lt hle (Nat.pred_lt (NeZero.ne k))
  -- The difference polynomial vanishes on all `ωs i`.
  have hvanish : ∀ i : Fin n, (p - q).eval (ωs i) = 0 := by
    intro i
    have hpi : p.eval (ωs i) = q.eval (ωs i) := by
      simpa using congrArg (fun g => g i) h_eval
    simp [hpi]
  -- If `p - q ≠ 0`, it would have at least `n` distinct roots, contradicting the degree bound.
  by_contra hne
  set r : F[X] := p - q
  have hrne : r ≠ 0 := by
    intro hr0
    apply hne
    have : p - q = 0 := by simpa [r] using hr0
    exact sub_eq_zero.mp this
  have hsubset : (Finset.univ.image ωs) ⊆ r.roots.toFinset := by
    intro x hx
    rcases Finset.mem_image.1 hx with ⟨i, _, rfl⟩
    have hroot : r.IsRoot (ωs i) := by
      have : r.eval (ωs i) = 0 := by simpa [r] using hvanish i
      exact this
    have : ωs i ∈ r.roots := (Polynomial.mem_roots hrne).2 hroot
    simpa [Multiset.mem_toFinset] using this
  have hcard_image : (Finset.univ.image ωs).card = n := by
    simpa using
      (Finset.card_image_of_injective (s := (Finset.univ : Finset (Fin n))) ωs.injective)
  have hn_le : n ≤ r.roots.toFinset.card := by
    have := Finset.card_le_card hsubset
    simpa [hcard_image] using this
  have hn_le_natDegree : n ≤ r.natDegree := by
    have hroots_le : r.roots.toFinset.card ≤ r.roots.card := Multiset.toFinset_card_le r.roots
    exact le_trans hn_le (le_trans hroots_le (Polynomial.card_roots' r))
  have hnat_lt_n : r.natDegree < n := lt_of_lt_of_le (by simpa [r] using hdeg_sub) hk
  exact (not_lt_of_ge hn_le_natDegree) hnat_lt_n

theorem decoder_length_le_reedSolomon_ball {k r D e : ℕ} [NeZero k] (hk : k ≤ n) {ωs : Fin n ↪ F}
    (f : Fin n → F) :
    (decoder (F := F) (n := n) k r D e ωs f).length ≤
      ((ReedSolomonCode.finCarrier (ι := Fin n) (F := F) ωs k) ∩
          ({x | Δ₀(x, f) ≤ e} : Finset (Fin n → F))).card := by
  classical
  set decoded :
      Finset F[X] :=
    (messagePolynomials (F := F) k).filter fun p => Δ₀(f, p.eval ∘ ωs) ≤ e
  have hlen : (decoder (F := F) (n := n) k r D e ωs f).length = decoded.card := by
    simp [decoder, decoded]
  let B : Finset (Fin n → F) := ReedSolomonCode.finCarrier (ι := Fin n) (F := F) ωs k
  let ball : Finset (Fin n → F) := B ∩ ({x | Δ₀(x, f) ≤ e} : Finset (Fin n → F))
  have hcard : decoded.card ≤ ball.card := by
    -- Build an injective map from decoded polynomials to close Reed–Solomon codewords.
    let g : decoded → ball := fun p =>
      ⟨p.1.eval ∘ ωs, by
        have hp_mem : p.1 ∈ decoded := p.2
        have hp' : p.1 ∈ messagePolynomials (F := F) k ∧ Δ₀(f, p.1.eval ∘ ωs) ≤ e := by
          simpa [decoded] using (Finset.mem_filter.1 hp_mem)
        have hp_code : p.1.eval ∘ ωs ∈ ReedSolomon.code ωs k :=
          eval_mem_reedSolomon_code_of_mem_messagePolynomials (F := F) (n := n) hp'.1
        have hdist : Δ₀(p.1.eval ∘ ωs, f) ≤ e := by
          simpa [hammingDist, ne_comm] using hp'.2
        -- Membership in the finite carrier.
        have hpB : p.1.eval ∘ ωs ∈ B := by
          simpa [B, ReedSolomonCode.finCarrier] using hp_code
        -- Conclude membership in `ball`.
        simp [ball, hpB, hdist]⟩
    have hg_inj : Function.Injective g := by
      intro p q hpq
      have hvals : p.1.eval ∘ ωs = q.1.eval ∘ ωs := by
        simpa [g] using congrArg Subtype.val hpq
      have hp_deg : p.1.natDegree < k := by
        have hp_mem : p.1 ∈ decoded := p.2
        have hp' : p.1 ∈ messagePolynomials (F := F) k ∧ Δ₀(f, p.1.eval ∘ ωs) ≤ e := by
          simpa [decoded] using (Finset.mem_filter.1 hp_mem)
        exact natDegree_lt_of_mem_messagePolynomials (F := F) (k := k) hp'.1
      have hq_deg : q.1.natDegree < k := by
        have hq_mem : q.1 ∈ decoded := q.2
        have hq' : q.1 ∈ messagePolynomials (F := F) k ∧ Δ₀(f, q.1.eval ∘ ωs) ≤ e := by
          simpa [decoded] using (Finset.mem_filter.1 hq_mem)
        exact natDegree_lt_of_mem_messagePolynomials (F := F) (k := k) hq'.1
      have : p.1 = q.1 := eval_injective_of_natDegree_lt (F := F) (n := n) (k := k) hk
        (ωs := ωs) hp_deg hq_deg hvals
      exact Subtype.ext this
    -- Convert injectivity into a cardinality bound.
    simpa [Fintype.card_coe] using (Fintype.card_le_of_injective g hg_inj)
  -- Rewrite the goal in terms of `decoded.card`.
  simpa [hlen, B, ball] using hcard

private lemma nat_cast_sub_eq_cast_pred {k : ℕ} [NeZero k] (hk : k ≤ n) :
    (n : ℝ) - ((n - k + 1 : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) := by
  have hk_pos : 0 < k := NeZero.pos k
  have h_le : n - k + 1 ≤ n := by omega
  have hcastnat : n - (n - k + 1) = k - 1 := by omega
  have hsub' : (n : ℝ) - ((n - k + 1 : ℕ) : ℝ) = ((n - (n - k + 1)) : ℕ) := by
    simpa using (Nat.cast_sub h_le).symm
  have hcast_real : ((n - (n - k + 1) : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast hcastnat
  calc
    (n : ℝ) - ((n - k + 1 : ℕ) : ℝ) = ((n - (n - k + 1)) : ℕ) := hsub'
    _ = ((k - 1 : ℕ) : ℝ) := hcast_real

theorem decoder_length_le_johnson_bound {k r D e : ℕ} [NeZero k] (hk : k ≤ n) [NeZero n]
    {ωs : Fin n ↪ F} (f : Fin n → F)
    (h_e : (e : ℝ) ≤ (n : ℝ) - Real.sqrt ((n : ℝ) * ((k - 1 : ℕ) : ℝ))) :
    (decoder (F := F) (n := n) k r D e ωs f).length ≤
      Fintype.card F * (n - k + 1) * n := by
  classical
  have h_le_ball : (decoder (F := F) (n := n) k r D e ωs f).length ≤
      ((ReedSolomonCode.finCarrier (ι := Fin n) (F := F) ωs k) ∩
          ({x | Δ₀(x, f) ≤ e} : Finset (Fin n → F))).card :=
    decoder_length_le_reedSolomon_ball (F := F) (n := n) (k := k) (r := r) (D := D)
      (e := e) hk (ωs := ωs) f
  -- Apply the Johnson bound to the Reed–Solomon codeword set.
  let B : Finset (Fin n → F) := ReedSolomonCode.finCarrier (ι := Fin n) (F := F) ωs k
  have hB : 1 < B.card := by
    -- `0` and the constant `1` codeword are distinct members.
    refine (Finset.one_lt_card).2 ?_
    refine ⟨0, ?_, ReedSolomonCode.constantCode (x := (1 : F)) (ι' := Fin n), ?_, ?_⟩
    · simp [B, ReedSolomonCode.finCarrier]
    · simp [B, ReedSolomonCode.finCarrier]
    · -- Distinctness uses `Nonempty (Fin n)` from `[NeZero n]`.
      have hne : ReedSolomonCode.constantCode (x := (1 : F)) (ι' := Fin n) ≠ (0 : Fin n → F) := by
        intro h0
        have : (1 : F) = 0 := (ReedSolomonCode.constantCode_eq_ofNat_zero_iff (ι := Fin n)
          (F := F) (x := (1 : F))).1 h0
        exact one_ne_zero this
      simpa using hne.symm
  have hminDist : Code.minDist (↑(ReedSolomon.code ωs k) : Set (Fin n → F)) = n - k + 1 := by
    simpa using
      (ReedSolomonCode.minDist' (ι := Fin n) (F := F) (α := ωs) (n := k)
        (h := by simpa [Fintype.card_fin] using hk))
  have hdB : sInf {d : ℕ | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ Δ₀(u, v) = d} = n - k + 1 := by
    simpa [Code.minDist, B, ReedSolomonCode.finCarrier] using hminDist
  have he_d :
      (e : ℝ) ≤
        (n : ℝ) -
          Real.sqrt
            ((n : ℝ) *
              ((n : ℝ) - ((sInf {d : ℕ | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ Δ₀(u, v) = d} : ℕ) : ℝ))) := by
    -- Substitute `d = n - k + 1` and rewrite the square-root term to match `h_e`.
    -- (Avoid `simp` so we don't expand `sqrt` of a product.)
    rw [hdB]
    have hsqrt :
        Real.sqrt ((n : ℝ) * ((n : ℝ) - ((n - k + 1 : ℕ) : ℝ))) =
          Real.sqrt ((n : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
      rw [nat_cast_sub_eq_cast_pred (n := n) (k := k) hk]
    rw [hsqrt]
    exact h_e
  have hball_q :
      ((B ∩ ({x | Δ₀(x, f) ≤ e} : Finset (Fin n → F))).card : ℚ) ≤
        (Fintype.card F : ℚ) * (n - k + 1) * n := by
    have hJB := JohnsonBound.johnson_bound_alphabet_free (B := B) (v := f) (e := e) hB
    -- Substitute `d = n - k + 1` into the Johnson bound.
    have hJB' :
        ((B ∩ ({x | Δ₀(x, f) ≤ e} : Finset (Fin n → F))).card : ℚ) ≤
          (Fintype.card F : ℚ) * ((sInf {d : ℕ | ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ Δ₀(u, v) = d} : ℕ) : ℚ) *
            (n : ℚ) := by
      simpa [B] using hJB he_d
    -- Rewrite the `sInf` distance using `hdB`.
    simpa [Nat.cast_sub hk, hdB, mul_assoc, mul_left_comm, mul_comm] using hJB'
  have hball_nat :
      (B ∩ ({x | Δ₀(x, f) ≤ e} : Finset (Fin n → F))).card ≤
        Fintype.card F * (n - k + 1) * n := by
    exact_mod_cast hball_q
  -- Use the previously proved reduction to the ball.
  refine le_trans h_le_ball ?_
  simpa [B] using hball_nat

end Decoder

/-- The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan
    in lemma 5.3 of [BCIKS20].
    D_X(m) = (m + 1/2)√ρn.
-/
noncomputable def proximity_gap_degree_bound (k m : ℕ) : ℕ := by
  classical
  let rho := (k + 1 : ℚ) / n
  let b : ℝ := (((m : ℚ) + (1 : ℚ) / 2) * (Real.sqrt rho)) * n
  exact if h : ∃ t : ℕ, b = t then h.choose - 1 else Nat.floor b

/-- The ball radius from lemma 5.3 of [BCIKS20],
    which follows from the Johnson bound.
    δ₀(ρ, m) = 1 - √ρ - √ρ/2m.
-/
noncomputable def proximity_gap_johnson (k m : ℕ) : ℕ :=
  let rho := (k + 1 : ℚ) / n
  Nat.floor (((1 : ℝ) - Real.sqrt rho - Real.sqrt rho / (2 * m)) * (n : ℝ))

private lemma proximity_gap_b_le_degree_bound_add_one (k m : ℕ) :
    let rho := (k + 1 : ℚ) / n
    let b : ℝ := (((m : ℚ) + (1 : ℚ) / 2) * (Real.sqrt rho)) * n
    b ≤ (proximity_gap_degree_bound (n := n) k m + 1 : ℝ) := by
  classical
  intro rho b
  let b' : ℝ :=
    ((m : ℝ) + (1 : ℝ) / 2) * (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (n : ℝ)) * (n : ℝ)
  have hb' : b = b' := by
    have hk : 0 ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (k + 1))
    calc
      b = ((m : ℝ) + (1 : ℝ) / 2) * Real.sqrt (rho : ℝ) * (n : ℝ) := by
        simp [b, rho]
      _ =
          ((m : ℝ) + (1 : ℝ) / 2) *
            (Real.sqrt (((k + 1 : ℕ) : ℝ) / (n : ℝ))) * (n : ℝ) := by
        simp [rho]
      _ =
          ((m : ℝ) + (1 : ℝ) / 2) *
            (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (n : ℝ)) * (n : ℝ) := by
        have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        have hsqrt :
            Real.sqrt (((k + 1 : ℕ) : ℝ) / (n : ℝ)) =
              Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (n : ℝ) := by
          exact
            Real.sqrt_div (x := ((k + 1 : ℕ) : ℝ)) (hx := hk) (y := (n : ℝ))
        rw [hsqrt]
      _ = b' := rfl
  have hD' :
      proximity_gap_degree_bound (n := n) k m =
        (if h0 : ∃ t : ℕ, b' = t then h0.choose - 1 else Nat.floor b') := by
    simp [proximity_gap_degree_bound, b']
  by_cases h : ∃ t : ℕ, b = t
  · have h' : ∃ t : ℕ, b' = t := by
      rcases h with ⟨t, ht⟩
      have ht' := ht
      simp [hb'] at ht'
      exact ⟨t, ht'⟩
    have hb : b = h'.choose := by
      simpa [hb'] using h'.choose_spec
    have hleNat : h'.choose ≤ h'.choose - 1 + 1 := by
      cases h'.choose with
      | zero => simp
      | succ t => simp
    have hle : (h'.choose : ℝ) ≤ (h'.choose - 1 + 1 : ℕ) := by
      exact_mod_cast hleNat
    have hD : proximity_gap_degree_bound (n := n) k m = h'.choose - 1 := by
      simpa [h'] using hD'
    calc
      b = (h'.choose : ℝ) := hb
      _ ≤ (h'.choose - 1 + 1 : ℕ) := hle
      _ = (proximity_gap_degree_bound (n := n) k m + 1 : ℝ) := by
        simp [hD]
  · have h' : ¬ ∃ t : ℕ, b' = t := by
      intro h'
      exact h (by simpa [hb'] using h')
    have hb : b < (Nat.floor b : ℝ) + 1 := by
      simpa using (Nat.lt_floor_add_one (a := b))
    have hD' : proximity_gap_degree_bound (n := n) k m = Nat.floor b' := by
      simpa [h'] using hD'
    have hD : proximity_gap_degree_bound (n := n) k m = Nat.floor b := by
      simpa [hb'] using hD'
    calc
      b ≤ (Nat.floor b : ℝ) + 1 := le_of_lt hb
      _ = (proximity_gap_degree_bound (n := n) k m + 1 : ℝ) := by
        simp [hD]

private lemma proximity_gap_count_bound {k m : ℕ} (hk : 2 ≤ k) :
    n * (multiplicityPairs m).card <
      monomialCount (k := k) (proximity_gap_degree_bound (n := n) k m) := by
  classical
  set D := proximity_gap_degree_bound (n := n) k m with hD
  by_cases hn : n = 0
  · subst hn
    have hkpos : 0 < k - 1 := by omega
    have hkposR : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hkpos
    have hden : (0 : ℝ) < 2 * ((k - 1 : ℕ) : ℝ) := by nlinarith [hkposR]
    have hnum : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_pos D)
    have hpos :
        (0 : ℝ) <
          (((D + 1 : ℕ) : ℝ) ^ 2) / (2 * ((k - 1 : ℕ) : ℝ)) := by
      have : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) ^ 2 := by
        exact pow_pos hnum 2
      exact div_pos this hden
    have hmon :
        (((D + 1 : ℕ) : ℝ) ^ 2) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
          (monomialCount (k := k) D : ℝ) :=
      monomialCount_ge_sq (k := k) (D := D) hk
    have hpos' : (0 : ℝ) < (monomialCount (k := k) D : ℝ) :=
      lt_of_lt_of_le hpos hmon
    have hposNat : 0 < monomialCount (k := k) D := by
      exact_mod_cast hpos'
    simpa [hD] using hposNat
  · have hkpos : 0 < k - 1 := by omega
    have hkposR : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hkpos
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    let rho : ℚ := (k + 1 : ℚ) / n
    let b : ℝ := (((m : ℚ) + (1 : ℚ) / 2) * (Real.sqrt rho)) * n
    have hb_le : b ≤ (D + 1 : ℝ) := by
      simpa [D, rho, b] using
        (proximity_gap_b_le_degree_bound_add_one (n := n) (k := k) (m := m))
    have hb_nonneg : 0 ≤ b := by
      have hm : (0 : ℝ) ≤ (m : ℝ) + (1 : ℝ) / 2 := by nlinarith
      have hsqrt : 0 ≤ Real.sqrt (rho : ℝ) := by
        exact Real.sqrt_nonneg _
      have hn' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have hmul : 0 ≤ ((m : ℝ) + (1 : ℝ) / 2) * Real.sqrt (rho : ℝ) :=
        mul_nonneg hm hsqrt
      have hmul' : 0 ≤ ((m : ℝ) + (1 : ℝ) / 2) * Real.sqrt (rho : ℝ) * (n : ℝ) :=
        mul_nonneg hmul hn'
      simpa [b, rho, mul_assoc] using hmul'
    have hb_sq :
        b ^ 2 =
          ((m : ℝ) + (1 : ℝ) / 2) ^ 2 * (rho : ℝ) * (n : ℝ) ^ 2 := by
      have hrho : 0 ≤ (rho : ℝ) := by
        have hk' : (0 : ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast (Nat.zero_le (k + 1))
        have hn' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        have : 0 ≤ ((k + 1 : ℝ) / (n : ℝ)) := div_nonneg hk' hn'
        simpa [rho] using this
      have : b =
          ((m : ℝ) + (1 : ℝ) / 2) * Real.sqrt (rho : ℝ) * (n : ℝ) := by
        simp [b, rho]
      calc
        b ^ 2 =
            (((m : ℝ) + (1 : ℝ) / 2) * Real.sqrt (rho : ℝ) * (n : ℝ)) ^ 2 := by
          simp [this]
        _ =
            ((m : ℝ) + (1 : ℝ) / 2) ^ 2 * (Real.sqrt (rho : ℝ)) ^ 2 * (n : ℝ) ^ 2 := by
          ring
        _ =
            ((m : ℝ) + (1 : ℝ) / 2) ^ 2 * (rho : ℝ) * (n : ℝ) ^ 2 := by
          simp [Real.sq_sqrt hrho]
    have hb_sq' :
        b ^ 2 =
          ((m : ℝ) + (1 : ℝ) / 2) ^ 2 * ((k + 1 : ℕ) : ℝ) * (n : ℝ) := by
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hrho_n :
          (rho : ℝ) * (n : ℝ) ^ 2 = ((k + 1 : ℕ) : ℝ) * (n : ℝ) := by
        calc
          (rho : ℝ) * (n : ℝ) ^ 2 = (((k + 1 : ℕ) : ℝ) / (n : ℝ)) * (n : ℝ) ^ 2 := by
            simp [rho]
          _ = ((k + 1 : ℕ) : ℝ) * (n : ℝ) := by
            field_simp [hnR]
            ring
      calc
        b ^ 2 =
            ((m : ℝ) + (1 : ℝ) / 2) ^ 2 * (rho : ℝ) * (n : ℝ) ^ 2 := hb_sq
        _ =
            ((m : ℝ) + (1 : ℝ) / 2) ^ 2 * ((rho : ℝ) * (n : ℝ) ^ 2) := by
          ring
        _ = ((m : ℝ) + (1 : ℝ) / 2) ^ 2 * (((k + 1 : ℕ) : ℝ) * (n : ℝ)) := by
          simp [hrho_n]
        _ = ((m : ℝ) + (1 : ℝ) / 2) ^ 2 * ((k + 1 : ℕ) : ℝ) * (n : ℝ) := by
          ring
    have hbase :
        (m : ℝ) * (m + 1) * ((k - 1 : ℕ) : ℝ) <
          ((m : ℝ) + (1 : ℝ) / 2) ^ 2 * ((k + 1 : ℕ) : ℝ) := by
      exact m_mul_m_add_one_mul_lt m k
    have hdenpos : (0 : ℝ) < 2 * ((k - 1 : ℕ) : ℝ) := by nlinarith [hkposR]
    have hkposR' : ((k - 1 : ℕ) : ℝ) ≠ 0 := by exact ne_of_gt hkposR
    have hbase_div :
        (m : ℝ) * (m + 1) / 2 <
          ((m : ℝ) + (1 : ℝ) / 2) ^ 2 * ((k + 1 : ℕ) : ℝ) /
            (2 * ((k - 1 : ℕ) : ℝ)) := by
      have h := div_lt_div_of_pos_right hbase hdenpos
      have hL :
          (m : ℝ) * (m + 1) * ((k - 1 : ℕ) : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) =
            (m : ℝ) * (m + 1) / 2 := by
        calc
          (m : ℝ) * (m + 1) * ((k - 1 : ℕ) : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) =
              ((k - 1 : ℕ) : ℝ) * ((m : ℝ) * (m + 1)) / (((k - 1 : ℕ) : ℝ) * 2) := by
            simp [mul_comm, mul_left_comm]
          _ = (m : ℝ) * (m + 1) / 2 := by
            simp [mul_div_mul_left, hkposR']
      -- Rewrite the left-hand side using `hL`.
      rw [hL] at h
      exact h
    have hbase_mul :
        (n : ℝ) * ((m : ℝ) * (m + 1) / 2) <
          (n : ℝ) *
            (((m : ℝ) + (1 : ℝ) / 2) ^ 2 * ((k + 1 : ℕ) : ℝ) /
              (2 * ((k - 1 : ℕ) : ℝ))) := by
      exact mul_lt_mul_of_pos_left hbase_div hnposR
    have hineq :
        (n : ℝ) * ((m : ℝ) * (m + 1) / 2) <
          ((m : ℝ) + (1 : ℝ) / 2) ^ 2 * ((k + 1 : ℕ) : ℝ) * (n : ℝ) /
            (2 * ((k - 1 : ℕ) : ℝ)) := by
      -- Fold the quotient into the numerator using `div_eq_mul_inv`.
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbase_mul
    have hineq' :
        (n : ℝ) * ((m : ℝ) * (m + 1) / 2) < b ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) := by
      simpa [hb_sq', mul_assoc, mul_left_comm, mul_comm] using hineq
    have hcard :
        (n * (multiplicityPairs m).card : ℝ) =
          (n : ℝ) * ((m : ℝ) * (m + 1) / 2) := by
      simp [card_multiplicityPairs_cast]
    have hineq0 :
        (n * (multiplicityPairs m).card : ℝ) <
          b ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) := by
      simpa [hcard] using hineq'
    have hsq : b ^ 2 ≤ ((D + 1 : ℕ) : ℝ) ^ 2 := by
      simpa [pow_two] using (mul_self_le_mul_self hb_nonneg hb_le)
    have hdiv :
        b ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) ≤
          ((D + 1 : ℕ) : ℝ) ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) := by
      have hden : (0 : ℝ) ≤ 2 * ((k - 1 : ℕ) : ℝ) := by nlinarith [hkposR]
      exact div_le_div_of_nonneg_right hsq hden
    have hmon :
        ((D + 1 : ℕ) : ℝ) ^ 2 / (2 * ((k - 1 : ℕ) : ℝ)) ≤
          (monomialCount (k := k) D : ℝ) :=
      monomialCount_ge_sq (k := k) (D := D) hk
    have hfinal :
        (n * (multiplicityPairs m).card : ℝ) <
          (monomialCount (k := k) D : ℝ) := by
      exact lt_of_lt_of_le (lt_of_lt_of_le hineq0 hdiv) hmon
    have hfinalNat :
        n * (multiplicityPairs m).card <
          monomialCount (k := k) D := by
      exact_mod_cast hfinal
    simpa [hD] using hfinalNat

private lemma proximity_gap_degree_bound_lt_mul {k m : ℕ} [NeZero n] [NeZero m]
    (hδ :
      (0 : ℝ) ≤
        (1 : ℝ) - Real.sqrt ((k + 1 : ℚ) / n) - Real.sqrt ((k + 1 : ℚ) / n) / (2 * m)) :
    proximity_gap_degree_bound (n := n) k m <
      m * (n - proximity_gap_johnson (n := n) k m) := by
  classical
  let rho : ℚ := (k + 1 : ℚ) / n
  let b : ℝ := (((m : ℚ) + (1 : ℚ) / 2) * (Real.sqrt rho)) * n
  let a : ℝ := Real.sqrt (rho : ℝ) + Real.sqrt (rho : ℝ) / (2 * (m : ℝ))
  let E : ℝ := ((1 : ℝ) - Real.sqrt (rho : ℝ) - Real.sqrt (rho : ℝ) / (2 * (m : ℝ))) * (n : ℝ)
  set D := proximity_gap_degree_bound (n := n) k m with hD
  set e := proximity_gap_johnson (n := n) k m with he
  have hδ' :
      (0 : ℝ) ≤ (1 : ℝ) - Real.sqrt (rho : ℝ) - Real.sqrt (rho : ℝ) / (2 * (m : ℝ)) := by
    simpa [rho] using hδ
  have hE_nonneg : 0 ≤ E := by
    have hn' : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have : 0 ≤
        ((1 : ℝ) - Real.sqrt (rho : ℝ) - Real.sqrt (rho : ℝ) / (2 * (m : ℝ))) * (n : ℝ) :=
      mul_nonneg hδ' hn'
    simpa [E] using this
  have he_le : (e : ℝ) ≤ E := by
    have hfloor : ((Nat.floor E : ℝ)) ≤ E := Nat.floor_le hE_nonneg
    simpa [he, proximity_gap_johnson, rho, E] using hfloor
  have hcoef_le :
      (1 : ℝ) - Real.sqrt (rho : ℝ) - Real.sqrt (rho : ℝ) / (2 * (m : ℝ)) ≤ 1 := by
    have hsqrt : 0 ≤ Real.sqrt (rho : ℝ) := by exact Real.sqrt_nonneg _
    have hden : 0 ≤ (2 * (m : ℝ)) := by
      have hm : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
      nlinarith
    have hdiv : 0 ≤ Real.sqrt (rho : ℝ) / (2 * (m : ℝ)) := by
      exact div_nonneg hsqrt hden
    have hnonneg : 0 ≤ Real.sqrt (rho : ℝ) + Real.sqrt (rho : ℝ) / (2 * (m : ℝ)) := by
      nlinarith [hsqrt, hdiv]
    have : (1 : ℝ) - (Real.sqrt (rho : ℝ) + Real.sqrt (rho : ℝ) / (2 * (m : ℝ))) ≤ 1 :=
      sub_le_self _ hnonneg
    nlinarith
  have hE_le : E ≤ (n : ℝ) := by
    have hn' : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have :
        ((1 : ℝ) - Real.sqrt (rho : ℝ) - Real.sqrt (rho : ℝ) / (2 * (m : ℝ))) * (n : ℝ) ≤
          (1 : ℝ) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef_le hn'
    simpa [E] using this
  have he_le_nat : e ≤ n := by
    have : (Nat.floor E) ≤ n := Nat.floor_le_of_le hE_le
    simpa [he, proximity_gap_johnson, rho, E] using this
  have hsub_cast : ((n - e : ℕ) : ℝ) = (n : ℝ) - (e : ℝ) := by
    simpa using (Nat.cast_sub (R := ℝ) (m := e) (n := n) he_le_nat)
  have hsub_le : (n : ℝ) - E ≤ ((n - e : ℕ) : ℝ) := by
    have : (n : ℝ) - E ≤ (n : ℝ) - (e : ℝ) := by linarith [he_le]
    simpa [hsub_cast] using this
  have hmnonneg : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
  have hmul_le :
      (m : ℝ) * ((n : ℝ) - E) ≤ (m : ℝ) * ((n - e : ℕ) : ℝ) := by
    exact mul_le_mul_of_nonneg_left hsub_le hmnonneg
  have hsubE : (n : ℝ) - E = a * (n : ℝ) := by
    have :
        (n : ℝ) -
            ((1 : ℝ) - Real.sqrt (rho : ℝ) - Real.sqrt (rho : ℝ) / (2 * (m : ℝ))) *
              (n : ℝ) =
          (Real.sqrt (rho : ℝ) + Real.sqrt (rho : ℝ) / (2 * (m : ℝ))) * (n : ℝ) := by
      ring
    simpa [E, a] using this
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have h2mne : (2 * (m : ℝ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hmne
  have hmul_a :
      (m : ℝ) * (Real.sqrt (rho : ℝ) + Real.sqrt (rho : ℝ) / (2 * (m : ℝ))) =
        ((m : ℝ) + (1 : ℝ) / 2) * Real.sqrt (rho : ℝ) := by
    field_simp [hmne, h2mne]
    ring
  have hb_eq : b = (m : ℝ) * ((n : ℝ) - E) := by
    have hb' :
        b = ((m : ℝ) + (1 : ℝ) / 2) * Real.sqrt (rho : ℝ) * (n : ℝ) := by
      simp [b, rho]
    have hsubE' : a * (n : ℝ) = (n : ℝ) - E := hsubE.symm
    calc
      b = ((m : ℝ) + (1 : ℝ) / 2) * Real.sqrt (rho : ℝ) * (n : ℝ) := hb'
      _ =
          (((m : ℝ) + (1 : ℝ) / 2) * Real.sqrt (rho : ℝ)) * (n : ℝ) := by
        simp [mul_assoc]
      _ =
          ((m : ℝ) * (Real.sqrt (rho : ℝ) + Real.sqrt (rho : ℝ) / (2 * (m : ℝ)))) *
            (n : ℝ) := by
        rw [hmul_a.symm]
      _ = (m : ℝ) * a * (n : ℝ) := by
        simp [a, mul_assoc]
      _ = (m : ℝ) * ((n : ℝ) - E) := by
        simp [hsubE', mul_assoc]
  have hb_le :
      b ≤ (m : ℝ) * ((n - e : ℕ) : ℝ) := by
    simpa [hb_eq] using hmul_le
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (NeZero.pos n)
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos k)
  have hrho_pos : 0 < (rho : ℝ) := by
    have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) / (n : ℝ) := div_pos hkpos hnpos
    simpa [rho] using this
  have hsqrt_pos : 0 < Real.sqrt (rho : ℝ) := by
    exact Real.sqrt_pos.2 hrho_pos
  have hmpos : 0 < (m : ℝ) + (1 : ℝ) / 2 := by nlinarith
  have hb_pos : 0 < b := by
    have : 0 < ((m : ℝ) + (1 : ℝ) / 2) * Real.sqrt (rho : ℝ) * (n : ℝ) := by
      have hmul : 0 < ((m : ℝ) + (1 : ℝ) / 2) * Real.sqrt (rho : ℝ) := by
        exact mul_pos hmpos hsqrt_pos
      exact mul_pos hmul hnpos
    simpa [b, rho] using this
  let b' : ℝ :=
    ((m : ℝ) + (1 : ℝ) / 2) * (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (n : ℝ)) * (n : ℝ)
  have hb' : b = b' := by
    have hk : 0 ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (k + 1))
    calc
      b = ((m : ℝ) + (1 : ℝ) / 2) * Real.sqrt (rho : ℝ) * (n : ℝ) := by
        simp [b, rho]
      _ =
          ((m : ℝ) + (1 : ℝ) / 2) *
            (Real.sqrt (((k + 1 : ℕ) : ℝ) / (n : ℝ))) * (n : ℝ) := by
        simp [rho]
      _ =
          ((m : ℝ) + (1 : ℝ) / 2) *
            (Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (n : ℝ)) * (n : ℝ) := by
        have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        have hsqrt :
            Real.sqrt (((k + 1 : ℕ) : ℝ) / (n : ℝ)) =
              Real.sqrt ((k + 1 : ℕ) : ℝ) / Real.sqrt (n : ℝ) := by
          exact
            Real.sqrt_div (x := ((k + 1 : ℕ) : ℝ)) (hx := hk) (y := (n : ℝ))
        rw [hsqrt]
      _ = b' := rfl
  have hD_b' :
      D =
        (if h0 : ∃ t : ℕ, b' = t then h0.choose - 1 else Nat.floor b') := by
    simp [hD, proximity_gap_degree_bound, b']
  have hD_lt_b : (D : ℝ) < b := by
    by_cases h : ∃ t : ℕ, b = t
    · have h' : ∃ t : ℕ, b' = t := by
        simpa [hb'] using h
      have hb'': b = h'.choose := by
        simpa [hb'] using h'.choose_spec
      have hchoose_pos : 0 < (h'.choose : ℝ) := by
        simpa [hb''] using hb_pos
      have hchoose_pos_nat : 0 < h'.choose := by exact_mod_cast hchoose_pos
      have hchoose_le : 1 ≤ h'.choose := Nat.succ_le_of_lt hchoose_pos_nat
      have hcast : ((h'.choose - 1 : ℕ) : ℝ) = (h'.choose : ℝ) - 1 := by
        simpa using (Nat.cast_sub (R := ℝ) (m := 1) (n := h'.choose) hchoose_le)
      have hlt : (h'.choose : ℝ) - 1 < (h'.choose : ℝ) := by linarith
      have hD' : D = h'.choose - 1 := by
        simpa [h'] using hD_b'
      calc
        (D : ℝ) = ((h'.choose - 1 : ℕ) : ℝ) := by exact_mod_cast hD'
        _ = (h'.choose : ℝ) - 1 := hcast
        _ < (h'.choose : ℝ) := hlt
        _ = b := hb''.symm
    · have h' : ¬ ∃ t : ℕ, b' = t := by
        intro h'
        exact h (by simpa [hb'] using h')
      have hb_nonneg : 0 ≤ b := le_of_lt hb_pos
      have hfloor_le : (Nat.floor b : ℝ) ≤ b := Nat.floor_le hb_nonneg
      have hneq : (Nat.floor b : ℝ) ≠ b := by
        intro hEq
        exact h ⟨Nat.floor b, hEq.symm⟩
      have hlt : (Nat.floor b : ℝ) < b := lt_of_le_of_ne hfloor_le hneq
      have hD' : D = Nat.floor b' := by
        simpa [h'] using hD_b'
      have hD'' : D = Nat.floor b := by
        simpa [hb'] using hD'
      calc
        (D : ℝ) = (Nat.floor b : ℝ) := by exact_mod_cast hD''
        _ < b := hlt
  have hlt :
      (D : ℝ) < (m * (n - e) : ℕ) := by
    exact lt_of_lt_of_le hD_lt_b (by simpa [Nat.cast_mul] using hb_le)
  exact_mod_cast hlt

/-- The first part of lemma 5.3 from [BCIKS20].
    Given the D_X (`proximity_gap_degree_bound`) and δ₀ (`proximity_gap_johnson`),
    a solution to Guruswami-Sudan system exists.
-/
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ}
    {ωs : Fin n ↪ F} (f : Fin n → F) :
  ∃ Q,
    GSCondition k m (proximity_gap_degree_bound (n := n) k m) ωs f Q := by
  classical
  -- Handle the small-`k` cases (`k ≤ 1`) directly using a `Y`-only interpolant.
  have small_case :
      ∀ {k : ℕ}, k ≤ 1 →
        ∃ Q, GSCondition k m (proximity_gap_degree_bound (n := n) k m) ωs f Q := by
    intro k hk
    let base : Fin n → F[X][Y] := fun i =>
      (Polynomial.X - Polynomial.C (Polynomial.C (f i)) : F[X][Y])
    let Q : F[X][Y] :=
      Finset.prod (Finset.univ : Finset (Fin n)) (fun i => (base i) ^ m)
    refine ⟨Q, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · -- `Q ≠ 0`.
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro i hi
      have hne : (base i : F[X][Y]) ≠ 0 := by
        simpa [base] using (Polynomial.X_sub_C_ne_zero (Polynomial.C (f i)))
      exact pow_ne_zero _ hne
    · -- Weighted degree bound: `wdeg_{1,0}(Q) = 0`.
      have hdegX_base0 (i : Fin n) :
          Polynomial.Bivariate.degreeX (base i) = 0 := by
        classical
        unfold Polynomial.Bivariate.degreeX base
        refine
          (Finset.sup_eq_bot_iff
              (f := fun n =>
                ((Polynomial.X - Polynomial.C (Polynomial.C (f i)) : F[X][Y]).coeff n).natDegree)
              (S := (Polynomial.X - Polynomial.C (Polynomial.C (f i)) : F[X][Y]).support)).2 ?_
        intro n hn
        by_cases h1 : n = 1
        · subst h1
          simp [Polynomial.coeff_X]
        · by_cases h0 : n = 0
          · subst h0
            simp [Polynomial.coeff_X]
          · have h1' : (1 : ℕ) ≠ n := by simpa [eq_comm] using h1
            simp [Polynomial.coeff_X, Polynomial.coeff_C, h1', h0]
      have hdegX_one : Polynomial.Bivariate.degreeX (1 : F[X][Y]) = 0 := by
        classical
        have hsupport : (1 : F[X][Y]).support = {0} := by
          simpa [Polynomial.C_1] using
            (Polynomial.support_C (a := (1 : Polynomial F)) (by simp))
        simp [Polynomial.Bivariate.degreeX, hsupport]
      have hdegX_factor (i : Fin n) :
          Polynomial.Bivariate.degreeX ((base i) ^ m) = 0 := by
        induction m with
        | zero =>
            simpa using hdegX_one
        | succ m ih =>
            have hne : (base i : F[X][Y]) ≠ 0 := by
              simpa [base] using (Polynomial.X_sub_C_ne_zero (Polynomial.C (f i)))
            have hpow_ne : ((base i : F[X][Y]) ^ m) ≠ 0 := pow_ne_zero _ hne
            have hmul :=
              Polynomial.Bivariate.degreeX_mul
                (f := (base i : F[X][Y]) ^ m) (g := (base i : F[X][Y])) hpow_ne hne
            simpa [pow_succ, ih, hdegX_base0 i] using hmul
      have hdegX_Q :
          Polynomial.Bivariate.degreeX
              (Finset.prod (Finset.univ : Finset (Fin n)) (fun i => (base i) ^ m)) = 0 := by
        classical
        refine
          (Finset.induction_on (s := (Finset.univ : Finset (Fin n))) ?_ ?_)
        · simpa using hdegX_one
        · intro a s ha hs
          have hne_prod :
              Finset.prod s (fun x => (base x) ^ m) ≠ 0 := by
            refine Finset.prod_ne_zero_iff.mpr ?_
            intro x hx
            have hne : (base x : F[X][Y]) ≠ 0 := by
              simpa [base] using (Polynomial.X_sub_C_ne_zero (Polynomial.C (f x)))
            exact pow_ne_zero _ hne
          have hne_factor : ((base a : F[X][Y]) ^ m) ≠ 0 := by
            have hne : (base a : F[X][Y]) ≠ 0 := by
              simpa [base] using (Polynomial.X_sub_C_ne_zero (Polynomial.C (f a)))
            exact pow_ne_zero _ hne
          have hmul :=
            Polynomial.Bivariate.degreeX_mul
              (f := Finset.prod s (fun x => (base x) ^ m)) (g := (base a) ^ m)
              hne_prod hne_factor
          -- `Finset.prod_insert` multiplies on the left; commute to match `hmul`.
          simpa [Finset.prod_insert ha, hs, hdegX_factor a, base, mul_comm, mul_left_comm,
            mul_assoc] using hmul
      have hdeg :
          Polynomial.Bivariate.natWeightedDegree Q 1 (k - 1) = 0 := by
        have hk' : k - 1 = 0 := Nat.sub_eq_zero_of_le hk
        have hdeg0 :
            Polynomial.Bivariate.natWeightedDegree Q 1 0 = 0 := by
          have h := hdegX_Q
          simp [Polynomial.Bivariate.degreeX_as_weighted_deg] at h
          exact h
        simp [hk', hdeg0]
      simp [hdeg]
    · -- Multiplicity constraints: `X^m` divides the shifted polynomial.
      intro i a b hab
      have hXpow :
          (Polynomial.X : F[X][Y]) ^ m ∣ shiftAt Q (ωs i) (f i) := by
        -- Expand `shiftAt` over the product.
        have hprod :
            shiftAt ((base i) ^ m) (ωs i) (f i) ∣
              Finset.prod (Finset.univ : Finset (Fin n))
                (fun j => shiftAt ((base j) ^ m) (ωs i) (f i)) :=
          Finset.dvd_prod_of_mem
            (fun j => shiftAt ((base j) ^ m) (ωs i) (f i)) (by simp)
        have hshift_base :
            shiftAt ((base i) ^ m) (ωs i) (f i) = (Polynomial.X : F[X][Y]) ^ m := by
          -- `shiftAt` maps `X - C fᵢ` to `X`.
          simp [base, shiftAt, shiftAtRingHom, map_pow]
        have hshift_Q :
            shiftAt Q (ωs i) (f i) =
              Finset.prod (Finset.univ : Finset (Fin n))
                (fun j => shiftAt ((base j) ^ m) (ωs i) (f i)) := by
          simp [Q, base, shiftAt, shiftAtRingHom]
        have hdiv :
            (Polynomial.X : F[X][Y]) ^ m ∣
              Finset.prod (Finset.univ : Finset (Fin n))
                (fun j => shiftAt ((base j) ^ m) (ωs i) (f i)) := by
          simpa [hshift_base] using hprod
        simpa [hshift_Q] using hdiv
      have hb : b < m := lt_of_le_of_lt (Nat.le_add_left b a) hab
      have hcoeff :
          (shiftAt Q (ωs i) (f i)).coeff b = 0 := by
        exact (Polynomial.X_pow_dvd_iff.mp hXpow) b hb
      simp [Polynomial.Bivariate.coeff, hcoeff]
  -- Now split on `k`.
  cases k with
  | zero =>
      simpa using (small_case (k := 0) (by decide))
  | succ k' =>
      cases k' with
      | zero =>
          simpa using (small_case (k := 1) (by decide))
      | succ k'' =>
          -- For `k ≥ 2`, reuse the linear-algebra existence proof.
          have hk : 2 ≤ Nat.succ (Nat.succ k'') := by
            exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
          have hk_pos : 0 < Nat.succ (Nat.succ k'') := Nat.succ_pos _
          letI : NeZero (Nat.succ (Nat.succ k'')) := ⟨ne_of_gt hk_pos⟩
          have hcount :
              n * (multiplicityPairs m).card <
                monomialCount (k := Nat.succ (Nat.succ k''))
                  (proximity_gap_degree_bound (n := n) (Nat.succ (Nat.succ k'')) m) :=
            proximity_gap_count_bound (n := n) (k := Nat.succ (Nat.succ k'')) (m := m) hk
          simpa using
            exists_nonzero_interpolant_mul (F := F) (n := n)
              (k := Nat.succ (Nat.succ k''))
              (D := proximity_gap_degree_bound (n := n) (Nat.succ (Nat.succ k'')) m)
              (m := m) hk (ωs := ωs) f hcount

/-- The second part of lemma 5.3 from [BCIKS20].
    For any solution Q of the Guruswami-Sudan system, and for any
    polynomial P ∈ RS[n, k, ρ] such that Δ(w, P) ≤ δ₀(ρ, m),
    we have that Y - P(X) divides Q(X, Y) in the polynomial ring
    F[X][Y].
-/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} [NeZero n] [NeZero m]
    (hδ :
      (0 : ℝ) ≤
        (1 : ℝ) - Real.sqrt ((k + 1 : ℚ) / n) - Real.sqrt ((k + 1 : ℚ) / n) / (2 * m))
    {ωs : Fin n ↪ F} {f : Fin n → F} {Q : F[X][Y]}
    (hQ : GSCondition k m (proximity_gap_degree_bound (n := n) k m) ωs f Q)
    {p : F[X]} (hpdeg : p.natDegree < k)
    (hdist : Δ₀(f, p.eval ∘ ωs) ≤ proximity_gap_johnson (n := n) k m) :
    (Polynomial.X - Polynomial.C p) ∣ Q := by
  classical
  cases k with
  | zero =>
      -- Impossible degree constraint.
      exact (False.elim ((Nat.not_lt_zero _ ) hpdeg))
  | succ k' =>
      -- In the positive-`k` case, reuse the original proof.
      letI : NeZero (Nat.succ k') := ⟨Nat.succ_ne_zero _⟩
      have hD :
          proximity_gap_degree_bound (n := n) (Nat.succ k') m <
            m * (n - proximity_gap_johnson (n := n) (Nat.succ k') m) :=
        proximity_gap_degree_bound_lt_mul (n := n) (k := Nat.succ k') (m := m) hδ
      exact divides_of_close_of_vanish (F := F) (n := n) (k := Nat.succ k') (m := m)
        (D := proximity_gap_degree_bound (n := n) (Nat.succ k') m)
        (ωs := ωs) (f := f) hQ hpdeg hdist hD

section ListSizeBound

open Polynomial

variable {F : Type} [Field F] [DecidableEq F]

lemma natDegreeY_le_natWeightedDegree {k : ℕ} (hk : 2 ≤ k) {Q : F[X][Y]} :
    Polynomial.Bivariate.natDegreeY Q ≤
      Polynomial.Bivariate.natWeightedDegree Q 1 (k - 1) := by
  classical
  by_cases hQ : Q = 0
  · simp [Polynomial.Bivariate.natDegreeY, hQ]
  · -- Use the coefficient characterization of `natDegree`.
    refine (Polynomial.natDegree_le_iff_coeff_eq_zero).2 ?_
    intro N hN
    by_contra hcoeff
    have hmem : N ∈ Q.support := by
      exact Polynomial.mem_support_iff.mpr hcoeff
    have hsup :
        1 * (Q.coeff N).natDegree + (k - 1) * N ≤
          Polynomial.Bivariate.natWeightedDegree Q 1 (k - 1) := by
      exact
        (Finset.le_sup
          (s := Q.support)
          (f := fun m : ℕ => 1 * (Q.coeff m).natDegree + (k - 1) * m)
          hmem)
    have hmul :
        (k - 1) * N ≤ Polynomial.Bivariate.natWeightedDegree Q 1 (k - 1) := by
      exact le_trans (Nat.le_add_left _ _) hsup
    have hk' : 1 ≤ k - 1 := by omega
    have hNle : N ≤ Polynomial.Bivariate.natWeightedDegree Q 1 (k - 1) := by
      have hNmul : N ≤ (k - 1) * N := by
        simpa using (Nat.mul_le_mul_right N hk')
      exact le_trans hNmul hmul
    exact (not_lt_of_ge hNle) hN

/-- If a finite family of distinct linear `Y`-factors divides a bivariate polynomial `Q`,
then the family size is bounded by the `Y`-degree of `Q`. -/
lemma card_linear_factors_le_degreeY {P : Finset F[X]} {Q : F[X][Y]}
    (hQ : Q ≠ 0)
    (hdiv : ∀ p ∈ P, (Polynomial.X - Polynomial.C p) ∣ Q) :
    P.card ≤ Polynomial.Bivariate.natDegreeY Q := by
  classical
  -- Map coefficients to the rational function field, so distinct factors are coprime.
  let φ : F[X] →+* RatFunc F := algebraMap F[X] (RatFunc F)
  let Q' : Polynomial (RatFunc F) := Polynomial.map φ Q
  have hφ_inj : Function.Injective φ := by
    simpa [φ] using (RatFunc.algebraMap_injective (K := F))
  have hQ' : Q' ≠ 0 := by
    intro h
    apply hQ
    exact (Polynomial.map_injective φ hφ_inj) (by simpa [Q'] using h)

  -- Each linear factor still divides after mapping.
  have hdiv' :
      ∀ p ∈ P,
        (Polynomial.X - Polynomial.C (φ p)) ∣ Q' := by
    intro p hp
    have h := hdiv p hp
    have h' := Polynomial.map_dvd φ h
    simp [Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X] at h'
    exact h'

  let s : F[X] → Polynomial (RatFunc F) := fun p => Polynomial.X - Polynomial.C (φ p)

  -- Pairwise coprimality of distinct linear factors in the field `RatFunc F`.
  have hpair : (P : Set F[X]).Pairwise (Function.onFun IsCoprime s) := by
    intro p hp q hq hpq
    have hne : (φ p - φ q) ≠ 0 := by
      have hne' : p ≠ q := by
        intro hEq; exact hpq (by simp [hEq])
      exact sub_ne_zero.mpr (hφ_inj.ne hne')
    have hunit : IsUnit (φ p - φ q) := by
      simpa [isUnit_iff_ne_zero] using hne
    have hcop :=
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (a := φ p) (b := φ q) hunit)
    simp [sub_eq_add_neg] at hcop
    exact hcop

  -- The product of all factors divides `Q'`.
  have hprod_div : Finset.prod P (fun p => s p) ∣ Q' := by
    refine Finset.prod_dvd_of_coprime (t := P) (s := s) hpair ?_
    intro p hp
    simpa [s] using hdiv' p hp

  -- Degree of the product is the number of factors.
  have hdeg_prod : (Finset.prod P (fun p => s p)).natDegree = P.card := by
    classical
    refine Finset.induction_on P ?_ ?_
    · simp [s]
    · intro a t ha ht
      have hmonic : (s a).Monic := by
        simpa [s] using (Polynomial.monic_X_sub_C (φ a))
      have hmonic_prod : (Finset.prod t (fun p => s p)).Monic := by
        refine Finset.induction_on t ?_ ?_
        · simp [s]
        · intro b u hb hu
          have hmonic_b : (s b).Monic := by
            simpa [s] using (Polynomial.monic_X_sub_C (φ b))
          simpa [Finset.prod_insert hb] using hmonic_b.mul hu
      have hdeg_mul :
          (s a * Finset.prod t (fun p => s p)).natDegree =
            (s a).natDegree + (Finset.prod t (fun p => s p)).natDegree := by
        exact (hmonic.natDegree_mul' (by simpa using hmonic_prod.ne_zero))
      have hdeg_linear : (s a).natDegree = 1 := by
        simp [s]
      simp [Finset.prod_insert ha, s, hdeg_mul, hdeg_linear, ht,
        Finset.card_insert_of_notMem ha, Nat.add_comm]

  -- Combine: product degree ≤ degree of `Q'`.
  have hdeg_le : P.card ≤ Q'.natDegree := by
    have hdeg_prod' :
        (Finset.prod P (fun p => s p)).natDegree ≤ Q'.natDegree := by
      exact Polynomial.natDegree_le_of_dvd hprod_div hQ'
    simpa [hdeg_prod] using hdeg_prod'

  -- Map does not change the `Y`-degree.
  have hdeg_map : Q'.natDegree = Q.natDegree := by
    simpa [Q'] using (Polynomial.natDegree_map_eq_of_injective hφ_inj Q)

  -- Convert to `natDegreeY`.
  simpa [Polynomial.Bivariate.natDegreeY, hdeg_map] using hdeg_le

/-- A list-size bound for the Guruswami–Sudan system: the number of degree-`< k` polynomials
close to `f` is bounded by the `Y`-degree of the interpolant. -/
lemma list_size_le_degreeY_of_GSCondition
    [Fintype F] {n k m : ℕ} [NeZero n] [NeZero m] [NeZero k]
    {ωs : Fin n ↪ F} {f : Fin n → F} {Q : F[X][Y]}
    (hδ :
      (0 : ℝ) ≤
        (1 : ℝ) - Real.sqrt ((k + 1 : ℚ) / n) - Real.sqrt ((k + 1 : ℚ) / n) / (2 * m))
    (hQ : GSCondition (n := n) (F := F) k m
      (proximity_gap_degree_bound (n := n) k m) ωs f Q) :
    ((messagePolynomials (F := F) k).filter fun p =>
      Δ₀(f, p.eval ∘ ωs) ≤ proximity_gap_johnson (n := n) k m).card
      ≤ Polynomial.Bivariate.natDegreeY Q := by
  classical
  -- Every close message polynomial yields a linear factor of `Q`.
  have hdiv :
      ∀ p ∈
        ((messagePolynomials (F := F) k).filter fun p =>
          Δ₀(f, p.eval ∘ ωs) ≤ proximity_gap_johnson (n := n) k m),
        (Polynomial.X - Polynomial.C p) ∣ Q := by
    intro p hp
    have hp_mem :
        p ∈ messagePolynomials (F := F) k ∧
          Δ₀(f, p.eval ∘ ωs) ≤ proximity_gap_johnson (n := n) k m := by
      simpa using (Finset.mem_filter.1 hp)
    have hp_deg : p.natDegree < k := by
      exact natDegree_lt_of_mem_messagePolynomials (F := F) (k := k) hp_mem.1
    exact
      guruswami_sudan_for_proximity_gap_property (F := F) (n := n) (k := k) (m := m) hδ
        (ωs := ωs) (f := f) (Q := Q) hQ hp_deg hp_mem.2

  refine card_linear_factors_le_degreeY (F := F) (P := _) (Q := Q) ?_ hdiv
  exact hQ.1

lemma list_size_le_degree_bound_of_GSCondition
    [Fintype F] {n k m : ℕ} [NeZero n] [NeZero m] [NeZero k] (hk : 2 ≤ k)
    {ωs : Fin n ↪ F} {f : Fin n → F} {Q : F[X][Y]}
    (hδ :
      (0 : ℝ) ≤
        (1 : ℝ) - Real.sqrt ((k + 1 : ℚ) / n) - Real.sqrt ((k + 1 : ℚ) / n) / (2 * m))
    (hQ : GSCondition (n := n) (F := F) k m
      (proximity_gap_degree_bound (n := n) k m) ωs f Q) :
    ((messagePolynomials (F := F) k).filter fun p =>
      Δ₀(f, p.eval ∘ ωs) ≤ proximity_gap_johnson (n := n) k m).card
      ≤ proximity_gap_degree_bound (n := n) k m := by
  have hlist :=
    list_size_le_degreeY_of_GSCondition (F := F) (n := n) (k := k) (m := m)
      (ωs := ωs) (f := f) (Q := Q) hδ hQ
  have hdegY :
      Polynomial.Bivariate.natDegreeY Q ≤
        Polynomial.Bivariate.natWeightedDegree Q 1 (k - 1) :=
    natDegreeY_le_natWeightedDegree (F := F) (k := k) hk
  have hdeg_bound : Polynomial.Bivariate.natDegreeY Q ≤
      proximity_gap_degree_bound (n := n) k m := by
    exact le_trans hdegY hQ.Q_deg
  exact le_trans hlist hdeg_bound

end ListSizeBound

section Tests

open Polynomial
open Polynomial.Bivariate

/-- A small regression test: the linear-algebra existence lemma typechecks on a tiny instance. -/
example :
    let ωs : Fin 1 ↪ ℚ := ⟨fun _ => 0, by
      intro i j _
      exact Subsingleton.elim i j⟩
    let f : Fin 1 → ℚ := fun _ => 0
    ∃ Q : Polynomial (Polynomial ℚ), GSCondition (n := 1) (F := ℚ) 2 1 1 ωs f Q := by
  classical
  intro ωs f
  have hcount : 1 * (multiplicityPairs (m := 1)).card < monomialCount (k := 2) 1 := by
    decide
  exact
    (exists_nonzero_interpolant_mul (F := ℚ) (n := 1) (k := 2) (D := 1) (m := 1)
      (by decide : (2 : ℕ) ≤ 2) (ωs := ωs) f hcount)

/-- A small regression test: `divides_of_close_of_vanish` proves a simple divisibility fact. -/
example :
    let _ωs : Fin 2 ↪ ℚ := ⟨fun i => (i.1 : ℚ), by
      intro i j h
      apply Fin.ext
      exact Nat.cast_injective (R := ℚ) (by simpa using h)⟩
    let _f : Fin 2 → ℚ := fun _ => 0
    let Q : ℚ[X][Y] := (Polynomial.X : ℚ[X][Y])
    let p : ℚ[X] := 0
    (Polynomial.X - Polynomial.C p) ∣ Q := by
  classical
  intro ωs f Q p
  have hQ : GSCondition (n := 2) (F := ℚ) 2 1 1 ωs f Q := by
    refine ⟨?_, ?_, ?_⟩
    · simp [Q]
    · simp [Q, Polynomial.Bivariate.natWeightedDegree, Polynomial.support_X]
    · intro i a b hab
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha; subst hb
      simp [Q, f, shiftAt, shiftAtRingHom, Polynomial.Bivariate.coeff]
  have hpdeg : p.natDegree < 2 := by simp [p]
  have hdist : Δ₀(f, p.eval ∘ ωs) ≤ 0 := by
    have : f = p.eval ∘ ωs := by
      funext i
      simp [f, p]
    simp [this]
  have hD : 1 < 1 * (2 - 0) := by decide
  simpa [p] using
    (divides_of_close_of_vanish (F := ℚ) (n := 2) (k := 2) (m := 1) (D := 1)
      (ωs := ωs) (f := f) (Q := Q) hQ hpdeg hdist hD)

/-- A small regression test: the proximity-gap existence lemma closes on a tiny instance. -/
example :
    let ωs : Fin 1 ↪ ℚ := ⟨fun _ => 0, by
      intro i j _
      exact Subsingleton.elim i j⟩
    let f : Fin 1 → ℚ := fun _ => 0
    ∃ Q : Polynomial (Polynomial ℚ),
      GSCondition (n := 1) (F := ℚ) 2 1 (proximity_gap_degree_bound (n := 1) 2 1) ωs f Q := by
  classical
  intro ωs f
  simpa using
    (guruswami_sudan_for_proximity_gap_existence (F := ℚ) (n := 1) (k := 2) (m := 1)
      (ωs := ωs) f)

/-- A small regression test: the proximity-gap count bound holds on a tiny instance. -/
example :
    1 * (multiplicityPairs (m := 1)).card <
      monomialCount (k := 2) (proximity_gap_degree_bound (n := 1) 2 1) := by
  simpa using
    (proximity_gap_count_bound (n := 1) (k := 2) (m := 1) (by decide))

end Tests

end GuruswamiSudan
