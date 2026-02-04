import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import ArkLib.Data.Polynomial.RationalFunctionsInfrastructure

/-!
  # List-recovery scaffolding for proximity-gap proofs

  This file provides a basic interpolation lemma: given values of a word stack at a finite
  set of field points, we can interpolate a polynomial curve passing through all those values.
  This is a foundational step toward list-recovery arguments used in proximity-gap proofs.
-/

namespace ProximityGap

open Polynomial

open scoped BigOperators

lemma exists_polynomial_curve_through_values
    {ι F : Type*} [Field F] [Fintype ι] [DecidableEq ι] [DecidableEq F]
    {S : Finset F} (hS : S.Nonempty)
    (r : {z // z ∈ S} → ι → F) :
    ∃ v : Fin S.card → ι → F,
      ∀ z (hz : z ∈ S),
        (fun x => r ⟨z, hz⟩ x) =
          fun x => ∑ i : Fin S.card, z ^ (i : ℕ) * v i x := by
  classical
  -- Interpolate each coordinate function in the parameter `z`.
  let r_total : ι → F → F := fun x z => if hz : z ∈ S then r ⟨z, hz⟩ x else 0
  have h_inj : Set.InjOn (fun z : F => z) (S : Set F) := by
    intro a ha b hb h
    simpa using h
  let p : ι → F[X] := fun x => Lagrange.interpolate S (fun z => z) (r_total x)
  have hp_eval : ∀ x (z : F) (hz : z ∈ S), (p x).eval z = r ⟨z, hz⟩ x := by
    intro x z hz
    have h :=
      Lagrange.eval_interpolate_at_node (s := S) (v := fun z : F => z)
        (r := r_total x) h_inj hz
    -- unfold `r_total` at the node
    simpa [r_total, hz] using h
  -- Define curve coefficients as polynomial coefficients.
  let v : Fin S.card → ι → F := fun i x => (p x).coeff i
  refine ⟨v, ?_⟩
  intro z hz
  funext x
  -- bound the degree of the interpolant
  have hdeg' : (p x).degree < (S.card : WithBot ℕ) := by
    simpa using
      (Lagrange.degree_interpolate_lt (s := S) (v := fun z : F => z) (r := r_total x) h_inj)
  have hdeg : (p x).natDegree < S.card := by
    by_cases hp0 : p x = 0
    · have hpos : 0 < S.card := Finset.card_pos.mpr hS
      simp [hp0, hpos] -- natDegree 0 = 0 < S.card
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hdeg'
  have hsum :
      (p x).eval z =
        Finset.sum (Finset.range S.card) (fun i => (p x).coeff i * z ^ i) := by
    simpa using (Polynomial.eval_eq_sum_range' (p := p x) (n := S.card) hdeg z)
  have hsum' :
      Finset.sum (Finset.range S.card) (fun i => (p x).coeff i * z ^ i) =
        ∑ i : Fin S.card, z ^ (i : ℕ) * v i x := by
    simpa [v, mul_comm] using
      (Finset.sum_range (n := S.card) (f := fun i : ℕ => (p x).coeff i * z ^ i))
  -- conclude
  have hval := hp_eval x z hz
  simpa [hsum, hsum'] using hval.symm

lemma exists_polynomial_curve_through_values_in_submodule
    {ι F : Type*} [Field F] [Fintype ι] [DecidableEq ι] [DecidableEq F]
    {C : Submodule F (ι → F)}
    {S : Finset F} (hS : S.Nonempty)
    (r : {z // z ∈ S} → ι → F)
    (hr : ∀ z, r z ∈ C) :
    ∃ v : Fin S.card → ι → F,
      (∀ i, v i ∈ C) ∧
      ∀ z (hz : z ∈ S),
        (fun x => r ⟨z, hz⟩ x) =
          fun x => ∑ i : Fin S.card, z ^ (i : ℕ) * v i x := by
  classical
  -- Interpolate each coordinate function in the parameter `z`.
  let r_total : ι → F → F := fun x z => if hz : z ∈ S then r ⟨z, hz⟩ x else 0
  have h_inj : Set.InjOn (fun z : F => z) (S : Set F) := by
    intro a ha b hb h
    simpa using h
  let p : ι → F[X] := fun x => Lagrange.interpolate S (fun z => z) (r_total x)
  have hp_eval : ∀ x (z : F) (hz : z ∈ S), (p x).eval z = r ⟨z, hz⟩ x := by
    intro x z hz
    have h :=
      Lagrange.eval_interpolate_at_node (s := S) (v := fun z : F => z)
        (r := r_total x) h_inj hz
    simpa [r_total, hz] using h
  -- Define curve coefficients as polynomial coefficients.
  let v : Fin S.card → ι → F := fun i x => (p x).coeff i
  have hv_mem : ∀ i, v i ∈ C := by
    intro i
    have hv_formula :
        v i =
          Finset.sum S
            (fun z => (Lagrange.basis S (fun z : F => z) z).coeff i • (fun x => r_total x z)) := by
      funext x
      -- compute the coefficient of the interpolant
      simp [v, p, Lagrange.interpolate_apply, smul_eq_mul, mul_comm]
    -- use submodule closure under finite sums
    refine hv_formula ▸ C.sum_mem ?_
    intro z hz
    have hz' : z ∈ S := hz
    have hrz' : (fun x => r_total x z) ∈ C := by
      have : (fun x => r_total x z) = r ⟨z, hz'⟩ := by
        funext x
        simp [r_total, hz']
      simpa [this] using hr ⟨z, hz'⟩
    exact C.smul_mem _ hrz'
  refine ⟨v, hv_mem, ?_⟩
  -- show the interpolation identity
  intro z hz
  funext x
  have hdeg' : (p x).degree < (S.card : WithBot ℕ) := by
    simpa using
      (Lagrange.degree_interpolate_lt (s := S) (v := fun z : F => z) (r := r_total x) h_inj)
  have hdeg : (p x).natDegree < S.card := by
    by_cases hp0 : p x = 0
    · have hpos : 0 < S.card := Finset.card_pos.mpr hS
      simp [hp0, hpos]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).2 hdeg'
  have hsum :
      (p x).eval z =
        Finset.sum (Finset.range S.card) (fun i => (p x).coeff i * z ^ i) := by
    simpa using (Polynomial.eval_eq_sum_range' (p := p x) (n := S.card) hdeg z)
  have hsum' :
      Finset.sum (Finset.range S.card) (fun i => (p x).coeff i * z ^ i) =
        ∑ i : Fin S.card, z ^ (i : ℕ) * v i x := by
    simpa [v, mul_comm] using
      (Finset.sum_range (n := S.card) (f := fun i : ℕ => (p x).coeff i * z ^ i))
  have hval := hp_eval x z hz
  simpa [hsum, hsum'] using hval.symm

-- Universe-polymorphic root-count lemma (avoids universe mismatch with the appendix).
lemma eq_zero_of_card_lt_roots {F : Type*} [Field F] [DecidableEq F] {p : F[X]} {s : Finset F}
    (hs : ∀ z ∈ s, p.eval z = 0) (hcard : p.natDegree < s.card) : p = 0 := by
  classical
  by_contra hp
  have hsubset : s.val ⊆ p.roots := by
    intro z hz
    have hz' : p.eval z = 0 := hs z (by simpa using hz)
    have hroot : IsRoot p z := by simpa [IsRoot] using hz'
    exact (Polynomial.mem_roots hp).2 hroot
  have hle : s.card ≤ p.natDegree := by
    simpa using (Polynomial.card_le_degree_of_subset_roots (p := p) (Z := s) hsubset)
  exact (not_lt_of_ge hle hcard)

set_option maxHeartbeats 1200000 in
-- This lemma performs several `simp`/`sum` rewrites on polynomial expressions.
lemma curve_coeff_eq_of_agree_on
    {ι F : Type*} [Field F] [Fintype ι] [DecidableEq ι] [DecidableEq F]
    {l : ℕ} {S : Finset F} (hS : S.card > l + 1)
    {u v : Fin (l + 2) → ι → F}
    (hagree :
      ∀ z ∈ S,
        (fun x => ∑ i : Fin (l + 2), z ^ (i : ℕ) * u i x) =
          fun x => ∑ i : Fin (l + 2), z ^ (i : ℕ) * v i x) :
    u = v := by
  classical
  funext i x
  -- polynomial in `z` capturing the difference at a fixed coordinate `x`
  let q : F[X] := ∑ j : Fin (l + 2), Polynomial.monomial j.1 (u j x - v j x)
  have hq_eval : ∀ z ∈ S, q.eval z = 0 := by
    intro z hz
    have h_eq := congrArg (fun f => f x) (hagree z hz)
    have eval_sum_monomial (a : Fin (l + 2) → F) :
        (∑ j : Fin (l + 2), Polynomial.monomial j.1 (a j)).eval z =
          ∑ j : Fin (l + 2), (a j) * z ^ j.1 := by
      change (Polynomial.evalRingHom z)
          (∑ j : Fin (l + 2), Polynomial.monomial j.1 (a j)) = _
      simp [map_sum, Polynomial.eval_monomial]
    have hq_eval'' :
        q.eval z =
          ∑ j : Fin (l + 2), (u j x - v j x) * z ^ j.1 := by
      simpa [q] using (eval_sum_monomial (a := fun j => u j x - v j x))
    have hq_eval''' :
        q.eval z =
          (∑ j : Fin (l + 2), u j x * z ^ j.1) -
            (∑ j : Fin (l + 2), v j x * z ^ j.1) := by
      calc
        q.eval z =
            ∑ j : Fin (l + 2), (u j x - v j x) * z ^ j.1 := hq_eval''
        _ = ∑ j : Fin (l + 2), (u j x * z ^ j.1 - v j x * z ^ j.1) := by
              refine Finset.sum_congr rfl ?_
              intro j _hj
              simp [sub_mul]
        _ = (∑ j : Fin (l + 2), u j x * z ^ j.1) -
              (∑ j : Fin (l + 2), v j x * z ^ j.1) := by
              simp [Finset.sum_sub_distrib]
    have h_eq' :
        (∑ j : Fin (l + 2), u j x * z ^ j.1) =
          ∑ j : Fin (l + 2), v j x * z ^ j.1 := by
      simpa [mul_comm] using h_eq
    have hzero :
        (∑ j : Fin (l + 2), u j x * z ^ j.1) -
          (∑ j : Fin (l + 2), v j x * z ^ j.1) = 0 := by
      simpa using (sub_eq_zero.mpr h_eq')
    simpa [hq_eval'''] using hzero
  have hdeg_le : q.natDegree ≤ l + 1 := by
    have hbound :
        ∀ j ∈ (Finset.univ : Finset (Fin (l + 2))),
          (Polynomial.monomial j.1 (u j x - v j x)).natDegree ≤ l + 1 := by
      intro j _hj
      have hj : j.1 ≤ l + 1 := by
        exact Nat.le_of_lt_succ j.isLt
      exact (Polynomial.natDegree_monomial_le _).trans hj
    simpa [q] using
      (Polynomial.natDegree_sum_le_of_forall_le (s := (Finset.univ : Finset (Fin (l + 2))))
        (f := fun j => Polynomial.monomial j.1 (u j x - v j x)) hbound)
  have hdeg_lt : q.natDegree < S.card := lt_of_le_of_lt hdeg_le hS
  have hq_zero : q = 0 := eq_zero_of_card_lt_roots (p := q) (s := S) hq_eval hdeg_lt
  have hcoeff : q.coeff i.1 = 0 := by
    simpa using congrArg (fun p => p.coeff i.1) hq_zero
  have hcoeff' : q.coeff i.1 = u i x - v i x := by
    -- only the `i`-term contributes
    have hsum :
        q.coeff i.1 =
          ∑ j : Fin (l + 2), (Polynomial.monomial j.1 (u j x - v j x)).coeff i.1 := by
      simp [q]
    have hsum' :
        (∑ j : Fin (l + 2), (Polynomial.monomial j.1 (u j x - v j x)).coeff i.1) =
          u i x - v i x := by
      refine (Finset.sum_eq_single_of_mem i (by simp) ?_).trans ?_
      · intro j _hj hji
        have hne : j.1 ≠ i.1 := by
          intro h
          exact hji (by
            apply Fin.ext
            simpa using h)
        simp [Polynomial.coeff_monomial, hne]
      · simp
    simpa [hsum] using hsum'
  have hzero : u i x - v i x = 0 := by simpa [hcoeff'] using hcoeff
  exact sub_eq_zero.mp hzero

/-!
  ## Curve evaluation helpers

  We package the evaluation of a coefficient list `u` at a scalar `z` as a word on `ι`, and
  show that evaluations on a sufficiently large set of `z` determine the coefficients.
-/

def curveEval
    {ι F : Type*} [Field F]
    {l : ℕ} (u : Fin (l + 2) → ι → F) (z : F) : ι → F :=
  fun x => ∑ i : Fin (l + 2), z ^ (i : ℕ) * u i x

lemma curveEval_injective
    {ι F : Type*} [Field F] [Fintype ι] [DecidableEq ι] [DecidableEq F]
    {l : ℕ} {S : Finset F} (hS : S.card > l + 1) :
    Function.Injective (fun u : Fin (l + 2) → ι → F =>
      fun z : {z // z ∈ S} => curveEval (l := l) u z.1) := by
  classical
  intro u v h
  -- Equality of evaluations on `S` forces equality of coefficients.
  apply curve_coeff_eq_of_agree_on (l := l) (S := S) hS
  intro z hz
  have h' := congrArg (fun f => f ⟨z, hz⟩) h
  funext x
  simpa [curveEval] using congrArg (fun g => g x) h'

lemma card_curves_le_prod_lists
    {ι F : Type*} [Field F] [Fintype ι] [Fintype F] [DecidableEq ι] [DecidableEq F]
    {l : ℕ} {S : Finset F} (hS : S.card > l + 1)
    (L : {z // z ∈ S} → Finset (ι → F)) :
    Fintype.card {u : Fin (l + 2) → ι → F // ∀ z, curveEval (l := l) u z.1 ∈ L z} ≤
      Fintype.card (∀ z : {z // z ∈ S}, {w : ι → F // w ∈ L z}) := by
  classical
  let α := {u : Fin (l + 2) → ι → F // ∀ z, curveEval (l := l) u z.1 ∈ L z}
  let β := Π z : {z // z ∈ S}, {w : ι → F // w ∈ L z}
  -- Evaluation map into the product of lists.
  let f : α → β := fun u z => ⟨curveEval (l := l) u.1 z.1, u.2 z⟩
  have hf_inj : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    apply curveEval_injective (l := l) (S := S) hS
    funext z
    have h' := congrArg (fun g => g z) h
    exact congrArg Subtype.val h'
  have hcard : Fintype.card α ≤ Fintype.card β :=
    Fintype.card_le_of_injective f hf_inj
  exact hcard

end ProximityGap
