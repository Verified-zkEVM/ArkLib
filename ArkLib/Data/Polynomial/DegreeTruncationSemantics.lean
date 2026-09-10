/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.DegreeTruncationMachine

/-!
# Polynomial meaning of checked coefficient truncation

The executed zero-prefix test accepts exactly polynomials of degree less than the requested
dimension, including zero. Its output denotes the same polynomial and has the requested physical
width when the input ambient width is at least the dimension. No normalization assumption on
leading coefficients is used.
-/

@[expose] public section

namespace Polynomial.JetHornerMachine

noncomputable section

variable {F : Type*} [CommSemiring F]

private theorem foldl_horner_eq (cs : List F) (p : F[X]) :
    cs.foldl (fun q a ↦ q * X + C a) p = p * X ^ cs.length + coefficientPolynomial cs := by
  induction cs generalizing p with
  | nil => simp [coefficientPolynomial]
  | cons a cs ih =>
      simp only [coefficientPolynomial, List.foldl_cons, List.length_cons, zero_mul, zero_add]
      rw [ih, ih]
      rw [pow_succ]
      ring

/-- The first descending coefficient occupies the degree given by the remaining list length. -/
theorem coefficientPolynomial_cons (a : F) (cs : List F) :
    coefficientPolynomial (a :: cs) = C a * X ^ cs.length + coefficientPolynomial cs := by
  simpa only [coefficientPolynomial, List.foldl_cons, zero_mul, zero_add] using
    foldl_horner_eq cs (C a)

/-- Every represented polynomial has degree strictly below its physical coefficient width. -/
theorem degree_coefficientPolynomial_lt_length (cs : List F) :
    (coefficientPolynomial cs).degree < cs.length := by
  induction cs with
  | nil => simp [coefficientPolynomial]
  | cons a cs ih =>
      rw [coefficientPolynomial_cons]
      apply (degree_add_le _ _).trans_lt
      apply max_lt
      · exact (degree_C_mul_X_pow_le cs.length a).trans_lt (by exact_mod_cast Nat.lt_succ_self _)
      · exact ih.trans (by exact_mod_cast Nat.lt_succ_self _)

/-- Removing a checked zero prefix preserves the represented polynomial. -/
theorem coefficientPolynomial_zero_prefix (n : ℕ) (cs : List F) :
    coefficientPolynomial (List.replicate n 0 ++ cs) = coefficientPolynomial cs := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, coefficientPolynomial_cons, ih]

/-- The physical leading coefficient is recoverable even when it equals zero. -/
theorem coeff_coefficientPolynomial_cons_length (a : F) (cs : List F) :
    (coefficientPolynomial (a :: cs)).coeff cs.length = a := by
  rw [coefficientPolynomial_cons, coeff_add,
    coeff_eq_zero_of_degree_lt (degree_coefficientPolynomial_lt_length cs)]
  simp

end
end Polynomial.JetHornerMachine

namespace Polynomial.DegreeTruncationMachine

noncomputable section

open JetHornerMachine

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- Under the physical-width relation, successful prefix removal is equivalent to the exact
polynomial degree condition, not merely a sufficient length test. -/
theorem exists_result_iff_degree_lt (n k : ℕ) (cs : List F) (hlen : cs.length = n + k) :
    (∃ out, result n cs = some out) ↔ (coefficientPolynomial cs).degree < k := by
  induction n generalizing cs with
  | zero =>
      constructor
      · intro _
        simpa only [hlen, zero_add] using degree_coefficientPolynomial_lt_length cs
      · intro _
        exact ⟨cs, rfl⟩
  | succ n ih =>
      cases cs with
      | nil => simp only [List.length_nil] at hlen; omega
      | cons a cs =>
          have htail : cs.length = n + k := by simp only [List.length_cons] at hlen; omega
          constructor
          · rintro ⟨out, hout⟩
            have hshape := (result_eq_some_iff (n + 1) (a :: cs) out).mp hout
            simp only [List.replicate_succ, List.cons_append, List.cons.injEq] at hshape
            rcases hshape with ⟨rfl, hs⟩
            have hsmall := (ih cs htail).mp ⟨out, (result_eq_some_iff n cs out).mpr hs⟩
            simpa [coefficientPolynomial_cons] using hsmall
          · intro hsmall
            have ha : a = 0 := by
              have hz := coeff_eq_zero_of_degree_lt
                (hsmall.trans_le (by exact_mod_cast (show k ≤ cs.length by omega)))
              simpa only [coeff_coefficientPolynomial_cons_length] using hz
            subst a
            have htailSmall : (coefficientPolynomial cs).degree < k := by
              simpa [coefficientPolynomial_cons] using hsmall
            obtain ⟨out, hout⟩ := (ih cs htail).mpr htailSmall
            exact ⟨out, by simpa [result] using hout⟩

/-- Successful execution emits an equal polynomial in a shorter materialized vector, and
rejects exactly when the original degree is too large. Its work bound is on that same run. -/
theorem truncation_runFuel_correct (w k : ℕ) (cs : List F)
    (hwidth : cs.length = w) (hk : k ≤ w) :
    ∃ out c, runFuel w k (w - k + 3) (.start cs) = (.done out, c) ∧
      (out ≠ none ↔ (coefficientPolynomial cs).degree < k) ∧
      (∀ tail, out = some tail → tail.length = k ∧
        coefficientPolynomial tail = coefficientPolynomial cs) ∧
      c.total ≤ 8 * (w - k + 3) := by
  obtain ⟨c, hrun, hcost⟩ := truncation_runFuel w k cs
  refine ⟨result (w - k) cs, c, hrun, ?_, ?_, hcost⟩
  · rw [Option.ne_none_iff_exists']
    exact exists_result_iff_degree_lt (w - k) k cs (by omega)
  · intro tail hout
    have hs := (result_eq_some_iff (w - k) cs tail).mp hout
    constructor
    · have hlen := congrArg List.length hs
      simp only [List.length_append, List.length_replicate] at hlen
      omega
    · rw [hs, coefficientPolynomial_zero_prefix]

end
end Polynomial.DegreeTruncationMachine
