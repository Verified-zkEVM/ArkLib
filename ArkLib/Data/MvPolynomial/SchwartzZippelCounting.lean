/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, Aristotle
-/
module

public import ArkLib.Data.Probability.Uniform
public import VCVio.OracleComp.Constructions.SampleableType.SchwartzZippel

/-!
# Schwartz–Zippel probability bounds

VCVio proves the counting and sampling bounds for polynomials over integral domains with any
finite variable type. The two lemmas here specialize its sampling bounds to `Fin s` variables over
a field.
-/

@[expose] public section

open scoped ENNReal

/-- A nonzero polynomial of total degree at most `d` vanishes on a uniform product sample with
probability at most `d / m` when every factor has at least `m` elements. -/
lemma prob_eval_zero_le_div
    {F : Type} [Field F] {s : ℕ} {S : Fin s → Set F} [∀ i, Fintype ↥(S i)]
    [SampleableType (∀ i, ↥(S i))]
    (f : MvPolynomial (Fin s) F) (hf : f ≠ 0)
    (d m : ℕ) (hd : f.totalDegree ≤ d) (hm : ∀ i, m ≤ (S i).toFinset.card) :
    Pr{let x ← $ᵗ (∀ i, ↥(S i))}[MvPolynomial.eval (fun i => (↑(x i) : F)) f = 0] ≤
      (d : ℝ≥0∞) / m :=
  prEvent_eval_eq_zero_le_div f hf d m hd hm

/-- The Schwartz–Zippel probability bound for a uniform assignment over a whole finite field. -/
lemma prob_eval_zero_univ_le_div
    {F : Type} [Field F] [Fintype F] [SampleableType F] {s d : ℕ}
    (f : MvPolynomial (Fin s) F) (hf : f ≠ 0) (hd : f.totalDegree ≤ d) :
    Pr{let x ← $ᵗ (Fin s → F)}[MvPolynomial.eval x f = 0] ≤
      (d : ℝ≥0∞) / Fintype.card F :=
  prEvent_eval_eq_zero_univ_le_div f hf hd
