/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability
/-!
# Exact Johnson mutual correlated agreement in every characteristic

A message polynomial has degree at most `D`, so the code dimension is `D + 1`. The Johnson
agreement fraction is `a = sqrt(D/n) + eta`: the ratio `D/n` in this formula is distinct from
the physical code rate `(D+1)/n`. A positive slack `eta` permits finite interpolation parameters.

The ordinary polynomial argument constructs one finite exceptional set for each received line.
Outside that set, every qualifying candidate has an exact correlated pair with equality of the
entire agreement set. Frobenius descent handles inseparability internally, so these statements
need no characteristic restriction and no algebraic-closure assumption on the caller's field.

`johnsonE0` counts exceptional challenges. Its terms are
`(2μ-1)h + θ(h+μ+4Dμh) + (n-D-1)μ`, with `θ = (n-D)/(A-D)` and the rounded Johnson
choices of μ and h. They account for exceptional specializations, incidence on factorwise
rational images, and accidental agreements on persistent graph lines, respectively.

The first theorem accepts an integer threshold `A`; the second sets `A = ceil(a*n)` exactly.
Only the final theorem assumes a finite field and divides the exceptional count by its size.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial HiddenDerivative CoreDefinitions LinearCode
open scoped ProbabilityTheory ENNReal

open Classical in
/-- **Outside at most `johnsonE0` challenges, every candidate has an exact correlated pair.**

Fix the integer agreement threshold above `sqrt(D/n) + eta`. For any distinct evaluation points
and received words f,g, choose one exceptional set before the challenge and candidate polynomial.
For every candidate P outside it, `HasExactCorrelatedPair` supplies P₀,P₁ with
`P = P₀ + z*P₁` and `Agr(f+z*g,P) = Agr(f,P₀) ∩ Agr(g,P₁)`.

The recovered pair may depend on z and P. The field may be infinite and have any characteristic.
-/
theorem exists_exceptional_johnson_lineMCA_allChar
    /-

    D is the maximum candidate degree, A is the number of required agreements.
    -/
    (n D A : ℕ) (eta : ℝ)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    /-

    a = sqrt(D/n) + eta; an integer A ≥ a*n represents the same agreement demand.
    -/
    (ha : johnsonAgreement n D eta ≤ 1)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n)
    /-

    An embedding ensures distinct evaluation points; no characteristic guard is needed.
    -/
    {F : Type*} [Field F] (domain : Fin n ↪ F) (f g : Fin n → F) :
    /-

    One exceptional set must work for all challenges and candidates quantified below.
    -/
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ johnsonE0 n D A eta ∧
      /-

      Every qualifying candidate outside the fixed exceptional set admits exact recovery.
      -/
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
  exact exists_exceptional_johnsonMCA domain f g hD hDn heta ha hthreshold hAn

open Classical in
/-- **The Johnson agreement demand with the exact integer threshold `ceil(a*n)`.**

Here a = sqrt(D/n) + eta. Rounding up is exactly what it means for an integer agreement count
to be at least a*n. The hypothesis a ≤ 1 ensures this threshold is at most n; the other
hypotheses already establish positivity of the incidence denominator.
-/
theorem exists_exceptional_johnson_lineMCA_at_ceil
    (n D : ℕ) (eta : ℝ)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    {F : Type*} [Field F] (domain : Fin n ↪ F) (f g : Fin n → F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤
        johnsonE0 n D (Nat.ceil (johnsonAgreement n D eta * n)) eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        Nat.ceil (johnsonAgreement n D eta * n) ≤
          (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
  apply exists_exceptional_johnson_lineMCA_allChar n D _ eta hD hDn heta ha
    (Nat.le_ceil _) _ domain f g
  exact Nat.ceil_le.mpr (by nlinarith [Nat.cast_nonneg n (α := ℝ)])

open Classical in
/-- **Uniform affine-line MCA failure probability is at most `min(1, E₀/|F|)`.**

The radius is 1-a, where a = sqrt(D/n) + eta. The exceptional-set theorem bounds the bad
challenges for every received line; uniform sampling divides that count by the field size.
The cap by one is the probability bound, not a change to the exceptional-set count.
-/
theorem johnson_lineMCA_probability
    (n D : ℕ) (eta : ℝ)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (ha : johnsonAgreement n D eta ≤ 1)
    /-

    Finiteness is needed here for uniform sampling, not for the preceding theorems.
    -/
    {F : Type} [Field F] [Fintype F] (domain : Fin n ↪ F) :
    /-

    Uniform sampling divides the exceptional count by the field size; the cap is one.
    -/
    mcaError (AffineLineGenerator F) (code domain (D + 1))
        (1 - johnsonAgreement n D eta) ≤
      min 1 (ENNReal.ofReal
        (johnsonE0 n D (Nat.ceil (johnsonAgreement n D eta * n)) eta /
          (Fintype.card F : ℝ))) := by
  exact johnson_mcaError_le domain hD hDn heta ha

end ReedSolomon
