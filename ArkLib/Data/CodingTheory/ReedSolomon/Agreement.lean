/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.CodingTheory.Basic.Distance

/-!
# Polynomial agreement sets

These definitions record all coordinates where polynomial explanations match received words.
They use an arbitrary finite coordinate type, so a domain indexed by `Fin n`, a finite subtype,
or a chosen basis enumeration uses the same API. Neither definition imposes a degree bound:
Reed–Solomon statements must supply their strict message-degree hypotheses separately.

## Main statements

* `polynomialAgreementSet`, `commonPolynomialAgreementSet`: the coordinates of individual and
  simultaneous agreement.
* `polynomialAgreementSet_map`: an injective coefficient map preserves polynomial agreement.
* `card_polynomialAgreementSet`, `commonPolynomialAgreementSet_eq_inter`.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

/-- The full set of positions where `P` agrees with a received word. -/
def polynomialAgreementSet {F : Type*} [Semiring F] [DecidableEq F] {ι : Type*} [Fintype ι]
    (domain : ι ↪ F) (received : ι → F) (P : F[X]) : Finset ι :=
  Finset.univ.filter fun i ↦ P.eval (domain i) = received i

/-- The positions where two message polynomials simultaneously agree with two received words. -/
def commonPolynomialAgreementSet {F : Type*} [Semiring F] [DecidableEq F] {ι : Type*} [Fintype ι]
    (domain : ι ↪ F) (f g : ι → F) (F₀ G₀ : F[X]) : Finset ι :=
  Finset.univ.filter fun i ↦ F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i

/-- Membership in the agreement set is exactly the evaluation equality. -/
@[simp] theorem mem_polynomialAgreementSet
    {F ι : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (received : ι → F) (P : F[X]) (i : ι) :
    i ∈ polynomialAgreementSet domain received P ↔ P.eval (domain i) = received i := by
  simp [polynomialAgreementSet]

/-- Common agreement keeps both equalities at the same coordinate. -/
@[simp] theorem mem_commonPolynomialAgreementSet
    {F ι : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (f g : ι → F) (P Q : F[X]) (i : ι) :
    i ∈ commonPolynomialAgreementSet domain f g P Q ↔
      P.eval (domain i) = f i ∧ Q.eval (domain i) = g i := by
  simp [commonPolynomialAgreementSet]

/-- The common set is the intersection of the two individual agreement sets. -/
theorem commonPolynomialAgreementSet_eq_inter
    {F ι : Type*} [Semiring F] [DecidableEq F] [Fintype ι] [DecidableEq ι]
    (domain : ι ↪ F) (f g : ι → F) (P Q : F[X]) :
    commonPolynomialAgreementSet domain f g P Q =
      polynomialAgreementSet domain f P ∩ polynomialAgreementSet domain g Q := by
  ext i
  simp

/-- Polynomial agreement counts are the usual agreement counts of evaluation words. -/
theorem card_polynomialAgreementSet
    {F ι : Type*} [Semiring F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (received : ι → F) (P : F[X]) :
    (polynomialAgreementSet domain received P).card =
      Code.agree (evalOnPoints domain P) received := rfl

/-- An injective coefficient map preserves the polynomial agreement set. -/
theorem polynomialAgreementSet_map
    {F E ι : Type*} [Semiring F] [Semiring E] [DecidableEq F] [DecidableEq E]
    [Fintype ι] (domain : ι ↪ F) (φ : F →+* E)
    (hφ : Function.Injective φ) (received : ι → F) (P : F[X]) :
    polynomialAgreementSet (domain.trans ⟨φ, hφ⟩) (fun i ↦ φ (received i)) (P.map φ) =
      polynomialAgreementSet domain received P := by
  classical
  ext i
  simp only [mem_polynomialAgreementSet]
  change (P.map φ).eval (φ (domain i)) = φ (received i) ↔ _
  rw [Polynomial.eval_map_apply]
  exact hφ.eq_iff

end
end ReedSolomon
