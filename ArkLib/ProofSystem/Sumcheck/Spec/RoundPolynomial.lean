/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Julian Sutherland
-/

module

public import ArkLib.OracleReduction.CompPolyOracleInterface
public import CompPoly.Multivariate.Eval
public import CompPoly.Multivariate.FinSuccEquiv
public import CompPoly.Multivariate.Restrict
public import CompPoly.Univariate.ToPoly.Impl
public import CompPoly.ToMathlib.MvPolynomial.Equiv

/-!
# The projected round polynomial for a single sum-check round

The honest oracle-statement lens of `Spec/SingleRound.lean` materializes, from the multivariate
sum-check polynomial `p`, the univariate round polynomial

  `pᵢ(X) = ∑ x ∈ (univ.map D) ^ᶠ (n - i), p ⸨challenges, X, x⸩`.

The oracle statements are `CompPoly`-backed, so this file builds `pᵢ` as a
`CPolynomialDegreeLE R deg` (a `CompPoly.CPolynomial R` subtype), **computably**: each summand is
`CMvPolynomial.finSuccEquivNthHom i` (the computable `finSuccEquivNth` of
`ArkLib/ToCompPoly/Multivariate/FinSuccEquivNth.lean`) followed by mapping its coefficients through
the evaluation at the remaining-domain suffix.

The bridge lemma `projectedRoundPolynomial_eval_succ` re-expresses its evaluation as a Mathlib
`MvPolynomial.eval` sum, which is what lets the query-simulation and completeness proofs use
Mathlib's polynomial API unchanged.
-/

@[expose] public section

open MvPolynomial Polynomial Finset
open CompPoly CompPoly.CPolynomial CPoly CPoly.CMvPolynomial

namespace Sumcheck.Spec.SingleRound

open scoped Polynomial MvPolynomial

variable (R : Type) [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
  (n : ℕ) (deg : ℕ) {m : ℕ} (D : Fin m ↪ R)

/-- Assignment to the variables after round `i`, formed by appending the prior challenges to a
remaining-domain suffix.  Naming this cast-sensitive map keeps the materialized polynomial and
its query-by-query implementation definitionally aligned. -/
def roundSuffix (i : Fin (n + 1)) (challenges : Fin i.castSucc → R)
    (x : Fin (n - i) → R) : Fin n → R :=
  Fin.append challenges x ∘ Fin.cast (by simp; omega)

omit [BEq R] [LawfulBEq R] [Nontrivial R] in
/-- `fromCMvPolynomial` transports a per-variable degree bound into Mathlib's `restrictDegree`. -/
theorem fromCMvPolynomial_mem_restrictDegree {N d : ℕ} (p : CPoly.CMvPolynomial N R)
    (hp : ∀ i, p.degreeOf i ≤ d) :
    CPoly.fromCMvPolynomial p ∈ MvPolynomial.restrictDegree (Fin N) R d := by
  rw [MvPolynomial.mem_restrictDegree_iff_sup]
  intro i
  rw [← MvPolynomial.degreeOf_def,
    ← congrFun (CPoly.degreeOf_equiv (S := R) (p := p)) i]
  exact hp i

omit [BEq R] [LawfulBEq R] [Nontrivial R] in
/-- `fromCMvPolynomial` identifies `CompPoly`'s support (of `CMvMonomial`-indexed coefficients)
with Mathlib's `MvPolynomial.support`. -/
theorem support_fromCMvPolynomial {N : ℕ} (p : CPoly.CMvPolynomial N R) :
    (CPoly.fromCMvPolynomial p).support = p.support := by
  ext σ
  rw [MvPolynomial.mem_support_iff, CPoly.coeff_eq, ← CPoly.CMvPolynomial.support_def]

omit [Nontrivial R] in
/-- `CompPoly`'s own `restrictDegree` membership agrees with a per-variable `degreeOf` bound. -/
theorem mem_restrictDegree_iff_degreeOf_le {N d : ℕ} {p : CPoly.CMvPolynomial N R} :
    p ∈ CPoly.restrictDegree R N d ↔ ∀ i : Fin N, p.degreeOf i ≤ d := by
  rw [CPoly.restrictDegree_elem]
  constructor
  · intro h i
    rw [congrFun (CPoly.degreeOf_equiv (S := R) (p := p)) i, MvPolynomial.degreeOf_le_iff,
      support_fromCMvPolynomial]
    exact fun σ hσ => h σ hσ i
  · intro h σ hσ i
    have hi := h i
    rw [congrFun (CPoly.degreeOf_equiv (S := R) (p := p)) i, MvPolynomial.degreeOf_le_iff,
      support_fromCMvPolynomial] at hi
    exact hi σ hσ

/-- The (value part of the) round polynomial at round `i`: split variable `i` off with the
computable `finSuccEquivNth`, map the (`CMvPolynomial n R`) coefficients through evaluation at the
prior challenges and a domain suffix, and sum over the suffix.  Computable. -/
def roundPolyBody (i : Fin (n + 1)) (challenges : Fin i.castSucc → R)
    (poly : CPoly.CMvPolynomial (n + 1) R) : CompPoly.CPolynomial R :=
  ∑ x ∈ (univ.map D) ^ᶠ (n - i),
    CompPoly.CPolynomial.mapRingHom
      (CPoly.CMvPolynomial.evalHom (roundSuffix R n i challenges x))
      (CPoly.CMvPolynomial.finSuccEquivNthHom i poly)

omit [Nontrivial R] in
private lemma _natDegree_finset_sum_le {α : Type*} (d : ℕ) (s : Finset α)
    (f : α → CompPoly.CPolynomial R) (h : ∀ a ∈ s, (f a).natDegree ≤ d) :
    (∑ a ∈ s, f a).natDegree ≤ d := by
  have : DecidableEq R := instDecidableEqOfLawfulBEq
  induction s using Finset.cons_induction_on with
  | empty =>
      rw [Finset.sum_empty, CompPoly.CPolynomial.natDegree_zero]
      exact Nat.zero_le _
  | cons a s ha ih =>
      rw [Finset.sum_cons]
      exact (CompPoly.CPolynomial.natDegree_add_le _ _).trans
        (max_le (h a (Finset.mem_cons_self ..))
          (ih fun a' ha' => h a' (Finset.mem_cons_of_mem ha')))

theorem roundPolyBody_natDegree_le (i : Fin (n + 1)) (challenges : Fin i.castSucc → R)
    (poly : CPoly.CMvPolynomial (n + 1) R) (hp : ∀ k, poly.degreeOf k ≤ deg) :
    (roundPolyBody R n D i challenges poly).natDegree ≤ deg := by
  refine _natDegree_finset_sum_le R deg _ _ (fun x _ => ?_)
  exact (CompPoly.CPolynomial.natDegree_mapRingHom_le _ _).trans
    (CPoly.CMvPolynomial.natDegree_finSuccEquivNthHom_le i poly hp)

/-- The projected round polynomial for round `i`, as a `CompPoly`-backed univariate polynomial of
degree at most `deg`.  Computable. -/
def projectedRoundPolynomial (i : Fin n) (challenges : Fin i.castSucc → R)
    (poly : CPoly.restrictDegree R n deg) :
    CompPoly.CPolynomial.degreeLE (R := R) (deg : WithBot ℕ) :=
  match n, i, challenges, poly with
  | 0, i, _, _ => Fin.elim0 i
  | _ + 1, i, challenges, poly =>
      ⟨roundPolyBody R _ D i challenges poly.1,
        (CompPoly.CPolynomial.mem_degreeLE_iff_natDegree_le R).mpr
          (roundPolyBody_natDegree_le R _ deg D i challenges poly.1
            ((mem_restrictDegree_iff_degreeOf_le (R := R)).mp poly.2))⟩

/-- **The bridge.**  Evaluating the projected round polynomial at `r` is the Mathlib
`MvPolynomial.eval` sum over the remaining domain, at the point that inserts `r` in slot `i`. -/
theorem projectedRoundPolynomial_eval_succ (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CPoly.restrictDegree R (n + 1) deg) (r : R) :
    CompPoly.CPolynomial.eval r
        (projectedRoundPolynomial R (n + 1) deg D i challenges poly).1
      = ∑ x ∈ (univ.map D) ^ᶠ (n - i),
          MvPolynomial.eval (Fin.insertNth i r (roundSuffix R n i challenges x))
            (CPoly.fromCMvPolynomial poly.1) := by
  have hcompeval : ∀ x : Fin (n - i) → R,
      (CompPoly.CPolynomial.eval₂Hom (CPoly.CMvPolynomial.evalHom
              (roundSuffix R n i challenges x)) r).comp
          (CPoly.CMvPolynomial.finSuccEquivNthHom i)
        = CPoly.CMvPolynomial.evalHom
            (Fin.insertNth i r (roundSuffix R n i challenges x)) := fun x => by
    refine CPoly.CMvPolynomial.ringHom_ext (fun c => ?_) (fun k => ?_)
    · rw [RingHom.comp_apply, CPoly.CMvPolynomial.finSuccEquivNthHom_C,
        CompPoly.CPolynomial.eval₂Hom_C, CPoly.CMvPolynomial.evalHom_apply,
        CPoly.CMvPolynomial.evalHom_apply, CMvPolynomial.eval_C, CMvPolynomial.eval_C]
    · refine Fin.succAboveCases i ?_ ?_ k
      · rw [RingHom.comp_apply, CPoly.CMvPolynomial.finSuccEquivNthHom_X_same,
          CompPoly.CPolynomial.eval₂Hom_X, CPoly.CMvPolynomial.evalHom_apply,
          CPoly.CMvPolynomial.eval_X, Fin.insertNth_apply_same]
      · intro j
        rw [RingHom.comp_apply, CPoly.CMvPolynomial.finSuccEquivNthHom_X_succAbove,
          CompPoly.CPolynomial.eval₂Hom_C, CPoly.CMvPolynomial.evalHom_apply,
          CPoly.CMvPolynomial.evalHom_apply, CPoly.CMvPolynomial.eval_X,
          CPoly.CMvPolynomial.eval_X, Fin.insertNth_apply_succAbove]
  change CompPoly.CPolynomial.eval r
      (roundPolyBody R n D i challenges poly.1) = _
  rw [CompPoly.CPolynomial.eval_eq_eval₂, ← CompPoly.CPolynomial.eval₂Hom_apply, roundPolyBody,
    map_sum (CompPoly.CPolynomial.eval₂Hom (RingHom.id R) r)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [CompPoly.CPolynomial.eval₂Hom_apply, ← CompPoly.CPolynomial.eval_eq_eval₂,
    CompPoly.CPolynomial.eval_mapRingHom, ← CompPoly.CPolynomial.eval₂Hom_apply,
    ← RingHom.comp_apply, hcompeval, CPoly.CMvPolynomial.evalHom_apply, CPoly.eval_equiv]

end Sumcheck.Spec.SingleRound
