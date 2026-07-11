/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.BigOperators
import CompPoly.Data.MvPolynomial.Notation
import CompPoly.Multivariate.Operations
import CompPoly.Multivariate.MvPolyEquiv.Eval
import CompPoly.Univariate.ToPoly.Impl
import ArkLib.Data.CompPoly.Basic

/-!
# Sumcheck-Oriented `CMvPolynomial` Operations

This module collects computable `CMvPolynomial` operations used by downstream
sumcheck formalizations: partial evaluation of the first or last variable,
finite-domain summation of the last variable, and conversion of a one-variable
`CMvPolynomial` to `CPolynomial`.
-/

open CompPoly Std

namespace CompPoly

namespace CPolynomial

variable {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- The embedding `R → CPolynomial R` via constant polynomials, bundled as a
ring homomorphism. -/
def CRingHom : R →+* CPolynomial R where
  toFun := CPolynomial.C
  map_zero' := by
    apply (CPolynomial.ringEquiv (R := R)).injective
    change (CPolynomial.C (0 : R)).toPoly = (0 : CPolynomial R).toPoly
    rw [CPolynomial.C_toPoly, CPolynomial.toPoly_zero]
    simp
  map_one' := by
    apply (CPolynomial.ringEquiv (R := R)).injective
    change (CPolynomial.C (1 : R)).toPoly = (1 : CPolynomial R).toPoly
    rw [CPolynomial.C_toPoly, CPolynomial.toPoly_one]
    simp
  map_add' x y := by
    apply (CPolynomial.ringEquiv (R := R)).injective
    change (CPolynomial.C (x + y)).toPoly = (CPolynomial.C x + CPolynomial.C y).toPoly
    rw [CPolynomial.C_toPoly, CPolynomial.toPoly_add,
      CPolynomial.C_toPoly, CPolynomial.C_toPoly]
    simp
  map_mul' x y := by
    apply (CPolynomial.ringEquiv (R := R)).injective
    change (CPolynomial.C (x * y)).toPoly = (CPolynomial.C x * CPolynomial.C y).toPoly
    rw [CPolynomial.C_toPoly, CPolynomial.toPoly_mul,
      CPolynomial.C_toPoly, CPolynomial.C_toPoly]
    simp

end CPolynomial

end CompPoly

namespace CPoly

namespace CMvPolynomial

variable {n : ℕ} {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- The computable substitution `bind₁` agrees with Mathlib substitution after
transporting through `fromCMvPolynomial`. -/
theorem fromCMvPolynomial_bind₁ {m : ℕ}
    (f : Fin n → CMvPolynomial m R) (p : CMvPolynomial n R) :
    fromCMvPolynomial (bind₁ f p) =
      MvPolynomial.eval₂ MvPolynomial.C (fun i => fromCMvPolynomial (f i))
        (fromCMvPolynomial p) := by
  rw [bind₁_eq_aeval]
  unfold aeval
  have h := MvPolynomial.map_eval₂Hom
    (f := algebraMap R (CMvPolynomial m R))
    (g := f)
    (φ := (CPoly.polyRingEquiv (n := m) (R := R)).toRingHom)
    (p := fromCMvPolynomial p)
  have hcomp :
      ((CPoly.polyRingEquiv (n := m) (R := R)).toRingHom).comp
        (algebraMap R (CMvPolynomial m R)) = MvPolynomial.C := by
    ext r μ
    rw [RingHom.comp_apply]
    change MvPolynomial.coeff μ
        (fromCMvPolynomial (algebraMap R (CMvPolynomial m R) r)) =
      MvPolynomial.coeff μ (MvPolynomial.C r)
    rw [show (algebraMap R (CMvPolynomial m R)) r = CMvPolynomial.C (n := m) r from rfl]
    rw [fromCMvPolynomial_C]
  rw [eval₂_equiv (p := p) (f := algebraMap R (CMvPolynomial m R)) (vals := f)]
  have h' :
      fromCMvPolynomial
          (MvPolynomial.eval₂ (algebraMap R (CMvPolynomial m R)) f
            (fromCMvPolynomial p)) =
        MvPolynomial.eval₂
          (((CPoly.polyRingEquiv (n := m) (R := R)).toRingHom).comp
            (algebraMap R (CMvPolynomial m R)))
          (fun i => fromCMvPolynomial (f i))
          (fromCMvPolynomial p) := by
    simpa [CPoly.polyRingEquiv, CPoly.polyEquiv] using h
  rw [hcomp] at h'
  exact h'

omit [BEq R] [LawfulBEq R] in
private lemma partialEvalFirst_subst_degreeOf_le [Nontrivial R] (a : R)
    (i : Fin n) (j : Fin (n + 1)) :
    MvPolynomial.degreeOf i
      (Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) j :
        MvPolynomial (Fin n) R) ≤ if j = i.succ then 1 else 0 := by
  cases j using Fin.cases with
  | zero =>
      simp [MvPolynomial.degreeOf_C]
  | succ j =>
      by_cases h : j = i
      · subst h
        simp [MvPolynomial.degreeOf_X]
      · have hsucc : Fin.succ j ≠ i.succ := by
          intro h'
          exact h ((Fin.succ_injective n) h')
        have hi_ne_j : i ≠ j := fun hij => h hij.symm
        simp [hsucc, hi_ne_j, MvPolynomial.degreeOf_X]

omit [BEq R] [LawfulBEq R] in
private lemma partialEvalFirst_eval₂_monomial_degreeOf_le [Nontrivial R] {deg : ℕ}
    (a : R) (i : Fin n) (s : Fin (n + 1) →₀ ℕ) (c : R)
    (hs : s i.succ ≤ deg) :
    MvPolynomial.degreeOf i
      (MvPolynomial.eval₂ MvPolynomial.C
        (fun j : Fin (n + 1) =>
          Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) j)
        (MvPolynomial.monomial s c) : MvPolynomial (Fin n) R) ≤ deg := by
  rw [MvPolynomial.eval₂_monomial]
  refine (MvPolynomial.degreeOf_C_mul_le _ i c).trans ?_
  rw [Finsupp.prod]
  refine (MvPolynomial.degreeOf_prod_le i s.support
    (fun j => (Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) j :
      MvPolynomial (Fin n) R) ^ s j)).trans ?_
  calc
    (∑ x ∈ s.support,
        MvPolynomial.degreeOf i
          ((Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) x :
            MvPolynomial (Fin n) R) ^ s x))
        ≤ ∑ x ∈ s.support, s x * (if x = i.succ then 1 else 0) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact (MvPolynomial.degreeOf_pow_le i
            (Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) x :
              MvPolynomial (Fin n) R) (s x)).trans
            (Nat.mul_le_mul_left _ (partialEvalFirst_subst_degreeOf_le a i x))
    _ ≤ s i.succ := by
          classical
          by_cases hi : i.succ ∈ s.support
          · rw [Finset.sum_eq_single i.succ]
            · simp
            · intro x hx hne
              simp [hne]
            · intro hnot
              exact False.elim (hnot hi)
          · rw [Finset.sum_eq_zero]
            · simp
            · intro x hx
              have hne : x ≠ i.succ := fun h => hi (h ▸ hx)
              simp [hne]
    _ ≤ deg := hs

omit [BEq R] [LawfulBEq R] in
private lemma partialEvalFirst_eval₂_degreeOf_le [Nontrivial R] {deg : ℕ}
    (a : R) (i : Fin n) (p : MvPolynomial (Fin (n + 1)) R)
    (hDeg : ∀ s ∈ p.support, s i.succ ≤ deg) :
    MvPolynomial.degreeOf i
      (MvPolynomial.eval₂ MvPolynomial.C
        (fun j : Fin (n + 1) =>
          Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) j)
        p : MvPolynomial (Fin n) R) ≤ deg := by
  rw [MvPolynomial.eval₂_eq]
  refine (MvPolynomial.degreeOf_sum_le i p.support
    (fun s => MvPolynomial.C (p.coeff s) *
      ∏ x ∈ s.support,
        (Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) x :
          MvPolynomial (Fin n) R) ^ s x)).trans ?_
  apply Finset.sup_le
  intro s hs
  simpa [MvPolynomial.eval₂_monomial, Finsupp.prod] using
    partialEvalFirst_eval₂_monomial_degreeOf_le (n := n) (R := R)
      (deg := deg) a i s (p.coeff s) (hDeg s hs)

/-! ## Core operations -/

/-- Fix variable 0 of a multivariate polynomial to a scalar value `a`. -/
def partialEvalFirst (a : R) (p : CMvPolynomial (n + 1) R) : CMvPolynomial n R :=
  bind₁ (Fin.cons (C a) X) p

/-- Fix the last variable of a multivariate polynomial to a scalar value `a`. -/
def partialEvalLast (a : R) (p : CMvPolynomial (n + 1) R) : CMvPolynomial n R :=
  bind₁ (Fin.snoc X (C a)) p

variable {m : ℕ}

/-- Sum out the last variable of a polynomial over domain `D`. -/
def sumOverLast (D : Fin m → R) (p : CMvPolynomial (n + 1) R) : CMvPolynomial n R :=
  (Finset.univ : Finset (Fin m)).sum (fun j => partialEvalLast (D j) p)

/-- Iterate `sumOverLast` to sum out all variables except variable 0. -/
def sumAllButFirst (D : Fin m → R) : (k : ℕ) → CMvPolynomial (k + 1) R → CMvPolynomial 1 R
  | 0, p => p
  | k + 1, p => sumAllButFirst D k (sumOverLast D p)

/-- Split a function on `Fin (k + 1)` into its initial `k` entries and its
last entry, with the pair order convenient for iterated sums. -/
private def snocFunEquiv (k m : ℕ) : ((Fin k → Fin m) × Fin m) ≃ (Fin (k + 1) → Fin m) where
  toFun := fun z => Fin.snoc z.1 z.2
  invFun := fun f => (Fin.init f, f (Fin.last k))
  left_inv z := by simp
  right_inv f := by simp

/-! ## Evaluation lemmas -/

/-- `partialEvalFirst a p` correctly implements partial evaluation. -/
theorem partialEvalFirst_eval (a : R) (p : CMvPolynomial (n + 1) R) (v : Fin n → R) :
    (partialEvalFirst a p).eval v = p.eval (Fin.cons a v) := by
  unfold partialEvalFirst
  rw [eval_equiv, fromCMvPolynomial_bind₁]
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (MvPolynomial.eval v).comp MvPolynomial.C = RingHom.id R := by
    ext r
    simp
  have hv :
      (⇑(MvPolynomial.eval v) ∘
          fun i => fromCMvPolynomial
            (((Fin.cons (CMvPolynomial.C (n := n) a)
              (fun i : Fin n => CMvPolynomial.X (R := R) i)) :
                Fin (n + 1) → CMvPolynomial n R) i)) =
        Fin.cons a v := by
    funext i
    cases i using Fin.cases with
    | zero => simp [fromCMvPolynomial_C]
    | succ i => simp [fromCMvPolynomial_X]
  rw [hc, hv]
  exact (eval_equiv (p := p) (vals := Fin.cons a v)).symm

/-- `partialEvalLast a p` correctly implements partial evaluation of the last variable. -/
theorem partialEvalLast_eval (a : R) (p : CMvPolynomial (n + 1) R) (v : Fin n → R) :
    (partialEvalLast a p).eval v = p.eval (Fin.snoc v a) := by
  unfold partialEvalLast
  rw [eval_equiv, fromCMvPolynomial_bind₁]
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (MvPolynomial.eval v).comp MvPolynomial.C = RingHom.id R := by
    ext r
    simp
  have hv :
      (⇑(MvPolynomial.eval v) ∘
          fun i => fromCMvPolynomial
            (((Fin.snoc (fun i : Fin n => CMvPolynomial.X (R := R) i)
              (CMvPolynomial.C (n := n) a)) :
                Fin (n + 1) → CMvPolynomial n R) i)) =
        Fin.snoc v a := by
    funext i
    cases i using Fin.lastCases with
    | last => simp [fromCMvPolynomial_C]
    | cast i => simp [fromCMvPolynomial_X]
  rw [hc, hv]
  exact (eval_equiv (p := p) (vals := Fin.snoc v a)).symm

/-- `sumOverLast` evaluates by summing the polynomial over the last variable. -/
theorem sumOverLast_eval (D : Fin m → R) (p : CMvPolynomial (n + 1) R) (v : Fin n → R) :
    (sumOverLast D p).eval v =
      (Finset.univ : Finset (Fin m)).sum (fun j => p.eval (Fin.snoc v (D j))) := by
  unfold sumOverLast CMvPolynomial.eval
  rw [show CMvPolynomial.eval₂ (RingHom.id R) v (∑ j, partialEvalLast (D j) p) =
      ∑ j : Fin m, CMvPolynomial.eval₂ (RingHom.id R) v (partialEvalLast (D j) p) from by
    exact _root_.map_sum (CMvPolynomial.eval₂Hom (RingHom.id R) v)
      (fun j : Fin m => partialEvalLast (D j) p) Finset.univ]
  apply Finset.sum_congr rfl
  intro j _hj
  exact partialEvalLast_eval (n := n) (R := R) (D j) p v

/-- Summing out all variables except the first agrees with direct evaluation over
the remaining domain points. -/
theorem sumAllButFirst_eval (D : Fin m → R) :
    ∀ (k : ℕ) (p : CMvPolynomial (k + 1) R) (x : R),
      (sumAllButFirst D k p).eval (fun _ : Fin 1 => x) =
        (Finset.univ : Finset (Fin k → Fin m)).sum (fun z =>
          p.eval (Fin.cons x (D ∘ z))) := by
  intro k
  induction k with
  | zero =>
      intro p x
      simp [sumAllButFirst]
      congr
      funext i
      fin_cases i
      rfl
  | succ k ih =>
      intro p x
      simp [sumAllButFirst]
      rw [ih]
      simp only [sumOverLast_eval]
      rw [← Finset.sum_product'
        (Finset.univ : Finset (Fin k → Fin m)) (Finset.univ : Finset (Fin m))]
      refine Fintype.sum_equiv (snocFunEquiv k m)
        (fun zj : (Fin k → Fin m) × Fin m =>
          p.eval (Fin.snoc (Fin.cons x (D ∘ zj.1)) (D zj.2)))
        (fun z : Fin (k + 1) → Fin m => p.eval (Fin.cons x (D ∘ z))) ?_
      intro zj
      simp only [snocFunEquiv]
      congr 1
      rw [← Fin.cons_snoc_eq_snoc_cons]
      congr 1
      change Fin.snoc (D ∘ zj.1) (D zj.2) = D ∘ Fin.snoc zj.1 zj.2
      rw [Fin.comp_snoc]

/-! ## Degree preservation -/

/-- `partialEvalFirst` preserves degree bounds for each remaining variable. -/
theorem partialEvalFirst_degreeOf_le [Nontrivial R] {deg : ℕ} (a : R)
    (i : Fin n) (p : CMvPolynomial (n + 1) R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.degreeOf i.succ ≤ deg) :
    ∀ mono ∈ Lawful.monomials (partialEvalFirst a p), mono.degreeOf i ≤ deg := by
  intro mono hmono
  have hSupport :
      ∀ s ∈ (fromCMvPolynomial p).support, s i.succ ≤ deg := by
    apply MvPolynomial.degreeOf_le_iff.mp
    have hdegree := congrFun (degreeOf_equiv (p := p) (S := R)) i.succ
    rw [← hdegree]
    unfold CMvPolynomial.degreeOf
    apply Finset.sup_le
    intro mono hmono
    exact hDeg mono (by simpa using hmono)
  have hEval :
      MvPolynomial.degreeOf i (fromCMvPolynomial (partialEvalFirst a p)) ≤ deg := by
    unfold partialEvalFirst
    rw [fromCMvPolynomial_bind₁]
    have hvars :
        (fun i : Fin (n + 1) =>
            fromCMvPolynomial
              (((Fin.cons (CMvPolynomial.C (n := n) a)
                (fun i : Fin n => CMvPolynomial.X (R := R) i)) :
                  Fin (n + 1) → CMvPolynomial n R) i)) =
          (fun j : Fin (n + 1) =>
            Fin.cases (MvPolynomial.C a) (fun k : Fin n => MvPolynomial.X k) j) := by
      funext j
      cases j using Fin.cases with
      | zero => simp [fromCMvPolynomial_C]
      | succ j => simp [fromCMvPolynomial_X]
    rw [hvars]
    exact partialEvalFirst_eval₂_degreeOf_le (n := n) (R := R) a i
      (fromCMvPolynomial p) hSupport
  have hdegree := congrFun (degreeOf_equiv (p := partialEvalFirst a p) (S := R)) i
  rw [← hdegree] at hEval
  exact (Finset.le_sup (s := (Lawful.monomials (partialEvalFirst a p)).toFinset)
    (f := fun m => m.degreeOf i) (by simpa using hmono)).trans hEval

omit [BEq R] [LawfulBEq R] in
private lemma partialEvalLast_subst_degreeOf_le [Nontrivial R] (a : R)
    (i : Fin n) (j : Fin (n + 1)) :
    MvPolynomial.degreeOf i
      (@Fin.snoc n (fun _ => MvPolynomial (Fin n) R)
        (fun k : Fin n => MvPolynomial.X k) (MvPolynomial.C a) j) ≤
        if j = i.castSucc then 1 else 0 := by
  cases j using Fin.lastCases with
  | last =>
      have hlast : Fin.last n ≠ i.castSucc := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
        omega
      simp [hlast, MvPolynomial.degreeOf_C]
  | cast j =>
      by_cases h : j = i
      · subst h
        simp [MvPolynomial.degreeOf_X]
      · have hcast : j.castSucc ≠ i.castSucc := by
          intro h'
          exact h (Fin.ext (by simpa using congrArg Fin.val h'))
        have hi_ne_j : i ≠ j := fun hij => h hij.symm
        simp [hcast, hi_ne_j, MvPolynomial.degreeOf_X]

omit [BEq R] [LawfulBEq R] in
private lemma partialEvalLast_eval₂_monomial_degreeOf_le [Nontrivial R] {deg : ℕ}
    (a : R) (i : Fin n) (s : Fin (n + 1) →₀ ℕ) (c : R)
    (hs : s i.castSucc ≤ deg) :
    MvPolynomial.degreeOf i
      (MvPolynomial.eval₂ MvPolynomial.C
        (fun j : Fin (n + 1) =>
          @Fin.snoc n (fun _ => MvPolynomial (Fin n) R)
            (fun k : Fin n => MvPolynomial.X k) (MvPolynomial.C a) j)
        (MvPolynomial.monomial s c) : MvPolynomial (Fin n) R) ≤ deg := by
  rw [MvPolynomial.eval₂_monomial]
  refine (MvPolynomial.degreeOf_C_mul_le _ i c).trans ?_
  rw [Finsupp.prod]
  refine (MvPolynomial.degreeOf_prod_le i s.support
    (fun j => (@Fin.snoc n (fun _ => MvPolynomial (Fin n) R)
      (fun k : Fin n => MvPolynomial.X k) (MvPolynomial.C a) j) ^ s j)).trans ?_
  calc
    (∑ x ∈ s.support,
        MvPolynomial.degreeOf i
          ((@Fin.snoc n (fun _ => MvPolynomial (Fin n) R)
            (fun k : Fin n => MvPolynomial.X k) (MvPolynomial.C a) x) ^ s x))
        ≤ ∑ x ∈ s.support, s x * (if x = i.castSucc then 1 else 0) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact (MvPolynomial.degreeOf_pow_le i
            (@Fin.snoc n (fun _ => MvPolynomial (Fin n) R)
              (fun k : Fin n => MvPolynomial.X k) (MvPolynomial.C a) x) (s x)).trans
            (Nat.mul_le_mul_left _ (partialEvalLast_subst_degreeOf_le a i x))
    _ ≤ s i.castSucc := by
          classical
          by_cases hi : i.castSucc ∈ s.support
          · rw [Finset.sum_eq_single i.castSucc]
            · simp
            · intro x hx hne
              simp [hne]
            · intro hnot
              exact False.elim (hnot hi)
          · rw [Finset.sum_eq_zero]
            · simp
            · intro x hx
              have hne : x ≠ i.castSucc := fun h => hi (h ▸ hx)
              simp [hne]
    _ ≤ deg := hs

omit [BEq R] [LawfulBEq R] in
private lemma partialEvalLast_eval₂_degreeOf_le [Nontrivial R] {deg : ℕ}
    (a : R) (i : Fin n) (p : MvPolynomial (Fin (n + 1)) R)
    (hDeg : ∀ s ∈ p.support, s i.castSucc ≤ deg) :
    MvPolynomial.degreeOf i
      (MvPolynomial.eval₂ MvPolynomial.C
        (fun j : Fin (n + 1) =>
          @Fin.snoc n (fun _ => MvPolynomial (Fin n) R)
            (fun k : Fin n => MvPolynomial.X k) (MvPolynomial.C a) j)
        p : MvPolynomial (Fin n) R) ≤ deg := by
  rw [MvPolynomial.eval₂_eq]
  refine (MvPolynomial.degreeOf_sum_le i p.support
    (fun s => MvPolynomial.C (p.coeff s) *
      ∏ x ∈ s.support,
        (@Fin.snoc n (fun _ => MvPolynomial (Fin n) R)
          (fun k : Fin n => MvPolynomial.X k) (MvPolynomial.C a) x) ^ s x)).trans ?_
  apply Finset.sup_le
  intro s hs
  simpa [MvPolynomial.eval₂_monomial, Finsupp.prod] using
    partialEvalLast_eval₂_monomial_degreeOf_le (n := n) (R := R)
      (deg := deg) a i s (p.coeff s) (hDeg s hs)

/-- `partialEvalLast` preserves degree bounds for each remaining variable. -/
theorem partialEvalLast_degreeOf_le [Nontrivial R] {deg : ℕ} (a : R)
    (i : Fin n) (p : CMvPolynomial (n + 1) R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.degreeOf i.castSucc ≤ deg) :
    ∀ mono ∈ Lawful.monomials (partialEvalLast a p), mono.degreeOf i ≤ deg := by
  intro mono hmono
  have hSupport :
      ∀ s ∈ (fromCMvPolynomial p).support, s i.castSucc ≤ deg := by
    apply MvPolynomial.degreeOf_le_iff.mp
    have hdegree := congrFun (degreeOf_equiv (p := p) (S := R)) i.castSucc
    rw [← hdegree]
    unfold CMvPolynomial.degreeOf
    apply Finset.sup_le
    intro mono hmono
    exact hDeg mono (by simpa using hmono)
  have hEval :
      MvPolynomial.degreeOf i (fromCMvPolynomial (partialEvalLast a p)) ≤ deg := by
    unfold partialEvalLast
    rw [fromCMvPolynomial_bind₁]
    have hvars :
        (fun i : Fin (n + 1) =>
            fromCMvPolynomial
              (((Fin.snoc (fun i : Fin n => CMvPolynomial.X (R := R) i)
                (CMvPolynomial.C (n := n) a)) :
                  Fin (n + 1) → CMvPolynomial n R) i)) =
          (fun j : Fin (n + 1) =>
            @Fin.snoc n (fun _ => MvPolynomial (Fin n) R)
              (fun k : Fin n => MvPolynomial.X k) (MvPolynomial.C a) j) := by
      funext j
      cases j using Fin.lastCases with
      | last => simp [fromCMvPolynomial_C]
      | cast j => simp [fromCMvPolynomial_X]
    rw [hvars]
    exact partialEvalLast_eval₂_degreeOf_le (n := n) (R := R) a i
      (fromCMvPolynomial p) hSupport
  have hdegree := congrFun (degreeOf_equiv (p := partialEvalLast a p) (S := R)) i
  rw [← hdegree] at hEval
  exact (Finset.le_sup (s := (Lawful.monomials (partialEvalLast a p)).toFinset)
    (f := fun m => m.degreeOf i) (by simpa using hmono)).trans hEval

/-- Summing out the last variable preserves the degree bound in variable `0`. -/
theorem sumOverLast_degreeOf_zero_le [Nontrivial R] {deg : ℕ} (D : Fin m → R)
    (p : CMvPolynomial (n + 2) R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.degreeOf 0 ≤ deg) :
    ∀ mono ∈ Lawful.monomials (sumOverLast D p), mono.degreeOf 0 ≤ deg := by
  intro mono hmono
  have hEval :
      MvPolynomial.degreeOf (0 : Fin (n + 1)) (fromCMvPolynomial (sumOverLast D p)) ≤ deg := by
    unfold sumOverLast
    change MvPolynomial.degreeOf (0 : Fin (n + 1))
      ((CPoly.polyRingEquiv (n := n + 1) (R := R))
        ((Finset.univ : Finset (Fin m)).sum (fun j => partialEvalLast (D j) p))) ≤ deg
    rw [map_sum]
    refine (MvPolynomial.degreeOf_sum_le (0 : Fin (n + 1)) (Finset.univ : Finset (Fin m))
      (fun j => fromCMvPolynomial (partialEvalLast (D j) p))).trans ?_
    apply Finset.sup_le
    intro j hj
    have hcast : ((0 : Fin (n + 1)).castSucc : Fin (n + 2)) = 0 := rfl
    have hinput :
        ∀ mono ∈ Lawful.monomials p,
          mono.degreeOf ((0 : Fin (n + 1)).castSucc : Fin (n + 2)) ≤ deg := by
      intro mono hmono
      simpa [hcast] using hDeg mono hmono
    have hcmv :
        CMvPolynomial.degreeOf (0 : Fin (n + 1)) (partialEvalLast (D j) p) ≤ deg := by
      unfold CMvPolynomial.degreeOf
      apply Finset.sup_le
      intro mono hmono
      exact partialEvalLast_degreeOf_le (n := n + 1) (R := R) (deg := deg)
        (D j) (0 : Fin (n + 1)) p hinput mono (by simpa using hmono)
    have hdegree :=
      congrFun (degreeOf_equiv (p := partialEvalLast (D j) p) (S := R)) (0 : Fin (n + 1))
    rw [hdegree] at hcmv
    exact hcmv
  have hdegree := congrFun (degreeOf_equiv (p := sumOverLast D p) (S := R)) (0 : Fin (n + 1))
  rw [← hdegree] at hEval
  exact (Finset.le_sup (s := (Lawful.monomials (sumOverLast D p)).toFinset)
    (f := fun m => m.degreeOf 0) (by simpa using hmono)).trans hEval

/-- Iterated summation of all but the first variable preserves the degree bound
in variable `0`. -/
theorem sumAllButFirst_degreeOf_zero_le [Nontrivial R] {deg : ℕ} (D : Fin m → R) :
    ∀ (k : ℕ) (p : CMvPolynomial (k + 1) R),
      (∀ mono ∈ Lawful.monomials p, mono.degreeOf 0 ≤ deg) →
      ∀ mono ∈ Lawful.monomials (sumAllButFirst D k p), mono.degreeOf 0 ≤ deg
  | 0, p, hDeg => by
      simpa [sumAllButFirst] using hDeg
  | k + 1, p, hDeg => by
      simpa [sumAllButFirst] using
        sumAllButFirst_degreeOf_zero_le D k
          (sumOverLast D p)
          (sumOverLast_degreeOf_zero_le (n := k) (R := R) (m := m)
            (deg := deg) D p hDeg)

section Univariate

variable [Nontrivial R]

/-- Convert a single-variable multivariate polynomial to a univariate `CPolynomial`. -/
def toUnivariate (p : CMvPolynomial 1 R) : CPolynomial R :=
  eval₂ CPolynomial.CRingHom (fun _ => CPolynomial.X) p

/-- Compute a Sumcheck-style round polynomial from a multivariate polynomial. -/
def roundPoly (D : Fin m → R) (k : ℕ) (p : CMvPolynomial (k + 1) R) : CPolynomial R :=
  toUnivariate (sumAllButFirst D k p)

/-- The univariate bridge agrees with the Mathlib polynomial obtained by
transporting the one-variable computable polynomial through `fromCMvPolynomial`. -/
theorem toUnivariate_toPoly (p : CMvPolynomial 1 R) :
    (toUnivariate p).toPoly =
      MvPolynomial.eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X)
        (fromCMvPolynomial p) := by
  unfold toUnivariate
  have h := MvPolynomial.map_eval₂Hom
    (f := CPolynomial.CRingHom (R := R))
    (g := fun _ : Fin 1 => CPolynomial.X)
    (φ := (CPolynomial.ringEquiv (R := R)).toRingHom)
    (p := fromCMvPolynomial p)
  have hcomp :
      ((CPolynomial.ringEquiv (R := R)).toRingHom).comp
        (CPolynomial.CRingHom (R := R)) = Polynomial.C := by
    ext r n
    rw [RingHom.comp_apply]
    change ((CPolynomial.C r).toPoly).coeff n = (Polynomial.C r).coeff n
    rw [CPolynomial.C_toPoly]
  have hvars :
      (fun i : Fin 1 =>
          (CPolynomial.ringEquiv (R := R)).toRingHom CPolynomial.X) =
        (fun _ : Fin 1 => Polynomial.X) := by
    funext i
    change CPolynomial.X.toPoly = Polynomial.X
    rw [CPolynomial.X_toPoly]
  rw [eval₂_equiv (p := p) (f := CPolynomial.CRingHom (R := R))
    (vals := fun _ : Fin 1 => CPolynomial.X)]
  change (CPolynomial.ringEquiv (R := R)).toRingHom
      (MvPolynomial.eval₂ (CPolynomial.CRingHom (R := R)) (fun _ : Fin 1 => CPolynomial.X)
        (fromCMvPolynomial p)) = _
  rw [hcomp] at h
  rw [hvars] at h
  exact h

/-- `toUnivariate` preserves evaluation at the unique remaining variable. -/
theorem toUnivariate_eval (p : CMvPolynomial 1 R) (x : R) :
    CPolynomial.eval x (toUnivariate p) = p.eval (fun _ : Fin 1 => x) := by
  rw [CPolynomial.eval_toPoly, toUnivariate_toPoly]
  change Polynomial.eval x
      (MvPolynomial.eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X)
        (fromCMvPolynomial p)) = _
  rw [← Polynomial.coe_evalRingHom]
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (Polynomial.evalRingHom x).comp Polynomial.C = RingHom.id R := by
    ext r
    simp
  have hv :
      (⇑(Polynomial.evalRingHom x) ∘ fun _ : Fin 1 => Polynomial.X) =
        (fun _ : Fin 1 => x) := by
    funext i
    simp
  rw [hc, hv]
  exact (eval_equiv (p := p) (vals := fun _ : Fin 1 => x)).symm

/-- The symbolic round polynomial computes the exact remaining-sum function. -/
theorem roundPoly_eval (D : Fin m → R) (k : ℕ) (p : CMvPolynomial (k + 1) R) (x : R) :
    CPolynomial.eval x (roundPoly D k p) =
      (Finset.univ : Finset (Fin k → Fin m)).sum (fun z =>
        p.eval (Fin.cons x (D ∘ z))) := by
  unfold roundPoly
  rw [toUnivariate_eval, sumAllButFirst_eval]

/-- `toUnivariate` preserves degree bounds in the single remaining variable. -/
theorem toUnivariate_natDegree_le {deg : ℕ}
    (p : CMvPolynomial 1 R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.degreeOf 0 ≤ deg) :
    (toUnivariate p).natDegree ≤ deg := by
  rw [CPolynomial.natDegree_toPoly, toUnivariate_toPoly]
  have hfin :
      MvPolynomial.eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X)
          (fromCMvPolynomial p) =
        MvPolynomial.finOneEquiv R (fromCMvPolynomial p) := by
    rw [MvPolynomial.finOneEquiv, AlgEquiv.trans_apply, MvPolynomial.finSuccEquiv_apply]
    symm
    change (Polynomial.mapRingHom (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv.toRingHom)
        (MvPolynomial.eval₂Hom
          (Polynomial.C.comp (MvPolynomial.C : R →+* MvPolynomial (Fin 0) R))
          (fun i : Fin 1 =>
            Fin.cases Polynomial.X (fun k : Fin 0 => Polynomial.C (MvPolynomial.X k)) i)
          (fromCMvPolynomial p)) =
        MvPolynomial.eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X)
          (fromCMvPolynomial p)
    rw [MvPolynomial.map_eval₂Hom]
    have hf :
        (Polynomial.mapRingHom (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv.toRingHom).comp
            (Polynomial.C.comp (MvPolynomial.C : R →+* MvPolynomial (Fin 0) R)) =
          Polynomial.C := by
      ext r n
      simp
    have hg :
        (fun i : Fin 1 =>
            (Polynomial.mapRingHom (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv.toRingHom)
              (Fin.cases Polynomial.X (fun k : Fin 0 => Polynomial.C (MvPolynomial.X k)) i)) =
          (fun _ : Fin 1 => Polynomial.X) := by
      funext i
      fin_cases i
      simp
    rw [hf, hg]
    rfl
  rw [hfin]
  change (Polynomial.map (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingHom
      (MvPolynomial.finSuccEquiv R 0 (fromCMvPolynomial p))).natDegree ≤ deg
  have hinj : Function.Injective
      (fun x => (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv.toRingHom x) := by
    intro a b h
    exact (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv.injective h
  rw [Polynomial.natDegree_map_eq_of_injective hinj]
  rw [MvPolynomial.natDegree_finSuccEquiv]
  have hdegree := congrFun (degreeOf_equiv (p := p) (S := R)) 0
  rw [← hdegree]
  unfold CMvPolynomial.degreeOf
  apply Finset.sup_le
  intro mono hmono
  exact hDeg mono (by simpa using hmono)

/-- The round polynomial has degree at most `deg` when the original polynomial has
degree at most `deg` in variable `0`. -/
theorem roundPoly_natDegree_le {deg : ℕ} (D : Fin m → R) {k : ℕ}
    (p : CMvPolynomial (k + 1) R)
    (hDeg : ∀ mono ∈ Lawful.monomials p, mono.degreeOf 0 ≤ deg) :
    (roundPoly D k p).natDegree ≤ deg := by
  unfold roundPoly
  exact toUnivariate_natDegree_le (R := R) (deg := deg) (sumAllButFirst D k p)
    (sumAllButFirst_degreeOf_zero_le (R := R) (m := m) (deg := deg) D k p hDeg)

end Univariate

end CMvPolynomial

end CPoly
