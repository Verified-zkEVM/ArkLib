/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct

open Polynomial
open Polynomial.Bivariate
open ToRatFunc
open Ideal
open scoped BigOperators

namespace BCIKS20AppendixA

variable {F : Type} [CommRing F] [IsDomain F]

noncomputable def resultantY (P Q : F[X][Y]) : F[X] :=
  Polynomial.resultant P Q

lemma resultantY_def (P Q : F[X][Y]) :
    resultantY P Q = Polynomial.resultant P Q := rfl

noncomputable def specializeX (z : F) : F[X][Y] →+* Polynomial F :=
  Polynomial.mapRingHom (Polynomial.evalRingHom z)

lemma specializeX_apply (z : F) (P : F[X][Y]) :
    specializeX (F := F) z P = Polynomial.map (Polynomial.evalRingHom z) P := rfl

section ResultantLemmas

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)

lemma sylvester_map (p q : R[X]) (m n : ℕ) :
    f.mapMatrix (Polynomial.sylvester p q m n) =
      Polynomial.sylvester (p.map f) (q.map f) m n := by
  classical
  ext i j
  cases' j using Fin.addCases with j1 j1
  · by_cases h' : (j1 : ℕ) ≤ i ∧ i ≤ (j1 : ℕ) + m
    · simp [Polynomial.sylvester, RingHom.mapMatrix, Matrix.map_apply, h', Polynomial.coeff_map]
    · simp [Polynomial.sylvester, RingHom.mapMatrix, Matrix.map_apply, h', Polynomial.coeff_map]
  · by_cases h' : (j1 : ℕ) ≤ i ∧ i ≤ (j1 : ℕ) + n
    · simp [Polynomial.sylvester, RingHom.mapMatrix, Matrix.map_apply, h', Polynomial.coeff_map]
    · simp [Polynomial.sylvester, RingHom.mapMatrix, Matrix.map_apply, h', Polynomial.coeff_map]

lemma resultant_map (p q : R[X]) (m n : ℕ) :
    f (Polynomial.resultant p q m n) =
      Polynomial.resultant (p.map f) (q.map f) m n := by
  classical
  simp [Polynomial.resultant, sylvester_map (f := f) p q m n, RingHom.map_det]

end ResultantLemmas

lemma resultantY_eval (P Q : F[X][Y]) (z : F) :
    (Polynomial.evalRingHom z) (resultantY P Q) =
      Polynomial.resultant (specializeX (F := F) z P) (specializeX (F := F) z Q)
        P.natDegree Q.natDegree := by
  classical
  simpa [resultantY, specializeX_apply, Polynomial.resultant] using
    (resultant_map (f := Polynomial.evalRingHom z) (p := P) (q := Q)
      (m := P.natDegree) (n := Q.natDegree))

section LinearDependence

variable {R : Type} [CommRing R] [IsDomain R]
variable {n : Type} [Fintype n] [DecidableEq n]

lemma not_linearIndependent_cols_of_mulVec_eq_zero
    {A : Matrix n n R} {v : n → R}
    (hv : ∃ i, v i ≠ 0) (hA : A.mulVec v = 0) :
    ¬ LinearIndependent R (fun j => A.transpose j) := by
  classical
  refine (Fintype.not_linearIndependent_iff).2 ?_
  refine ⟨v, ?_, hv⟩
  ext i
  have hAi : (A.mulVec v) i = 0 := by simpa using congrArg (fun w => w i) hA
  have hsum : ∑ j, A i j * v j = 0 := by
    simpa [Matrix.mulVec] using hAi
  -- swap the factors in the sum
  simpa [Matrix.transpose_apply, mul_comm] using hsum

end LinearDependence

section RootCount

variable {F : Type} [Field F] [DecidableEq F]

lemma eq_zero_of_card_lt_roots {p : F[X]} {s : Finset F}
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

end RootCount

section DegreeBounds

variable {F : Type} [CommRing F]

lemma natDegree_coeff_le_degreeX (f : F[X][Y]) (i : ℕ) :
    (f.coeff i).natDegree ≤ Bivariate.degreeX f := by
  classical
  unfold Bivariate.degreeX
  by_cases hi : i ∈ f.support
  · exact Finset.le_sup (s := f.support) (f := fun n => (f.coeff n).natDegree) hi
  · have hcoeff : f.coeff i = 0 := by
      exact (Polynomial.notMem_support_iff.mp hi)
    simp [hcoeff]

lemma natDegree_sylvester_entry_le (P Q : F[X][Y]) (m n : ℕ)
    (i j : Fin (n + m)) :
    (Polynomial.sylvester P Q m n i j).natDegree ≤
      max (Bivariate.degreeX P) (Bivariate.degreeX Q) := by
  classical
  cases' j using Fin.addCases with j1 j1
  · by_cases h' : (i : ℕ) ∈ Set.Icc (j1 : ℕ) (j1 + m)
    · have h'' : (j1 : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j1 : ℕ) + m := by
        simpa [Set.mem_Icc] using h'
      have hentry :
          (Polynomial.sylvester P Q m n i (Fin.castAdd m j1)).natDegree =
            (P.coeff (i - j1)).natDegree := by
            simp [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, h'']
      have hdeg : (P.coeff (i - j1)).natDegree ≤ Bivariate.degreeX P :=
        natDegree_coeff_le_degreeX (f := P) (i := i - j1)
      exact le_trans (by simpa [hentry]) (le_max_left _ _)
    · have hentry :
          (Polynomial.sylvester P Q m n i (Fin.castAdd m j1)).natDegree = 0 := by
            have h'' : ¬ ((j1 : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j1 : ℕ) + m) := by
              simpa [Set.mem_Icc] using h'
            simp [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, h'']
      simpa [hentry] using (Nat.zero_le (max (Bivariate.degreeX P) (Bivariate.degreeX Q)))
  · by_cases h' : (i : ℕ) ∈ Set.Icc (j1 : ℕ) (j1 + n)
    · have h'' : (j1 : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j1 : ℕ) + n := by
        simpa [Set.mem_Icc] using h'
      have hentry :
          (Polynomial.sylvester P Q m n i (Fin.natAdd n j1)).natDegree =
            (Q.coeff (i - j1)).natDegree := by
            simp [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, h'']
      have hdeg : (Q.coeff (i - j1)).natDegree ≤ Bivariate.degreeX Q :=
        natDegree_coeff_le_degreeX (f := Q) (i := i - j1)
      exact le_trans (by simpa [hentry]) (le_max_right _ _)
    · have hentry :
          (Polynomial.sylvester P Q m n i (Fin.natAdd n j1)).natDegree = 0 := by
            have h'' : ¬ ((j1 : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) ≤ (j1 : ℕ) + n) := by
              simpa [Set.mem_Icc] using h'
            simp [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, h'']
      simpa [hentry] using (Nat.zero_le (max (Bivariate.degreeX P) (Bivariate.degreeX Q)))

lemma natDegree_det_le_of_entries {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n F[X]) (d : ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ d) :
    (Matrix.det A).natDegree ≤ Fintype.card n * d := by
  classical
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro g
  have hsmul :
      (Polynomial.natDegree (Equiv.Perm.sign g • ∏ i, A (g i) i)) ≤
        Polynomial.natDegree (∏ i, A (g i) i) := by
      exact Polynomial.natDegree_smul_le _ _
  have hprod :
      Polynomial.natDegree (∏ i, A (g i) i) ≤ ∑ i, (A (g i) i).natDegree := by
      simpa using
        (Polynomial.natDegree_prod_le (s := (Finset.univ : Finset n))
          (f := fun i => A (g i) i))
  have hsum :
      (∑ i, (A (g i) i).natDegree) ≤ (Fintype.card n) * d := by
      have h' : ∀ i ∈ (Finset.univ : Finset n), (A (g i) i).natDegree ≤ d := by
        intro i hi
        exact h (g i) i
      simpa [Finset.card_univ] using (Finset.sum_le_card_nsmul _ _ d h')
  exact hsmul.trans (hprod.trans hsum)

lemma natDegree_resultantY_le_max (P Q : F[X][Y]) :
    (resultantY P Q).natDegree ≤
      (P.natDegree + Q.natDegree) * max (Bivariate.degreeX P) (Bivariate.degreeX Q) := by
  classical
  -- unfold resultantY and use the Sylvester matrix bound
  simp [resultantY, Polynomial.resultant]
  have hentry :
      ∀ i j : Fin (Q.natDegree + P.natDegree),
        (Polynomial.sylvester P Q P.natDegree Q.natDegree i j).natDegree ≤
          max (Bivariate.degreeX P) (Bivariate.degreeX Q) := by
        intro i j
        simpa [Nat.add_comm] using
          (natDegree_sylvester_entry_le (P := P) (Q := Q)
            (m := P.natDegree) (n := Q.natDegree) (i := i) (j := j))
  simpa [Fintype.card_fin, Nat.add_comm] using
    (natDegree_det_le_of_entries
      (A := Polynomial.sylvester P Q P.natDegree Q.natDegree)
      (d := max (Bivariate.degreeX P) (Bivariate.degreeX Q)) hentry)

section WeightedResultant

lemma sum_univ_add_castAdd_natAdd {a b : ℕ} (f : Fin (a + b) → ℕ) :
    (∑ i : Fin (a + b), f i) =
      (∑ i : Fin a, f (Fin.castAdd b i)) + (∑ i : Fin b, f (Fin.natAdd a i)) := by
  simpa using (Fin.sum_univ_add (a := a) (b := b) (f := f))

lemma sum_perm_apply_eq_sum {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Fin n → ℕ) :
    (∑ i : Fin n, f (σ i)) = ∑ i : Fin n, f i := by
  simpa using (Equiv.sum_comp σ f)

lemma sum_sigma_sub_eq_mul {n m : ℕ} (σ : Equiv.Perm (Fin (n + m)))
    (hσ₁ : ∀ j : Fin n, (j : ℕ) ≤ σ (Fin.castAdd m j))
    (hσ₂ : ∀ j : Fin m, (j : ℕ) ≤ σ (Fin.natAdd n j)) :
    (∑ j : Fin n, ((σ (Fin.castAdd m j) : ℕ) - (j : ℕ))) +
        (∑ j : Fin m, ((σ (Fin.natAdd n j) : ℕ) - (j : ℕ))) = n * m := by
  classical
  -- rewrite the sum of σ in terms of the subtracted sums
  have hkf :
      (∑ j : Fin n, (σ (Fin.castAdd m j) : ℕ)) =
        (∑ j : Fin n, ((σ (Fin.castAdd m j) : ℕ) - (j : ℕ))) +
          (∑ j : Fin n, (j : ℕ)) := by
    calc
      (∑ j : Fin n, (σ (Fin.castAdd m j) : ℕ)) =
          ∑ j : Fin n,
            ((σ (Fin.castAdd m j) : ℕ) - (j : ℕ) + (j : ℕ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              exact (Nat.sub_add_cancel (hσ₁ j)).symm
      _ = (∑ j : Fin n, ((σ (Fin.castAdd m j) : ℕ) - (j : ℕ))) +
            (∑ j : Fin n, (j : ℕ)) := by
              simp [Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc]
  have hkg :
      (∑ j : Fin m, (σ (Fin.natAdd n j) : ℕ)) =
        (∑ j : Fin m, ((σ (Fin.natAdd n j) : ℕ) - (j : ℕ))) +
          (∑ j : Fin m, (j : ℕ)) := by
    calc
      (∑ j : Fin m, (σ (Fin.natAdd n j) : ℕ)) =
          ∑ j : Fin m,
            ((σ (Fin.natAdd n j) : ℕ) - (j : ℕ) + (j : ℕ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              exact (Nat.sub_add_cancel (hσ₂ j)).symm
      _ = (∑ j : Fin m, ((σ (Fin.natAdd n j) : ℕ) - (j : ℕ))) +
            (∑ j : Fin m, (j : ℕ)) := by
              simp [Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc]
  -- split the sum of σ and replace by the sum of indices
  have hsum_sigma :
      (∑ j : Fin n, (σ (Fin.castAdd m j) : ℕ)) +
          (∑ j : Fin m, (σ (Fin.natAdd n j) : ℕ)) =
        ∑ i : Fin (n + m), (i : ℕ) := by
    have hsplit :
        (∑ i : Fin (n + m), (σ i : ℕ)) =
          (∑ j : Fin n, (σ (Fin.castAdd m j) : ℕ)) +
            (∑ j : Fin m, (σ (Fin.natAdd n j) : ℕ)) := by
          simpa using
            (sum_univ_add_castAdd_natAdd (a := n) (b := m) (f := fun i => (σ i : ℕ)))
    have hperm : (∑ i : Fin (n + m), (σ i : ℕ)) = ∑ i : Fin (n + m), (i : ℕ) := by
      simpa using (sum_perm_apply_eq_sum (σ := σ) (f := fun i => (i : ℕ)))
    exact by simpa [hsplit] using hperm
  -- compute the sum of indices in `Fin (n+m)`
  have hsum_id :
      (∑ i : Fin (n + m), (i : ℕ)) =
        (∑ j : Fin n, (j : ℕ)) + (∑ j : Fin m, (j : ℕ)) + n * m := by
    have hsplit :
        (∑ i : Fin (n + m), (i : ℕ)) =
          (∑ j : Fin n, (j : ℕ)) + (∑ j : Fin m, (n + (j : ℕ))) := by
        simpa using
          (sum_univ_add_castAdd_natAdd (a := n) (b := m) (f := fun i => (i : ℕ)))
    calc
      (∑ i : Fin (n + m), (i : ℕ))
          = (∑ j : Fin n, (j : ℕ)) + (∑ j : Fin m, (n + (j : ℕ))) := hsplit
      _ = (∑ j : Fin n, (j : ℕ)) +
            ((∑ _j : Fin m, n) + (∑ j : Fin m, (j : ℕ))) := by
              simp [Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc]
      _ = (∑ j : Fin n, (j : ℕ)) + (∑ j : Fin m, (j : ℕ)) + n * m := by
              simp [Fin.sum_const, add_comm, add_left_comm, add_assoc, Nat.mul_comm]
  -- combine and cancel
  have hsum_sigma' :
      (∑ j : Fin n, ((σ (Fin.castAdd m j) : ℕ) - (j : ℕ))) +
          (∑ j : Fin m, ((σ (Fin.natAdd n j) : ℕ) - (j : ℕ))) +
          ((∑ j : Fin n, (j : ℕ)) + (∑ j : Fin m, (j : ℕ))) =
        ∑ i : Fin (n + m), (i : ℕ) := by
    calc
      (∑ j : Fin n, ((σ (Fin.castAdd m j) : ℕ) - (j : ℕ))) +
          (∑ j : Fin m, ((σ (Fin.natAdd n j) : ℕ) - (j : ℕ))) +
          ((∑ j : Fin n, (j : ℕ)) + (∑ j : Fin m, (j : ℕ))) =
        ((∑ j : Fin n, ((σ (Fin.castAdd m j) : ℕ) - (j : ℕ))) + (∑ j : Fin n, (j : ℕ))) +
          ((∑ j : Fin m, ((σ (Fin.natAdd n j) : ℕ) - (j : ℕ))) + (∑ j : Fin m, (j : ℕ))) := by
          ac_rfl
      _ = (∑ j : Fin n, (σ (Fin.castAdd m j) : ℕ)) +
            (∑ j : Fin m, (σ (Fin.natAdd n j) : ℕ)) := by
          simp [hkf, hkg]
      _ = ∑ i : Fin (n + m), (i : ℕ) := hsum_sigma
  -- cancel the common sum
  have hcancel :
      (∑ j : Fin n, ((σ (Fin.castAdd m j) : ℕ) - (j : ℕ))) +
          (∑ j : Fin m, ((σ (Fin.natAdd n j) : ℕ) - (j : ℕ))) =
        n * m := by
    -- rewrite hsum_sigma' using hsum_id
    have := hsum_sigma'.trans hsum_id
    -- cancel the common summand
    have h' :
        (∑ j : Fin n, (j : ℕ)) + (∑ j : Fin m, (j : ℕ)) +
            ((∑ j : Fin n, ((σ (Fin.castAdd m j) : ℕ) - (j : ℕ))) +
              (∑ j : Fin m, ((σ (Fin.natAdd n j) : ℕ) - (j : ℕ)))) =
          (∑ j : Fin n, (j : ℕ)) + (∑ j : Fin m, (j : ℕ)) + n * m := by
      simpa [add_assoc, add_left_comm, add_comm] using this
    exact (Nat.add_left_cancel h')
  exact hcancel

lemma natDegree_resultantY_le_weight
    {F : Type} [CommRing F]
    {f g : F[X][Y]} (A B : ℕ)
    (hB : A * g.natDegree ≤ B)
    (hf : ∀ k, (f.coeff k).natDegree ≤ A * (f.natDegree - k))
    (hg : ∀ k, (g.coeff k).natDegree ≤ B - A * k) :
    (resultantY f g).natDegree ≤ f.natDegree * B := by
  classical
  -- expand determinant definition
  simp [resultantY, Polynomial.resultant, Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro σ
  -- bound the degree of each product term
  have hterm :
      (Polynomial.natDegree (∏ i : Fin (g.natDegree + f.natDegree),
          Polynomial.sylvester f g f.natDegree g.natDegree (σ i) i)) ≤
        f.natDegree * B := by
    -- split into two blocks of columns
    have hsplit :
        (∑ i : Fin (g.natDegree + f.natDegree),
            (Polynomial.sylvester f g f.natDegree g.natDegree (σ i) i).natDegree) =
          (∑ j : Fin g.natDegree,
              (Polynomial.sylvester f g f.natDegree g.natDegree
                  (σ (Fin.castAdd f.natDegree j)) (Fin.castAdd f.natDegree j)).natDegree) +
          (∑ j : Fin f.natDegree,
              (Polynomial.sylvester f g f.natDegree g.natDegree
                  (σ (Fin.natAdd g.natDegree j)) (Fin.natAdd g.natDegree j)).natDegree) := by
        simpa using
          (sum_univ_add_castAdd_natAdd
            (a := g.natDegree) (b := f.natDegree)
            (f := fun i =>
              (Polynomial.sylvester f g f.natDegree g.natDegree (σ i) i).natDegree))
    -- apply `natDegree_prod_le`
    have hprod :
        Polynomial.natDegree (∏ i : Fin (g.natDegree + f.natDegree),
            Polynomial.sylvester f g f.natDegree g.natDegree (σ i) i) ≤
          ∑ i : Fin (g.natDegree + f.natDegree),
            (Polynomial.sylvester f g f.natDegree g.natDegree (σ i) i).natDegree := by
      simpa using
        (Polynomial.natDegree_prod_le
          (s := (Finset.univ : Finset (Fin (g.natDegree + f.natDegree))))
          (f := fun i =>
            Polynomial.sylvester f g f.natDegree g.natDegree (σ i) i))
    -- bound the sum of degrees using the coefficient bounds
    have hdeg_f :
        ∀ j : Fin g.natDegree,
          (Polynomial.sylvester f g f.natDegree g.natDegree
              (σ (Fin.castAdd f.natDegree j)) (Fin.castAdd f.natDegree j)).natDegree ≤
            A * (f.natDegree -
                (((σ (Fin.castAdd f.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) -
                  (j : ℕ))) := by
      intro j
      let k : ℕ :=
        ((σ (Fin.castAdd f.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) - (j : ℕ)
      by_cases h' :
          ((σ (Fin.castAdd f.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ∈
            Set.Icc (j : ℕ) (j + f.natDegree)
      · -- entry is `f.coeff`
        have h'' :
            (j : ℕ) ≤
                ((σ (Fin.castAdd f.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ∧
              ((σ (Fin.castAdd f.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ≤
                (j : ℕ) + f.natDegree := by
          simpa [Set.mem_Icc] using h'
        have hentry :
            Polynomial.sylvester f g f.natDegree g.natDegree
                (σ (Fin.castAdd f.natDegree j)) (Fin.castAdd f.natDegree j) =
              f.coeff k := by
            simp [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, h'', k]
        simpa [hentry, k] using (hf k)
      · -- entry is zero
        have h'' :
            ¬((j : ℕ) ≤
                ((σ (Fin.castAdd f.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ∧
              ((σ (Fin.castAdd f.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ≤
                (j : ℕ) + f.natDegree) := by
          simpa [Set.mem_Icc] using h'
        have hentry :
            Polynomial.sylvester f g f.natDegree g.natDegree
                (σ (Fin.castAdd f.natDegree j)) (Fin.castAdd f.natDegree j) = 0 := by
          simp [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, h'', k]
        simpa [hentry, k] using (Nat.zero_le (A * (f.natDegree - k)))
    have hdeg_g :
        ∀ j : Fin f.natDegree,
          (Polynomial.sylvester f g f.natDegree g.natDegree
              (σ (Fin.natAdd g.natDegree j)) (Fin.natAdd g.natDegree j)).natDegree ≤
            B - A *
              (((σ (Fin.natAdd g.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) -
                (j : ℕ)) := by
      intro j
      let k : ℕ :=
        ((σ (Fin.natAdd g.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) - (j : ℕ)
      by_cases h' :
          ((σ (Fin.natAdd g.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ∈
            Set.Icc (j : ℕ) (j + g.natDegree)
      · -- entry is `g.coeff`
        have h'' :
            (j : ℕ) ≤
                ((σ (Fin.natAdd g.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ∧
              ((σ (Fin.natAdd g.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ≤
                (j : ℕ) + g.natDegree := by
          simpa [Set.mem_Icc] using h'
        have hentry :
            Polynomial.sylvester f g f.natDegree g.natDegree
                (σ (Fin.natAdd g.natDegree j)) (Fin.natAdd g.natDegree j) =
              g.coeff k := by
            simp [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, h'', k]
        simpa [hentry, k] using (hg k)
      · -- entry is zero
        have h'' :
            ¬((j : ℕ) ≤
                ((σ (Fin.natAdd g.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ∧
              ((σ (Fin.natAdd g.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ≤
                (j : ℕ) + g.natDegree) := by
          simpa [Set.mem_Icc] using h'
        have hentry :
            Polynomial.sylvester f g f.natDegree g.natDegree
                (σ (Fin.natAdd g.natDegree j)) (Fin.natAdd g.natDegree j) = 0 := by
          simp [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, h'', k]
        simpa [hentry, k] using (Nat.zero_le (B - A * k))
    -- if any entry is zero, the product is zero and the bound holds
    by_cases hzero :
        ∃ i : Fin (g.natDegree + f.natDegree),
          Polynomial.sylvester f g f.natDegree g.natDegree (σ i) i = 0
    · rcases hzero with ⟨i, hi⟩
      have hprod0 :
          (∏ i : Fin (g.natDegree + f.natDegree),
              Polynomial.sylvester f g f.natDegree g.natDegree (σ i) i) = 0 := by
        simpa using
          (Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin (g.natDegree + f.natDegree))))
            (i := i) (f := fun i =>
              Polynomial.sylvester f g f.natDegree g.natDegree (σ i) i) (by simpa) hi)
      simpa [hprod0]
    · -- otherwise all entries are nonzero and satisfy the Icc conditions
      have hIcc_f :
          ∀ j : Fin g.natDegree,
            ((σ (Fin.castAdd f.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ∈
              Set.Icc (j : ℕ) (j + f.natDegree) := by
        intro j
        by_contra h'
        apply hzero
        refine ⟨Fin.castAdd f.natDegree j, ?_⟩
        have h'' :
            ¬((j : ℕ) ≤
                ((σ (Fin.castAdd f.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ∧
              ((σ (Fin.castAdd f.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ≤
                (j : ℕ) + f.natDegree) := by
          simpa [Set.mem_Icc] using h'
        simp [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, h'']
      have hIcc_g :
          ∀ j : Fin f.natDegree,
            ((σ (Fin.natAdd g.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ∈
              Set.Icc (j : ℕ) (j + g.natDegree) := by
        intro j
        by_contra h'
        apply hzero
        refine ⟨Fin.natAdd g.natDegree j, ?_⟩
        have h'' :
            ¬((j : ℕ) ≤
                ((σ (Fin.natAdd g.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ∧
              ((σ (Fin.natAdd g.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ≤
                (j : ℕ) + g.natDegree) := by
          simpa [Set.mem_Icc] using h'
        simp [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, h'']
      -- shorthand for the shifts
      let kf : Fin g.natDegree → ℕ := fun j =>
        ((σ (Fin.castAdd f.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) - (j : ℕ)
      let kg : Fin f.natDegree → ℕ := fun j =>
        ((σ (Fin.natAdd g.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) - (j : ℕ)
      have hsum_k :
          (∑ j : Fin g.natDegree, kf j) + (∑ j : Fin f.natDegree, kg j) =
            g.natDegree * f.natDegree := by
        have hsum :=
          (sum_sigma_sub_eq_mul (σ := σ)
            (hσ₁ := fun j => (hIcc_f j).1)
            (hσ₂ := fun j => (hIcc_g j).1))
        simpa [kf, kg] using hsum
      have hsum_bound :
          (∑ j : Fin g.natDegree,
              (Polynomial.sylvester f g f.natDegree g.natDegree
                  (σ (Fin.castAdd f.natDegree j)) (Fin.castAdd f.natDegree j)).natDegree) +
            (∑ j : Fin f.natDegree,
              (Polynomial.sylvester f g f.natDegree g.natDegree
                  (σ (Fin.natAdd g.natDegree j)) (Fin.natAdd g.natDegree j)).natDegree) ≤
            f.natDegree * B := by
        -- use the coefficient bounds and the sum identity
        have hf_sum :
            (∑ j : Fin g.natDegree,
                (Polynomial.sylvester f g f.natDegree g.natDegree
                    (σ (Fin.castAdd f.natDegree j)) (Fin.castAdd f.natDegree j)).natDegree) ≤
              ∑ j : Fin g.natDegree,
                A * (f.natDegree - kf j) := by
          exact Finset.sum_le_sum fun j hj => hdeg_f j
        have hg_sum :
            (∑ j : Fin f.natDegree,
                (Polynomial.sylvester f g f.natDegree g.natDegree
                    (σ (Fin.natAdd g.natDegree j)) (Fin.natAdd g.natDegree j)).natDegree) ≤
              ∑ j : Fin f.natDegree,
                (B - A * kg j) := by
          exact Finset.sum_le_sum fun j hj => hdeg_g j
        -- combine and use the sum of k's
        refine le_trans (add_le_add hf_sum hg_sum) ?_
        have hkf_le : ∀ j : Fin g.natDegree, kf j ≤ f.natDegree := by
          intro j
          have hle :
              ((σ (Fin.castAdd f.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ≤
                (j : ℕ) + f.natDegree := (hIcc_f j).2
          have hle' :
              ((σ (Fin.castAdd f.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) -
                  (j : ℕ) ≤
                ((j : ℕ) + f.natDegree) - (j : ℕ) :=
            Nat.sub_le_sub_right hle (j : ℕ)
          simpa [kf, Nat.add_sub_cancel_left] using hle'
        have hkg_le : ∀ j : Fin f.natDegree, kg j ≤ g.natDegree := by
          intro j
          have hle :
              ((σ (Fin.natAdd g.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) ≤
                (j : ℕ) + g.natDegree := (hIcc_g j).2
          have hle' :
              ((σ (Fin.natAdd g.natDegree j) : Fin (g.natDegree + f.natDegree)) : ℕ) -
                  (j : ℕ) ≤
                ((j : ℕ) + g.natDegree) - (j : ℕ) :=
            Nat.sub_le_sub_right hle (j : ℕ)
          simpa [kg, Nat.add_sub_cancel_left] using hle'
        have hAkg_leB : ∀ j : Fin f.natDegree, A * kg j ≤ B := by
          intro j
          have hle : A * kg j ≤ A * g.natDegree :=
            Nat.mul_le_mul_left _ (hkg_le j)
          exact le_trans hle hB
        have hsum_f :
            (∑ j : Fin g.natDegree, A * (f.natDegree - kf j)) =
              A * (g.natDegree * f.natDegree - ∑ j : Fin g.natDegree, kf j) := by
          have hmul_sum :
              (∑ j : Fin g.natDegree, A * (f.natDegree - kf j)) =
                A * ∑ j : Fin g.natDegree, (f.natDegree - kf j) := by
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Fin g.natDegree)))
                (f := fun j => f.natDegree - kf j) (a := A)).symm
          have hle :
              ∀ j ∈ (Finset.univ : Finset (Fin g.natDegree)), kf j ≤ f.natDegree := by
            intro j hj
            exact hkf_le j
          have hsum_tsub :
              (∑ j : Fin g.natDegree, (f.natDegree - kf j)) =
                (∑ j : Fin g.natDegree, f.natDegree) -
                  ∑ j : Fin g.natDegree, kf j := by
            simpa using
              (Finset.sum_tsub_distrib (s := (Finset.univ : Finset (Fin g.natDegree)))
                (f := fun _ => f.natDegree) (g := fun j => kf j) hle)
          have hsum_const :
              (∑ j : Fin g.natDegree, f.natDegree) = g.natDegree * f.natDegree := by
            simpa using (Fin.sum_const (n := g.natDegree) (a := f.natDegree))
          calc
            ∑ j : Fin g.natDegree, A * (f.natDegree - kf j)
                = A * ∑ j : Fin g.natDegree, (f.natDegree - kf j) := hmul_sum
            _ = A * ((∑ j : Fin g.natDegree, f.natDegree) -
                      ∑ j : Fin g.natDegree, kf j) := by
                  simp [hsum_tsub]
            _ = A * (g.natDegree * f.natDegree -
                      ∑ j : Fin g.natDegree, kf j) := by
                  simp [hsum_const]
        have hsum_kg :
            (∑ j : Fin f.natDegree, kg j) =
              g.natDegree * f.natDegree - ∑ j : Fin g.natDegree, kf j := by
          have h' :
              (∑ j : Fin g.natDegree, kf j) +
                  (∑ j : Fin f.natDegree, kg j) -
                  (∑ j : Fin g.natDegree, kf j) =
                ∑ j : Fin f.natDegree, kg j := by
            simpa using
              (Nat.add_sub_cancel_left (∑ j : Fin g.natDegree, kf j)
                (∑ j : Fin f.natDegree, kg j))
          calc
            ∑ j : Fin f.natDegree, kg j =
                (∑ j : Fin g.natDegree, kf j) +
                  (∑ j : Fin f.natDegree, kg j) -
                  (∑ j : Fin g.natDegree, kf j) := by
              simpa [h']
            _ = g.natDegree * f.natDegree - ∑ j : Fin g.natDegree, kf j := by
              simpa [hsum_k]
        have hsum_f' :
            (∑ j : Fin g.natDegree, A * (f.natDegree - kf j)) =
              A * ∑ j : Fin f.natDegree, kg j := by
          simpa [hsum_kg] using hsum_f
        have hsum_g :
            (∑ j : Fin f.natDegree, (B - A * kg j)) =
              f.natDegree * B - ∑ j : Fin f.natDegree, A * kg j := by
          have hle :
              ∀ j ∈ (Finset.univ : Finset (Fin f.natDegree)), A * kg j ≤ B := by
            intro j hj
            exact hAkg_leB j
          have hsum_const :
              (∑ j : Fin f.natDegree, B) = f.natDegree * B := by
            simpa using (Fin.sum_const (n := f.natDegree) (a := B))
          calc
            ∑ j : Fin f.natDegree, (B - A * kg j) =
                (∑ j : Fin f.natDegree, B) -
                  ∑ j : Fin f.natDegree, A * kg j := by
              simpa using
                (Finset.sum_tsub_distrib (s := (Finset.univ : Finset (Fin f.natDegree)))
                  (f := fun _ => B) (g := fun j => A * kg j) hle)
            _ = f.natDegree * B - ∑ j : Fin f.natDegree, A * kg j := by
              simp [hsum_const]
        have hmul_kg :
            (∑ j : Fin f.natDegree, A * kg j) = A * ∑ j : Fin f.natDegree, kg j := by
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin f.natDegree)))
              (f := fun j => kg j) (a := A)).symm
        have hsum_g' :
            (∑ j : Fin f.natDegree, (B - A * kg j)) =
              f.natDegree * B - A * ∑ j : Fin f.natDegree, kg j := by
          simpa [hmul_kg] using hsum_g
        have hle_kg : A * ∑ j : Fin f.natDegree, kg j ≤ f.natDegree * B := by
          have hsum_le :
              (∑ j : Fin f.natDegree, A * kg j) ≤ f.natDegree * B := by
            have h' :
                ∀ j ∈ (Finset.univ : Finset (Fin f.natDegree)), A * kg j ≤ B := by
              intro j hj
              exact hAkg_leB j
            simpa [Finset.card_univ] using
              (Finset.sum_le_card_nsmul _ _ B h')
          simpa [hmul_kg] using hsum_le
        have hsum_eq :
            (∑ j : Fin g.natDegree, A * (f.natDegree - kf j)) +
                (∑ j : Fin f.natDegree, (B - A * kg j)) =
              f.natDegree * B := by
          calc
            (∑ j : Fin g.natDegree, A * (f.natDegree - kf j)) +
                (∑ j : Fin f.natDegree, (B - A * kg j)) =
                A * ∑ j : Fin f.natDegree, kg j +
                  (f.natDegree * B - A * ∑ j : Fin f.natDegree, kg j) := by
              simp [hsum_f', hsum_g']
            _ = f.natDegree * B := by
              simpa using (Nat.add_sub_of_le hle_kg)
        exact le_of_eq hsum_eq
      -- conclude
      exact (hprod.trans (by simpa [hsplit] using hsum_bound))
  -- bound the natDegree of the term after the sign
  have hsign :
      (Polynomial.natDegree (Equiv.Perm.sign σ •
          ∏ i : Fin (g.natDegree + f.natDegree),
            Polynomial.sylvester f g f.natDegree g.natDegree (σ i) i)) ≤
        f.natDegree * B := by
    exact (Polynomial.natDegree_smul_le _ _).trans hterm
  exact hsign

end WeightedResultant

end DegreeBounds


section SylvesterKernel

variable {R : Type} [CommRing R] [IsDomain R]

lemma coeff_eq_zero_of_add_lt {p : R[X]} {x i : ℕ} (hx : x ≤ i) (h : x + p.natDegree < i) :
    p.coeff (i - x) = 0 := by
  have h' : p.natDegree < i - x := by
    have : x + p.natDegree < x + (i - x) := by
      simpa [Nat.add_sub_of_le hx] using h
    exact (Nat.add_lt_add_iff_left).1 this
  exact coeff_eq_zero_of_natDegree_lt h'

lemma castAdd_le_iff {m n : ℕ} {i : Fin m} {j : Fin (m + n)} :
    Fin.castAdd n i ≤ j ↔ (i : ℕ) ≤ j := by
  exact (Fin.le_def)

lemma natAdd_le_iff {m n : ℕ} {i : Fin n} {j : Fin (m + n)} :
    Fin.natAdd m i ≤ j ↔ m + (i : ℕ) ≤ j := by
  exact (Fin.le_def)

lemma sum_range_if_le (n k : ℕ) (f : ℕ → R) :
    Finset.sum (Finset.range n) (fun j => if j ≤ k then f j else 0) =
      Finset.sum (Finset.range (Nat.min n (k + 1))) f := by
  classical
  induction n with
  | zero =>
      simp
  | succ n ih =>
      by_cases hnk : n.succ ≤ k + 1
      · have hnkle : n ≤ k := (Nat.succ_le_succ_iff.mp hnk)
        have hmin : Nat.min n.succ (k + 1) = n.succ := Nat.min_eq_left hnk
        have hmin' : Nat.min n (k + 1) = n :=
          Nat.min_eq_left (Nat.le_trans hnkle (Nat.le_succ k))
        simp [Finset.sum_range_succ, ih, hmin', hnkle]
      · have hk1_le_n : k + 1 ≤ n := by
          exact (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hnk))
        have hmin : Nat.min n.succ (k + 1) = k + 1 :=
          Nat.min_eq_right (Nat.le_trans hk1_le_n (Nat.le_succ n))
        have hmin' : Nat.min n (k + 1) = k + 1 := Nat.min_eq_right hk1_le_n
        have hnk' : ¬ n ≤ k := by
          exact Nat.not_le.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk1_le_n)
        simp [Finset.sum_range_succ, ih, hmin, hmin', hnk']

lemma sum_range_add_eq_sum_range_of_forall_ge (f : ℕ → R) (n t : ℕ)
    (h : ∀ j ≥ n, f j = 0) :
    Finset.sum (Finset.range (n + t)) f = Finset.sum (Finset.range n) f := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      have hzero : f (n + t) = 0 := h (n + t) (Nat.le_add_right n t)
      calc
        Finset.sum (Finset.range (n + t.succ)) f
            = Finset.sum (Finset.range (n + t)) f + f (n + t) := by
                simpa [Nat.add_assoc] using (Finset.sum_range_succ (f := f) (n + t))
        _ = Finset.sum (Finset.range (n + t)) f := by simp [hzero]
        _ = Finset.sum (Finset.range n) f := ih

noncomputable def coeffVec (n : ℕ) (p : R[X]) : Fin n → R := fun i => p.coeff i

noncomputable def joinCoeffVec (m n : ℕ) (q p : R[X]) : Fin (n + m) → R :=
  fun j => j.addCases (fun j1 => q.coeff j1) (fun j1 => p.coeff j1)

noncomputable def polyOfVec (n : ℕ) (v : Fin n → R) : R[X] :=
  ∑ i : Fin n, Polynomial.monomial (i : ℕ) (v i)

lemma coeff_polyOfVec_lt {n : ℕ} (v : Fin n → R) {i : ℕ} (hi : i < n) :
    (polyOfVec n v).coeff i = v ⟨i, hi⟩ := by
  classical
  have hsum :
      (polyOfVec n v).coeff i =
        ∑ j : Fin n, (if (j : ℕ) = i then v j else 0) := by
    simp [polyOfVec, Polynomial.coeff_sum, Polynomial.coeff_monomial]
  have hsingle :
      (∑ j : Fin n, (if (j : ℕ) = i then v j else 0)) = v ⟨i, hi⟩ := by
    classical
    have hzero : ∀ j : Fin n, j ≠ ⟨i, hi⟩ → (if (j : ℕ) = i then v j else 0) = 0 := by
      intro j hj
      have hne : (j : ℕ) ≠ i := by
        intro h
        apply hj
        exact Fin.ext (by simpa using h)
      simp [hne]
    have hmem : (⟨i, hi⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := by simp
    have hsingle' :=
      (Finset.sum_eq_single_of_mem (s := (Finset.univ : Finset (Fin n)))
        (a := ⟨i, hi⟩) hmem (by intro j hj hne; exact hzero j hne))
    simpa using hsingle'
  simpa [hsum] using hsingle

lemma coeff_polyOfVec_ge {n : ℕ} (v : Fin n → R) {i : ℕ} (hi : n ≤ i) :
    (polyOfVec n v).coeff i = 0 := by
  classical
  have hne : ∀ j : Fin n, (j : ℕ) ≠ i := by
    intro j
    exact ne_of_lt (lt_of_lt_of_le j.is_lt hi)
  simp [polyOfVec, Polynomial.coeff_sum, Polynomial.coeff_monomial, hne]

lemma natDegree_polyOfVec_lt {n : ℕ} (v : Fin n → R) (hn : n ≠ 0) :
    (polyOfVec n v).natDegree < n := by
  classical
  have hle : (polyOfVec n v).natDegree ≤ n - 1 := by
    apply (Polynomial.natDegree_le_iff_coeff_eq_zero).2
    intro N hN
    have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hN' : n ≤ N := by
      have : n - 1 + 1 ≤ N := (Nat.succ_le_iff).2 hN
      have hEq : n - 1 + 1 = n := by
        exact Nat.sub_add_cancel (Nat.succ_le_iff.mp hpos)
      simpa [hEq] using this
    exact coeff_polyOfVec_ge (v := v) hN'
  have hlt : n - 1 < n := Nat.sub_lt (Nat.pos_of_ne_zero hn) (Nat.succ_pos 0)
  exact lt_of_le_of_lt hle hlt

lemma joinCoeffVec_polyOfVec {m n : ℕ} (v : Fin (n + m) → R) :
    joinCoeffVec (m := m) (n := n)
        (polyOfVec n (fun i => v (Fin.castAdd m i)))
        (polyOfVec m (fun i => v (Fin.natAdd n i))) = v := by
  funext j
  cases' j using Fin.addCases with j1 j1
  · have hj : (j1 : ℕ) < n := j1.is_lt
    simp [joinCoeffVec, coeff_polyOfVec_lt, hj]
  · have hj : (j1 : ℕ) < m := j1.is_lt
    simp [joinCoeffVec, coeff_polyOfVec_lt, hj]


lemma sylvester_mulVec_eq_coeff_add
    (f g p q : R[X]) (hp : p.natDegree < f.natDegree) (hq : q.natDegree < g.natDegree) :
    (Polynomial.sylvester f g f.natDegree g.natDegree).mulVec
        (joinCoeffVec (m := f.natDegree) (n := g.natDegree) q p)
      = fun i : Fin (g.natDegree + f.natDegree) => (f * q + g * p).coeff i := by
  classical
  -- helper: coefficients beyond degree bounds are zero
  have hq0 : ∀ j ≥ g.natDegree, q.coeff j = 0 := by
    intro j hj
    exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hq hj)
  have hp0 : ∀ j ≥ f.natDegree, p.coeff j = 0 := by
    intro j hj
    exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hp hj)
  ext i
  -- expand the mulVec against the Sylvester matrix
  -- then identify each block with coefficient formulas for products
  have hleft :
      (∑ x : Fin g.natDegree,
        if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + f.natDegree then
          f.coeff ((i : ℕ) - x) * q.coeff x
        else 0) =
        Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.1 * q.coeff x.2) := by
    -- the Sylvester block only contributes for x ≤ i; the extra upper bound kills terms by degree
    have hcoeff :
        Finset.sum (Finset.range ((i : ℕ) + 1)) (fun j => f.coeff ((i : ℕ) - j) * q.coeff j)
          = Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.1 * q.coeff x.2) := by
      have hswap :
          Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.1 * q.coeff x.2) =
            Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.2 * q.coeff x.1) := by
        simpa using
          (Finset.Nat.sum_antidiagonal_swap
            (f := fun x : ℕ × ℕ => f.coeff x.2 * q.coeff x.1) (n := (i : ℕ)))
      calc
        Finset.sum (Finset.range ((i : ℕ) + 1))
              (fun j => f.coeff ((i : ℕ) - j) * q.coeff j)
            =
            Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.2 * q.coeff x.1) := by
              simpa using
                (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
                  (f := fun x : ℕ × ℕ => f.coeff x.2 * q.coeff x.1) (n := (i : ℕ))).symm
        _ = Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.1 * q.coeff x.2) := by
              simpa using hswap.symm
    -- convert the finite sum over `Fin` into a range sum (indices beyond i vanish)
    have hsum :
        (∑ x : Fin g.natDegree,
          if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + f.natDegree then
            f.coeff ((i : ℕ) - x) * q.coeff x
          else 0)
          = Finset.sum (Finset.range ((i : ℕ) + 1)) (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
      classical
      -- replace the condition by `(x ≤ i)` since the other case yields zero coefficient
      have hcond :
          ∀ x : Fin g.natDegree,
            (if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + f.natDegree then
                f.coeff ((i : ℕ) - x) * q.coeff x else 0) =
              (if (x : ℕ) ≤ i then f.coeff ((i : ℕ) - x) * q.coeff x else 0) := by
        intro x
        by_cases hx : (x : ℕ) ≤ i
        · by_cases hxi : (i : ℕ) ≤ (x : ℕ) + f.natDegree
          · simp [hx, hxi]
          · have hlt : (x : ℕ) + f.natDegree < i := lt_of_not_ge hxi
            have hzero : f.coeff ((i : ℕ) - x) = 0 :=
              coeff_eq_zero_of_add_lt (p := f) (x := (x : ℕ)) (i := (i : ℕ)) hx hlt
            simp [hx, hxi, hzero]
        · simp [hx]
      have hsum_range :
          Finset.sum (Finset.range g.natDegree)
              (fun j => if j ≤ (i : ℕ) then f.coeff ((i : ℕ) - j) * q.coeff j else 0)
            =
            Finset.sum (Finset.range (Nat.min g.natDegree ((i : ℕ) + 1)))
              (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
        simpa using
          (sum_range_if_le g.natDegree (i : ℕ)
            (fun j => f.coeff ((i : ℕ) - j) * q.coeff j))
      have hsum_range' :
          Finset.sum (Finset.range (Nat.min g.natDegree ((i : ℕ) + 1)))
              (fun j => f.coeff ((i : ℕ) - j) * q.coeff j)
            =
            Finset.sum (Finset.range ((i : ℕ) + 1))
              (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
        by_cases hgi : (i : ℕ) + 1 ≤ g.natDegree
        · have hmin : Nat.min g.natDegree ((i : ℕ) + 1) = (i : ℕ) + 1 := Nat.min_eq_right hgi
          simp [hmin]
        · have hgi' : g.natDegree ≤ (i : ℕ) + 1 := Nat.le_of_not_le hgi
          obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hgi'
          have hmin : Nat.min g.natDegree ((i : ℕ) + 1) = g.natDegree := Nat.min_eq_left hgi'
          have htail :
              Finset.sum (Finset.range ((i : ℕ) + 1))
                  (fun j => f.coeff ((i : ℕ) - j) * q.coeff j)
                =
                Finset.sum (Finset.range g.natDegree)
                  (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
            have hzero : ∀ j ≥ g.natDegree,
                f.coeff ((i : ℕ) - j) * q.coeff j = 0 := by
              intro j hj
              have : q.coeff j = 0 := hq0 j hj
              simp [this]
            simpa [ht, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (sum_range_add_eq_sum_range_of_forall_ge
                (f := fun j => f.coeff ((i : ℕ) - j) * q.coeff j)
                (n := g.natDegree) (t := t) hzero)
          calc
            Finset.sum (Finset.range (Nat.min g.natDegree ((i : ℕ) + 1)))
                (fun j => f.coeff ((i : ℕ) - j) * q.coeff j)
                = Finset.sum (Finset.range g.natDegree)
                    (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
                      simp [hmin]
            _ = Finset.sum (Finset.range ((i : ℕ) + 1))
                    (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
                      simpa using htail.symm
      have :
          ∑ x : Fin g.natDegree,
            (if (x : ℕ) ≤ i then f.coeff ((i : ℕ) - x) * q.coeff x else 0) =
              Finset.sum (Finset.range ((i : ℕ) + 1))
                (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
        calc
          (∑ x : Fin g.natDegree,
              (if (x : ℕ) ≤ i then f.coeff ((i : ℕ) - x) * q.coeff x else 0))
              =
              Finset.sum (Finset.range g.natDegree)
                (fun j => if j ≤ (i : ℕ) then f.coeff ((i : ℕ) - j) * q.coeff j else 0) := by
                  simpa using
                    (Fin.sum_univ_eq_sum_range
                      (n := g.natDegree)
                      (fun j => if j ≤ (i : ℕ) then f.coeff ((i : ℕ) - j) * q.coeff j else 0))
          _ = Finset.sum (Finset.range (Nat.min g.natDegree ((i : ℕ) + 1)))
                (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := hsum_range
          _ = Finset.sum (Finset.range ((i : ℕ) + 1))
                (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := hsum_range'
      simpa [hcond] using this
    simpa [hsum] using hcoeff
  have hright :
      (∑ x : Fin f.natDegree,
        if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + g.natDegree then
          g.coeff ((i : ℕ) - x) * p.coeff x
        else 0) =
        Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.1 * p.coeff x.2) := by
    have hcoeff :
        Finset.sum (Finset.range ((i : ℕ) + 1)) (fun j => g.coeff ((i : ℕ) - j) * p.coeff j)
          = Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.1 * p.coeff x.2) := by
      have hswap :
          Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.1 * p.coeff x.2) =
            Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.2 * p.coeff x.1) := by
        simpa using
          (Finset.Nat.sum_antidiagonal_swap
            (f := fun x : ℕ × ℕ => g.coeff x.2 * p.coeff x.1) (n := (i : ℕ)))
      calc
        Finset.sum (Finset.range ((i : ℕ) + 1))
              (fun j => g.coeff ((i : ℕ) - j) * p.coeff j)
            =
            Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.2 * p.coeff x.1) := by
              simpa using
                (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
                  (f := fun x : ℕ × ℕ => g.coeff x.2 * p.coeff x.1) (n := (i : ℕ))).symm
        _ = Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.1 * p.coeff x.2) := by
              simpa using hswap.symm
    have hsum :
        (∑ x : Fin f.natDegree,
          if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + g.natDegree then
            g.coeff ((i : ℕ) - x) * p.coeff x
          else 0)
          = Finset.sum (Finset.range ((i : ℕ) + 1)) (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
      classical
      have hcond :
          ∀ x : Fin f.natDegree,
            (if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + g.natDegree then
                g.coeff ((i : ℕ) - x) * p.coeff x else 0) =
              (if (x : ℕ) ≤ i then g.coeff ((i : ℕ) - x) * p.coeff x else 0) := by
        intro x
        by_cases hx : (x : ℕ) ≤ i
        · by_cases hxi : (i : ℕ) ≤ (x : ℕ) + g.natDegree
          · simp [hx, hxi]
          · have hlt : (x : ℕ) + g.natDegree < i := lt_of_not_ge hxi
            have hzero : g.coeff ((i : ℕ) - x) = 0 :=
              coeff_eq_zero_of_add_lt (p := g) (x := (x : ℕ)) (i := (i : ℕ)) hx hlt
            simp [hx, hxi, hzero]
        · simp [hx]
      have hsum_range :
          Finset.sum (Finset.range f.natDegree)
              (fun j => if j ≤ (i : ℕ) then g.coeff ((i : ℕ) - j) * p.coeff j else 0)
            =
            Finset.sum (Finset.range (Nat.min f.natDegree ((i : ℕ) + 1)))
              (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
        simpa using
          (sum_range_if_le f.natDegree (i : ℕ)
            (fun j => g.coeff ((i : ℕ) - j) * p.coeff j))
      have hsum_range' :
          Finset.sum (Finset.range (Nat.min f.natDegree ((i : ℕ) + 1)))
              (fun j => g.coeff ((i : ℕ) - j) * p.coeff j)
            =
            Finset.sum (Finset.range ((i : ℕ) + 1))
              (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
        by_cases hfi : (i : ℕ) + 1 ≤ f.natDegree
        · have hmin : Nat.min f.natDegree ((i : ℕ) + 1) = (i : ℕ) + 1 := Nat.min_eq_right hfi
          simp [hmin]
        · have hfi' : f.natDegree ≤ (i : ℕ) + 1 := Nat.le_of_not_le hfi
          obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hfi'
          have hmin : Nat.min f.natDegree ((i : ℕ) + 1) = f.natDegree := Nat.min_eq_left hfi'
          have htail :
              Finset.sum (Finset.range ((i : ℕ) + 1))
                  (fun j => g.coeff ((i : ℕ) - j) * p.coeff j)
                =
                Finset.sum (Finset.range f.natDegree)
                  (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
            have hzero : ∀ j ≥ f.natDegree,
                g.coeff ((i : ℕ) - j) * p.coeff j = 0 := by
              intro j hj
              have : p.coeff j = 0 := hp0 j hj
              simp [this]
            simpa [ht, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (sum_range_add_eq_sum_range_of_forall_ge
                (f := fun j => g.coeff ((i : ℕ) - j) * p.coeff j)
                (n := f.natDegree) (t := t) hzero)
          calc
            Finset.sum (Finset.range (Nat.min f.natDegree ((i : ℕ) + 1)))
                (fun j => g.coeff ((i : ℕ) - j) * p.coeff j)
                = Finset.sum (Finset.range f.natDegree)
                    (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
                      simp [hmin]
            _ = Finset.sum (Finset.range ((i : ℕ) + 1))
                    (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
                      simpa using htail.symm
      have :
          ∑ x : Fin f.natDegree,
            (if (x : ℕ) ≤ i then g.coeff ((i : ℕ) - x) * p.coeff x else 0) =
              Finset.sum (Finset.range ((i : ℕ) + 1))
                (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
        calc
          (∑ x : Fin f.natDegree,
              (if (x : ℕ) ≤ i then g.coeff ((i : ℕ) - x) * p.coeff x else 0))
              =
              Finset.sum (Finset.range f.natDegree)
                (fun j => if j ≤ (i : ℕ) then g.coeff ((i : ℕ) - j) * p.coeff j else 0) := by
                  simpa using
                    (Fin.sum_univ_eq_sum_range
                      (n := f.natDegree)
                      (fun j => if j ≤ (i : ℕ) then g.coeff ((i : ℕ) - j) * p.coeff j else 0))
          _ = Finset.sum (Finset.range (Nat.min f.natDegree ((i : ℕ) + 1)))
                (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := hsum_range
          _ = Finset.sum (Finset.range ((i : ℕ) + 1))
                (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := hsum_range'
      simpa [hcond] using this
    simpa [hsum] using hcoeff
  -- now combine the two block sums
  have hmul :
      (Polynomial.sylvester f g f.natDegree g.natDegree).mulVec
          (joinCoeffVec (m := f.natDegree) (n := g.natDegree) q p) i
        =
        (∑ x : Fin g.natDegree,
            if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + f.natDegree then
              f.coeff ((i : ℕ) - x) * q.coeff x else 0)
          +
          (∑ x : Fin f.natDegree,
            if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + g.natDegree then
              g.coeff ((i : ℕ) - x) * p.coeff x else 0) := by
    classical
    simp [Matrix.mulVec, dotProduct, Polynomial.sylvester, joinCoeffVec, Fin.addCases,
      Fin.sum_univ_add, castAdd_le_iff, Set.mem_Icc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, Nat.add_le_add_iff_left]
  calc
    (Polynomial.sylvester f g f.natDegree g.natDegree).mulVec
        (joinCoeffVec (m := f.natDegree) (n := g.natDegree) q p) i
        = (∑ x : Fin g.natDegree,
            if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + f.natDegree then
              f.coeff ((i : ℕ) - x) * q.coeff x else 0)
            +
          (∑ x : Fin f.natDegree,
            if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + g.natDegree then
              g.coeff ((i : ℕ) - x) * p.coeff x else 0) := hmul
    _ =
        Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.1 * q.coeff x.2) +
        Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.1 * p.coeff x.2) := by
          simp [hleft, hright]
    _ = (f * q).coeff i + (g * p).coeff i := by
          simp [Polynomial.coeff_mul]
    _ = (f * q + g * p).coeff i := by
          simp [Polynomial.coeff_add]

lemma sylvester_mulVec_eq_coeff_add'
    (f g p q : R[X]) (m n : ℕ) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hp : p.natDegree < m) (hq : q.natDegree < n) :
    (Polynomial.sylvester f g m n).mulVec
        (joinCoeffVec (m := m) (n := n) q p)
      = fun i : Fin (n + m) => (f * q + g * p).coeff i := by
  classical
  -- helper: coefficients beyond degree bounds are zero
  have hq0 : ∀ j ≥ n, q.coeff j = 0 := by
    intro j hj
    exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hq hj)
  have hp0 : ∀ j ≥ m, p.coeff j = 0 := by
    intro j hj
    exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hp hj)
  ext i
  -- expand the mulVec against the Sylvester matrix
  -- then identify each block with coefficient formulas for products
  have hleft :
      (∑ x : Fin n,
        if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + m then
          f.coeff ((i : ℕ) - x) * q.coeff x
        else 0) =
        Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.1 * q.coeff x.2) := by
    -- the Sylvester block only contributes for x ≤ i; the extra upper bound kills terms by degree
    have hcoeff :
        Finset.sum (Finset.range ((i : ℕ) + 1)) (fun j => f.coeff ((i : ℕ) - j) * q.coeff j)
          = Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.1 * q.coeff x.2) := by
      have hswap :
          Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.1 * q.coeff x.2) =
            Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.2 * q.coeff x.1) := by
        simpa using
          (Finset.Nat.sum_antidiagonal_swap
            (f := fun x : ℕ × ℕ => f.coeff x.2 * q.coeff x.1) (n := (i : ℕ)))
      calc
        Finset.sum (Finset.range ((i : ℕ) + 1))
              (fun j => f.coeff ((i : ℕ) - j) * q.coeff j)
            =
            Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.2 * q.coeff x.1) := by
              simpa using
                (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
                  (f := fun x : ℕ × ℕ => f.coeff x.2 * q.coeff x.1) (n := (i : ℕ))).symm
        _ = Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.1 * q.coeff x.2) := by
              simpa using hswap.symm
    -- convert the finite sum over `Fin` into a range sum (indices beyond i vanish)
    have hsum :
        (∑ x : Fin n,
          if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + m then
            f.coeff ((i : ℕ) - x) * q.coeff x
          else 0)
          = Finset.sum (Finset.range ((i : ℕ) + 1)) (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
      classical
      -- replace the condition by `(x ≤ i)` since the other case yields zero coefficient
      have hcond :
          ∀ x : Fin n,
            (if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + m then
                f.coeff ((i : ℕ) - x) * q.coeff x else 0) =
              (if (x : ℕ) ≤ i then f.coeff ((i : ℕ) - x) * q.coeff x else 0) := by
        intro x
        by_cases hx : (x : ℕ) ≤ i
        · by_cases hxi : (i : ℕ) ≤ (x : ℕ) + m
          · simp [hx, hxi]
          · have hlt : (x : ℕ) + m < i := lt_of_not_ge hxi
            have hlt' : (x : ℕ) + f.natDegree < i := by
              exact lt_of_le_of_lt (Nat.add_le_add_left hf _) hlt
            have hzero : f.coeff ((i : ℕ) - x) = 0 :=
              coeff_eq_zero_of_add_lt (p := f) (x := (x : ℕ)) (i := (i : ℕ)) hx hlt'
            simp [hx, hxi, hzero]
        · simp [hx]
      have hsum_range :
          Finset.sum (Finset.range n)
              (fun j => if j ≤ (i : ℕ) then f.coeff ((i : ℕ) - j) * q.coeff j else 0)
            =
            Finset.sum (Finset.range (Nat.min n ((i : ℕ) + 1)))
              (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
        simpa using
          (sum_range_if_le n (i : ℕ)
            (fun j => f.coeff ((i : ℕ) - j) * q.coeff j))
      have hsum_range' :
          Finset.sum (Finset.range (Nat.min n ((i : ℕ) + 1)))
              (fun j => f.coeff ((i : ℕ) - j) * q.coeff j)
            =
            Finset.sum (Finset.range ((i : ℕ) + 1))
              (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
        by_cases hgi : (i : ℕ) + 1 ≤ n
        · have hmin : Nat.min n ((i : ℕ) + 1) = (i : ℕ) + 1 := Nat.min_eq_right hgi
          simp [hmin]
        · have hgi' : n ≤ (i : ℕ) + 1 := Nat.le_of_not_le hgi
          obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hgi'
          have hmin : Nat.min n ((i : ℕ) + 1) = n := Nat.min_eq_left hgi'
          have htail :
              Finset.sum (Finset.range ((i : ℕ) + 1))
                  (fun j => f.coeff ((i : ℕ) - j) * q.coeff j)
                =
                Finset.sum (Finset.range n)
                  (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
            have hzero : ∀ j ≥ n,
                f.coeff ((i : ℕ) - j) * q.coeff j = 0 := by
              intro j hj
              have : q.coeff j = 0 := hq0 j hj
              simp [this]
            simpa [ht, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (sum_range_add_eq_sum_range_of_forall_ge
                (f := fun j => f.coeff ((i : ℕ) - j) * q.coeff j)
                (n := n) (t := t) hzero)
          calc
            Finset.sum (Finset.range (Nat.min n ((i : ℕ) + 1)))
                (fun j => f.coeff ((i : ℕ) - j) * q.coeff j)
                = Finset.sum (Finset.range n)
                    (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
                      simp [hmin]
            _ = Finset.sum (Finset.range ((i : ℕ) + 1))
                    (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
                      simpa using htail.symm
      have :
          ∑ x : Fin n,
            (if (x : ℕ) ≤ i then f.coeff ((i : ℕ) - x) * q.coeff x else 0) =
              Finset.sum (Finset.range ((i : ℕ) + 1))
                (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := by
        calc
          (∑ x : Fin n,
              (if (x : ℕ) ≤ i then f.coeff ((i : ℕ) - x) * q.coeff x else 0))
              =
              Finset.sum (Finset.range n)
                (fun j => if j ≤ (i : ℕ) then f.coeff ((i : ℕ) - j) * q.coeff j else 0) := by
                  simpa using
                    (Fin.sum_univ_eq_sum_range
                      (n := n)
                      (fun j => if j ≤ (i : ℕ) then f.coeff ((i : ℕ) - j) * q.coeff j else 0))
          _ = Finset.sum (Finset.range (Nat.min n ((i : ℕ) + 1)))
                (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := hsum_range
          _ = Finset.sum (Finset.range ((i : ℕ) + 1))
                (fun j => f.coeff ((i : ℕ) - j) * q.coeff j) := hsum_range'
      simpa [hcond] using this
    simpa [hsum] using hcoeff
  have hright :
      (∑ x : Fin m,
        if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + n then
          g.coeff ((i : ℕ) - x) * p.coeff x
        else 0) =
        Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.1 * p.coeff x.2) := by
    have hcoeff :
        Finset.sum (Finset.range ((i : ℕ) + 1)) (fun j => g.coeff ((i : ℕ) - j) * p.coeff j)
          = Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.1 * p.coeff x.2) := by
      have hswap :
          Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.1 * p.coeff x.2) =
            Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.2 * p.coeff x.1) := by
        simpa using
          (Finset.Nat.sum_antidiagonal_swap
            (f := fun x : ℕ × ℕ => g.coeff x.2 * p.coeff x.1) (n := (i : ℕ)))
      calc
        Finset.sum (Finset.range ((i : ℕ) + 1))
              (fun j => g.coeff ((i : ℕ) - j) * p.coeff j)
            =
            Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.2 * p.coeff x.1) := by
              simpa using
                (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
                  (f := fun x : ℕ × ℕ => g.coeff x.2 * p.coeff x.1) (n := (i : ℕ))).symm
        _ = Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.1 * p.coeff x.2) := by
              simpa using hswap.symm
    have hsum :
        (∑ x : Fin m,
          if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + n then
            g.coeff ((i : ℕ) - x) * p.coeff x
          else 0)
          = Finset.sum (Finset.range ((i : ℕ) + 1)) (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
      classical
      have hcond :
          ∀ x : Fin m,
            (if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + n then
                g.coeff ((i : ℕ) - x) * p.coeff x else 0) =
              (if (x : ℕ) ≤ i then g.coeff ((i : ℕ) - x) * p.coeff x else 0) := by
        intro x
        by_cases hx : (x : ℕ) ≤ i
        · by_cases hxi : (i : ℕ) ≤ (x : ℕ) + n
          · simp [hx, hxi]
          · have hlt : (x : ℕ) + n < i := lt_of_not_ge hxi
            have hlt' : (x : ℕ) + g.natDegree < i := by
              exact lt_of_le_of_lt (Nat.add_le_add_left hg _) hlt
            have hzero : g.coeff ((i : ℕ) - x) = 0 :=
              coeff_eq_zero_of_add_lt (p := g) (x := (x : ℕ)) (i := (i : ℕ)) hx hlt'
            simp [hx, hxi, hzero]
        · simp [hx]
      have hsum_range :
          Finset.sum (Finset.range m)
              (fun j => if j ≤ (i : ℕ) then g.coeff ((i : ℕ) - j) * p.coeff j else 0)
            =
            Finset.sum (Finset.range (Nat.min m ((i : ℕ) + 1)))
              (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
        simpa using
          (sum_range_if_le m (i : ℕ)
            (fun j => g.coeff ((i : ℕ) - j) * p.coeff j))
      have hsum_range' :
          Finset.sum (Finset.range (Nat.min m ((i : ℕ) + 1)))
              (fun j => g.coeff ((i : ℕ) - j) * p.coeff j)
            =
            Finset.sum (Finset.range ((i : ℕ) + 1))
              (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
        by_cases hgi : (i : ℕ) + 1 ≤ m
        · have hmin : Nat.min m ((i : ℕ) + 1) = (i : ℕ) + 1 := Nat.min_eq_right hgi
          simp [hmin]
        · have hgi' : m ≤ (i : ℕ) + 1 := Nat.le_of_not_le hgi
          obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hgi'
          have hmin : Nat.min m ((i : ℕ) + 1) = m := Nat.min_eq_left hgi'
          have htail :
              Finset.sum (Finset.range ((i : ℕ) + 1))
                  (fun j => g.coeff ((i : ℕ) - j) * p.coeff j)
                =
                Finset.sum (Finset.range m)
                  (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
            have hzero : ∀ j ≥ m,
                g.coeff ((i : ℕ) - j) * p.coeff j = 0 := by
              intro j hj
              have : p.coeff j = 0 := hp0 j hj
              simp [this]
            simpa [ht, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (sum_range_add_eq_sum_range_of_forall_ge
                (f := fun j => g.coeff ((i : ℕ) - j) * p.coeff j)
                (n := m) (t := t) hzero)
          calc
            Finset.sum (Finset.range (Nat.min m ((i : ℕ) + 1)))
                (fun j => g.coeff ((i : ℕ) - j) * p.coeff j)
                = Finset.sum (Finset.range m)
                    (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
                      simp [hmin]
            _ = Finset.sum (Finset.range ((i : ℕ) + 1))
                    (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
                      simpa using htail.symm
      have :
          ∑ x : Fin m,
            (if (x : ℕ) ≤ i then g.coeff ((i : ℕ) - x) * p.coeff x else 0) =
              Finset.sum (Finset.range ((i : ℕ) + 1))
                (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := by
        calc
          (∑ x : Fin m,
              (if (x : ℕ) ≤ i then g.coeff ((i : ℕ) - x) * p.coeff x else 0))
              =
              Finset.sum (Finset.range m)
                (fun j => if j ≤ (i : ℕ) then g.coeff ((i : ℕ) - j) * p.coeff j else 0) := by
                  simpa using
                    (Fin.sum_univ_eq_sum_range
                      (n := m)
                      (fun j => if j ≤ (i : ℕ) then g.coeff ((i : ℕ) - j) * p.coeff j else 0))
          _ = Finset.sum (Finset.range (Nat.min m ((i : ℕ) + 1)))
                (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := hsum_range
          _ = Finset.sum (Finset.range ((i : ℕ) + 1))
                (fun j => g.coeff ((i : ℕ) - j) * p.coeff j) := hsum_range'
      simpa [hcond] using this
    simpa [hsum] using hcoeff
  -- now combine the two block sums
  have hmul :
      (Polynomial.sylvester f g m n).mulVec
          (joinCoeffVec (m := m) (n := n) q p) i
        =
        (∑ x : Fin n,
            if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + m then
              f.coeff ((i : ℕ) - x) * q.coeff x else 0)
          +
          (∑ x : Fin m,
            if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + n then
              g.coeff ((i : ℕ) - x) * p.coeff x else 0) := by
    classical
    simp [Matrix.mulVec, dotProduct, Polynomial.sylvester, joinCoeffVec, Fin.addCases,
      Fin.sum_univ_add, castAdd_le_iff, Set.mem_Icc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, Nat.add_le_add_iff_left]
  calc
    (Polynomial.sylvester f g m n).mulVec
        (joinCoeffVec (m := m) (n := n) q p) i
        = (∑ x : Fin n,
            if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + m then
              f.coeff ((i : ℕ) - x) * q.coeff x else 0)
            +
          (∑ x : Fin m,
            if (x : ℕ) ≤ i ∧ (i : ℕ) ≤ (x : ℕ) + n then
              g.coeff ((i : ℕ) - x) * p.coeff x else 0) := hmul
    _ =
        Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => f.coeff x.1 * q.coeff x.2) +
        Finset.sum (Finset.antidiagonal (i : ℕ)) (fun x => g.coeff x.1 * p.coeff x.2) := by
          simp [hleft, hright]
    _ = (f * q).coeff i + (g * p).coeff i := by
          simp [Polynomial.coeff_mul]
    _ = (f * q + g * p).coeff i := by
          simp [Polynomial.coeff_add]

lemma sylvester_mulVec_eq_zero_of_common_root'
    (f g p q : R[X]) {m n : ℕ} (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hp : p.natDegree < m) (hq : q.natDegree < n) (h : f * q + g * p = 0) :
    (Polynomial.sylvester f g m n).mulVec
        (joinCoeffVec (m := m) (n := n) q p) = 0 := by
  classical
  ext i
  simp [sylvester_mulVec_eq_coeff_add' (f := f) (g := g) (p := p) (q := q) m n hf hg hp hq, h]

lemma resultant_eq_zero_of_common_root'
    (f g p q : R[X]) {m n : ℕ} (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hp : p.natDegree < m) (hq : q.natDegree < n) (h : f * q + g * p = 0)
    (hvec : ∃ i, (joinCoeffVec (m := m) (n := n) q p) i ≠ 0) :
    Polynomial.resultant f g m n = 0 := by
  classical
  have hmul :
      (Polynomial.sylvester f g m n).mulVec
          (joinCoeffVec (m := m) (n := n) q p) = 0 :=
    sylvester_mulVec_eq_zero_of_common_root'
      (f := f) (g := g) (p := p) (q := q) hf hg hp hq h
  have hdet : (Polynomial.sylvester f g m n).det = 0 := by
    have h' : ∃ v ≠ (0 : Fin (n + m) → R),
        (Polynomial.sylvester f g m n).mulVec v = 0 := by
      refine ⟨joinCoeffVec (m := m) (n := n) q p, ?_, hmul⟩
      classical
      intro hzero
      rcases hvec with ⟨i, hi⟩
      exact hi (by simpa [hzero])
    simpa [Polynomial.resultant] using
      (Matrix.exists_mulVec_eq_zero_iff (M := Polynomial.sylvester f g m n)).1 h'
  simpa [Polynomial.resultant] using hdet

lemma exists_bezout_of_resultant_eq_zero {f g : R[X]}
    (hf : 0 < f.natDegree) (hg : 0 < g.natDegree)
    (hres : Polynomial.resultant f g = 0) :
    ∃ p q, p.natDegree < f.natDegree ∧ q.natDegree < g.natDegree ∧
      f * q + g * p = 0 ∧ (p ≠ 0 ∨ q ≠ 0) := by
  classical
  have hdet :
      (Polynomial.sylvester f g f.natDegree g.natDegree).det = 0 := by
    simpa [Polynomial.resultant] using hres
  have hvec :
      ∃ v ≠ (0 : Fin (g.natDegree + f.natDegree) → R),
        (Polynomial.sylvester f g f.natDegree g.natDegree).mulVec v = 0 := by
    exact (Matrix.exists_mulVec_eq_zero_iff
      (M := Polynomial.sylvester f g f.natDegree g.natDegree)).2 hdet
  rcases hvec with ⟨v, hv, hmul⟩
  let q : R[X] := polyOfVec g.natDegree (fun i => v (Fin.castAdd f.natDegree i))
  let p : R[X] := polyOfVec f.natDegree (fun i => v (Fin.natAdd g.natDegree i))
  have hjoin :
      joinCoeffVec (m := f.natDegree) (n := g.natDegree) q p = v := by
    simpa [q, p, add_comm] using
      (joinCoeffVec_polyOfVec (v := v) (m := f.natDegree) (n := g.natDegree))
  have hmul' :
      (Polynomial.sylvester f g f.natDegree g.natDegree).mulVec
          (joinCoeffVec (m := f.natDegree) (n := g.natDegree) q p) = 0 := by
    simpa [hjoin] using hmul
  have hpdeg : p.natDegree < f.natDegree := by
    simpa [p] using (natDegree_polyOfVec_lt (v := fun i =>
      v (Fin.natAdd g.natDegree i)) (hn := Nat.ne_of_gt hf))
  have hqdeg : q.natDegree < g.natDegree := by
    simpa [q] using (natDegree_polyOfVec_lt (v := fun i =>
      v (Fin.castAdd f.natDegree i)) (hn := Nat.ne_of_gt hg))
  have hcoeff :
      (fun i : Fin (g.natDegree + f.natDegree) => (f * q + g * p).coeff i) = 0 := by
    simpa [sylvester_mulVec_eq_coeff_add (f := f) (g := g) (p := p) (q := q) hpdeg hqdeg] using hmul'
  have hdeg :
      (f * q + g * p).natDegree < g.natDegree + f.natDegree := by
    have h1 : (f * q).natDegree ≤ f.natDegree + q.natDegree :=
      Polynomial.natDegree_mul_le
    have h2 : (g * p).natDegree ≤ g.natDegree + p.natDegree :=
      Polynomial.natDegree_mul_le
    have hmax :
        max (f.natDegree + q.natDegree) (g.natDegree + p.natDegree) <
          g.natDegree + f.natDegree := by
      have hq : f.natDegree + q.natDegree < f.natDegree + g.natDegree :=
        Nat.add_lt_add_left hqdeg _
      have hp : g.natDegree + p.natDegree < g.natDegree + f.natDegree :=
        Nat.add_lt_add_left hpdeg _
      have hq' : f.natDegree + q.natDegree < g.natDegree + f.natDegree := by
        simpa [add_comm] using hq
      have hp' : g.natDegree + p.natDegree < g.natDegree + f.natDegree := hp
      exact max_lt_iff.2 ⟨hq', hp'⟩
    have hsum :
        (f * q + g * p).natDegree ≤
          max (f * q).natDegree (g * p).natDegree := by
        simpa using Polynomial.natDegree_add_le (f * q) (g * p)
    have hsum' :
        max (f * q).natDegree (g * p).natDegree ≤
          max (f.natDegree + q.natDegree) (g.natDegree + p.natDegree) := by
      exact max_le_iff.2
        ⟨le_trans h1 (Nat.le_max_left _ _), le_trans h2 (Nat.le_max_right _ _)⟩
    exact lt_of_le_of_lt (hsum.trans hsum') hmax
  have hpoly : f * q + g * p = 0 := by
    apply Polynomial.ext
    intro i
    by_cases hi : i < g.natDegree + f.natDegree
    · have := congrArg (fun w => w ⟨i, hi⟩) hcoeff
      simpa using this
    · have hlt : (f * q + g * p).natDegree < i := by
        exact lt_of_lt_of_le hdeg (le_of_not_gt hi)
      simpa using (coeff_eq_zero_of_natDegree_lt hlt)
  have hnonzero : p ≠ 0 ∨ q ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    have hv' : v = 0 := by
      have : joinCoeffVec (m := f.natDegree) (n := g.natDegree) q p = 0 := by
        funext j
        cases' j using Fin.addCases with j1 j1
        · simp [joinCoeffVec, hzero.2]
        · simp [joinCoeffVec, hzero.1]
      simpa [hjoin] using this
    exact hv (by simpa [hv'] )
  exact ⟨p, q, hpdeg, hqdeg, hpoly, hnonzero⟩

lemma sylvester_mulVec_eq_zero_of_common_root
    (f g p q : R[X]) (hp : p.natDegree < f.natDegree) (hq : q.natDegree < g.natDegree)
    (h : f * q + g * p = 0) :
    (Polynomial.sylvester f g f.natDegree g.natDegree).mulVec
        (joinCoeffVec (m := f.natDegree) (n := g.natDegree) q p) = 0 := by
  classical
  ext i
  simp [sylvester_mulVec_eq_coeff_add (f := f) (g := g) (p := p) (q := q) hp hq, h]

lemma resultant_eq_zero_of_common_root
    (f g p q : R[X]) (hp : p.natDegree < f.natDegree) (hq : q.natDegree < g.natDegree)
    (h : f * q + g * p = 0)
    (hvec : ∃ i, (joinCoeffVec (m := f.natDegree) (n := g.natDegree) q p) i ≠ 0) :
    Polynomial.resultant f g = 0 := by
  classical
  have hmul :
      (Polynomial.sylvester f g f.natDegree g.natDegree).mulVec
          (joinCoeffVec (m := f.natDegree) (n := g.natDegree) q p) = 0 :=
    sylvester_mulVec_eq_zero_of_common_root (f := f) (g := g) (p := p) (q := q) hp hq h
  have hdet : (Polynomial.sylvester f g f.natDegree g.natDegree).det = 0 := by
    have h' : ∃ v ≠ (0 : Fin (g.natDegree + f.natDegree) → R),
        (Polynomial.sylvester f g f.natDegree g.natDegree).mulVec v = 0 := by
      refine ⟨joinCoeffVec (m := f.natDegree) (n := g.natDegree) q p, ?_, hmul⟩
      classical
      intro hzero
      rcases hvec with ⟨i, hi⟩
      exact hi (by simpa [hzero])
    simpa [Polynomial.resultant] using
      (Matrix.exists_mulVec_eq_zero_iff (M := Polynomial.sylvester f g f.natDegree g.natDegree)).1 h'
  simpa [Polynomial.resultant] using hdet

section ResultantRoots

variable {F : Type} [CommRing F] [IsDomain F]

lemma X_sub_C_dvd_of_eval_eq_zero {p : F[X]} {t : F} (ht : p.eval t = 0) :
    X - C t ∣ p := by
  have hmod : p %ₘ (X - C t) = 0 := by
    simpa [Polynomial.modByMonic_X_sub_C_eq_C_eval, ht]
  exact (Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_sub_C t)).1 hmod

lemma resultant_eq_zero_of_common_root_eval'
    {f g : F[X]} (hf : f ≠ 0) (hg : g ≠ 0) {t : F}
    (hft : f.eval t = 0) (hgt : g.eval t = 0) {m n : ℕ}
    (hf_le : f.natDegree ≤ m) (hg_le : g.natDegree ≤ n) :
    Polynomial.resultant f g m n = 0 := by
  rcases X_sub_C_dvd_of_eval_eq_zero (p := f) (t := t) hft with ⟨f1, hf1⟩
  rcases X_sub_C_dvd_of_eval_eq_zero (p := g) (t := t) hgt with ⟨g1, hg1⟩
  have hf1_ne : f1 ≠ 0 := by
    intro h
    apply hf
    simpa [hf1, h] using (by rfl : (X - C t) * f1 = (X - C t) * f1)
  have hg1_ne : g1 ≠ 0 := by
    intro h
    apply hg
    simpa [hg1, h] using (by rfl : (X - C t) * g1 = (X - C t) * g1)
  have hdegf : f1.natDegree < f.natDegree := by
    have hdeg :
        f.natDegree = (X - C t).natDegree + f1.natDegree := by
      simpa [hf1] using
        (Polynomial.natDegree_mul (p := (X - C t)) (q := f1)
          (Polynomial.X_sub_C_ne_zero t) hf1_ne)
    have hnat : (X - C t).natDegree = 1 := by
      simpa using (Polynomial.natDegree_X_sub_C t)
    have hdeg' : f.natDegree = f1.natDegree + 1 := by
      simpa [hnat, Nat.add_comm] using hdeg
    simpa [hdeg'] using (Nat.lt_succ_self f1.natDegree)
  have hdegg : g1.natDegree < g.natDegree := by
    have hdeg :
        g.natDegree = (X - C t).natDegree + g1.natDegree := by
      simpa [hg1] using
        (Polynomial.natDegree_mul (p := (X - C t)) (q := g1)
          (Polynomial.X_sub_C_ne_zero t) hg1_ne)
    have hnat : (X - C t).natDegree = 1 := by
      simpa using (Polynomial.natDegree_X_sub_C t)
    have hdeg' : g.natDegree = g1.natDegree + 1 := by
      simpa [hnat, Nat.add_comm] using hdeg
    simpa [hdeg'] using (Nat.lt_succ_self g1.natDegree)
  have hlin : f * g1 + g * (-f1) = 0 := by
    calc
      f * g1 + g * (-f1)
          = (X - C t) * (f1 * g1) + (X - C t) * (g1 * (-f1)) := by
                simp [hf1, hg1, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = (X - C t) * (f1 * g1 + g1 * (-f1)) := by
                simp [mul_add]
      _ = (X - C t) * 0 := by ring
      _ = 0 := by simp
  have hvec : ∃ i, (joinCoeffVec (m := m) (n := n) g1 (-f1)) i ≠ 0 := by
    have hneg_ne : (-f1) ≠ 0 := by
      simpa using (neg_ne_zero.mpr hf1_ne)
    have hcoeff' : (-f1).coeff (f1.natDegree) ≠ 0 := by
      have hlead' : (-f1).leadingCoeff ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr hneg_ne
      have hcoeff'' : (-f1).coeff (-f1).natDegree ≠ 0 := by
        simpa [Polynomial.coeff_natDegree] using hlead'
      simpa [Polynomial.natDegree_neg] using hcoeff''
    let i : Fin f.natDegree := ⟨f1.natDegree, hdegf⟩
    let i' : Fin m := ⟨i.1, lt_of_lt_of_le i.is_lt hf_le⟩
    refine ⟨Fin.natAdd n i', ?_⟩
    have hval' :
        joinCoeffVec (m := m) (n := n) g1 (-f1)
          (Fin.natAdd n i') = (-f1).coeff i' := by
      -- `addCases` picks the right branch on `natAdd`
      simpa [joinCoeffVec] using
        (Fin.addCases_right
          (u := fun j1 => g1.coeff j1)
          (v := fun j1 => (-f1).coeff j1) (i := i'))
    have hval :
        joinCoeffVec (m := m) (n := n) g1 (-f1)
          (Fin.natAdd n i') = (-f1).coeff i := by
      simpa [i', i] using hval'
    intro hzero
    apply hcoeff'
    -- rewrite to the coefficient
    have : (-f1).coeff i = 0 := by simpa [hval] using hzero
    simpa [i] using this
  have hdegf' : (-f1).natDegree < m := lt_of_lt_of_le (by simpa using hdegf) hf_le
  have hdegg' : g1.natDegree < n := lt_of_lt_of_le hdegg hg_le
  exact
    resultant_eq_zero_of_common_root'
      (f := f) (g := g) (p := -f1) (q := g1)
      (hf := hf_le) (hg := hg_le) (hp := hdegf') (hq := hdegg') (h := hlin) (hvec := hvec)

lemma resultant_eq_zero_of_common_root_eval
    {f g : F[X]} (hf : f ≠ 0) (hg : g ≠ 0) {t : F}
    (hft : f.eval t = 0) (hgt : g.eval t = 0) :
    Polynomial.resultant f g = 0 := by
  simpa [Polynomial.resultant] using
    (resultant_eq_zero_of_common_root_eval' (f := f) (g := g) (t := t)
      (hf := hf) (hg := hg) (hft := hft) (hgt := hgt)
      (m := f.natDegree) (n := g.natDegree) (hf_le := le_rfl) (hg_le := le_rfl))

end ResultantRoots

end SylvesterKernel

end BCIKS20AppendixA
