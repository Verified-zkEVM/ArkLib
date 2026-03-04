import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange

import ArkLib.Data.CodingTheory.ProximityGap.Basic

namespace ProximityGap

open NNReal Finset Function
open scoped ProbabilityTheory
open scoped BigOperators LinearCode
open Code Affine
open Polynomial

universe u v w k l

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type k} {ι : Type l} [DecidableEq ι] [Fintype κ] [Fintype ι] [Nonempty ι]
-- κ => row indices, ι => column indices
variable {F : Type v} [Field F] [Fintype F] [DecidableEq F]
-- variable {M : Type} [Fintype M] -- Message space type
variable {A : Type w} [Fintype A] [DecidableEq A] [AddCommMonoid A] [Module F A] -- Alphabet type
variable (C : Set (ι → A))

def iotaK (domain : ι ↪ F) (k : ℕ) : Finset ι :=
  {i : ι | ∃ i' : ι, domain i' ^ k = domain i}

def domainK (domain : ι ↪ F) (k : ℕ) : iotaK domain k ↪ F := 
  ⟨fun i => domain i.val, by {
    intro x y hxy
    simp at hxy
    tauto
  }⟩ 

noncomputable def foldAux (domain : ι ↪ F) (f : Word F ι) (k : ℕ) (x : F) : Polynomial F := 
  Lagrange.interpolate {i | domain i ^ k = x} (fun i => domain i) f  

lemma foldAux_natDegree {domain : ι ↪ F} {f : Word F ι} {k : ℕ} {x : F} 
  [inst : NeZero k]
  :
  (foldAux domain f k x).natDegree < k := by
  by_cases heq: foldAux domain f k x = 0 
  · simp [heq]
    have h := NeZero.ne (h := inst) 
    omega
  · unfold foldAux at *
    apply lt_of_lt_of_le
    rw [Polynomial.natDegree_lt_iff_degree_lt (by aesop)]
    apply Lagrange.degree_interpolate_lt _ (by simp)
    have h : Finset.image domain {i | domain i ^ k = x} = 
      @Set.toFinset _ (((Polynomial.X : Polynomial F) ^ k - C x).rootSet F ∩ Finset.image domain Finset.univ) (by sorry) := by
      apply Finset.ext
      intro a
      simp
      apply Iff.intro
      · intro h
        rcases h with ⟨y, ⟨h1, h2⟩⟩ 
        rw [←h2]
        rw [Polynomial.mem_rootSet]
        simp [h1]
        intro contra
        have h: ( Y ^ k - C x ).coeff k = 0 := by
          rw [contra]
          simp
        simp [Polynomial.coeff_C] at h
        have hk : k ≠ 0 := NeZero.ne (h := inst)
        simp [hk] at h
      · intro h
        rw [Polynomial.mem_rootSet] at h
        simp at h
        rcases h with ⟨h1, ⟨y, h2⟩⟩ 
        exists y
        simp [h2]
        rcases h1 with ⟨_, h1⟩ 
        rw [sub_eq_zero] at h1
        simp [h1]
    rw [←Finset.card_image_of_injOn (f := domain) (by simp)]
    rw [h]
    simp
    apply le_trans
    apply Finset.card_le_card (by {
        apply Finset.inter_subset_left
    })
    rw [←Set.ncard_eq_toFinset_card']
    apply le_trans (b := (Y ^ k - C x).natDegree)
    grw [rootSet, Set.ncard_coe_finset, aroots]
    rw [Polynomial.map]
    simp
    apply le_trans
    apply @Multiset.toFinset_card_le F (Classical.decEq F)
    apply le_trans
    apply Polynomial.card_roots'
    apply le_trans
    apply Polynomial.natDegree_sub_le
    simp
    apply le_trans
    apply Polynomial.natDegree_sub_le
    simp
  
noncomputable def fold (domain : ι ↪ F) (f : Word F ι) (k : ℕ) (α : F) :
  Word F (iotaK domain k)
  := fun x => (foldAux domain f k (domainK domain k x)).eval α 

end ProximityGap
