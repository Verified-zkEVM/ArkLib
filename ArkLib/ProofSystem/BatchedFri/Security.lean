/- Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: František Silváši, Julian Sutherland, Ilia Vlasov

  [BCIKS20] refers to the paper "Proximity Gaps for Reed-Solomon Codes" by Eli Ben-Sasson,
  Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.

  Using {https://eprint.iacr.org/2020/654}, version 20210703:203025.
-/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ReedSolomon.FftDomain
import ArkLib.Data.CodingTheory.Prelims
import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.BatchedFri.Spec.General
import ArkLib.ProofSystem.Fri.Spec.General
import ArkLib.ProofSystem.Fri.Spec.SingleRound
import ArkLib.OracleReduction.Security.Basic
import ToMathlib.Control.OptionT
import ArkLib.ToMathlib.List.Basic
import ArkLib.ToMathlib.Finset.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors

namespace Fri
section Fri

open OracleComp OracleSpec ProtocolSpec ReedSolomon
open NNReal Finset Function ProbabilityTheory

variable {𝔽 : Type} [NonBinaryField 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [Nontrivial 𝔽]
variable (n : ℕ)
variable (g : 𝔽ˣ) {k : ℕ}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable {i : Fin (k + 1)}
variable {ω : SmoothCosetFftDomain n 𝔽}

attribute [instance high] Spec.QueryRound.instOracleInterfaceMessagePSpec

instance {F : Type} [Field F] {a : F} [inst : NeZero a] : Invertible a where
  invOf := a⁻¹
  invOf_mul_self := by field_simp [inst.out]
  mul_invOf_self := by field_simp [inst.out]

section Completeness

abbrev evalDomainSigma {n k : ℕ} (s : Fin (k + 1) → ℕ+)
  (ω : SmoothCosetFftDomain n 𝔽) (i : ℕ) :=
  ω.subdomainNatReversed (∑ j' ∈ finRangeTo (k + 1) i, s j')

def cosetEnum (s₀ : evalDomainSigma s ω i) (k_le_n : ∑ j', (s j').1 ≤ n)
      (j : Fin (2 ^ (s i).1)) : evalDomainSigma s ω ↑i :=
  let r : {x | x ∈ ω.fftDomain.subdomainNatReversed (n - ↑(s i))} :=
    ⟨ω.fftDomain.subdomainNatReversed (n - (s i).1)
      ⟨j.1,
        by
          have s_i_lim : (s i).1 < n + 1 := by
            apply Nat.lt_succ_of_le
            rw [Finset.sum_eq_sum_diff_singleton_add (i := i) (by simp)] at k_le_n
            apply (swap <| Nat.le_trans) k_le_n
            omega
          rcases j with ⟨j, h⟩
          simp only [Nat.succ_eq_add_one, Fin.ofNat_eq_cast, Fin.val_natCast]
          have : n - (n - (s i).1) = (s i).1 := by
            apply Nat.sub_sub_self
            exact Nat.le_of_lt_succ s_i_lim
          rw [this]
          convert h
      ⟩,
      FftDomain.mem_domain_self
    ⟩
  let x : (evalDomainSigma s ω ↑i).toFinset := ⟨
    s₀.1 * r.1,
    by {
      rw [CosetFftDomain.mem_coset_finset_iff_mem_coset_domain]
      exact CosetFftDomain.subdomainNatReversed_mul_property (by {
        apply Nat.le_sub_of_add_le
        apply le_trans
          (b := ∑ j' ∈ finRangeTo (k + 1) ↑i, (s j').1 + (s i).1)
          (c := n)
        · constructor
        · rw [←sum_finRangeTo_add_one]
          apply le_trans (b := ∑ j', (s j').1) <;> try omega
          apply Finset.sum_le_sum_of_subset
          simp
      }) (by omega) (by {
        rcases s₀ with ⟨s₀, hs₀⟩ 
        simp only
        simp only [evalDomainSigma] at hs₀ 
        rw [CosetFftDomain.mem_coset_finset_iff_mem_coset_domain] at hs₀
        exact hs₀
      }) r.2
    }
  ⟩
  ↑x

def cosetG (s₀ : evalDomainSigma s ω ↑i)
  : Finset (evalDomainSigma s ω ↑i) :=
  if k_le_n : ∑ j', (s j').1 ≤ n
  then
    (Finset.univ).image (cosetEnum n s s₀ k_le_n)
  else ∅

def pows (z : 𝔽) (ℓ : ℕ) : Matrix Unit (Fin ℓ) 𝔽 :=
  Matrix.of <| fun _ j => z ^ j.val

def VDM (s₀ : evalDomainSigma s ω ↑i) :
  Matrix (Fin (2 ^ (s i : ℕ))) (Fin (2 ^ (s i : ℕ))) 𝔽 :=
  if k_le_n : (∑ j', (s j').1) ≤ n
  then Matrix.vandermonde (fun j => (cosetEnum n s s₀ k_le_n j).1)
  else 1

def cosetEnum' (s₀ : evalDomainSigma s ω ↑i)
  (k_le_n : ∑ j', (s j').1 ≤ n)
  (j : Fin (2 ^ (s i).1)) : cosetG n s s₀ :=
  ⟨
    cosetEnum n s s₀ k_le_n j,
    by simp [cosetG, k_le_n]
  ⟩

noncomputable def fin_equiv_coset (s₀ : evalDomainSigma s ω ↑i)
    (k_le_n : ∑ j', (s j').1 ≤ n) :
    (Fin (2 ^ (s i).1)) ≃ { x // x ∈ cosetG n s s₀ } := by
  apply Equiv.ofBijective (cosetEnum' n s s₀ k_le_n)
  unfold cosetEnum' cosetEnum
  unfold Function.Bijective
  apply And.intro
  · intros a b h
    simp only [Nat.succ_eq_add_one, finRangeTo.eq_1, Fin.ofNat_eq_cast, Fin.val_natCast,
      Set.mem_setOf_eq, FftDomain.subdomainNatReversed, FftDomain.subdomainNat, Subtype.mk.injEq,
      mul_eq_mul_left_iff] at h
    rcases h with h | h
    · have h := FftDomain.injective h
      aesop
    · rcases s₀ with ⟨s₀, hs₀⟩
      subst h
      simp only [Nat.succ_eq_add_one, finRangeTo.eq_1, Fin.ofNat_eq_cast, Fin.val_natCast,
        evalDomainSigma, CosetFftDomain.subdomainNatReversed, CosetFftDomain.subdomainNat] at hs₀
      rw [CosetFftDomain.mem_coset_finset_iff_mem_coset_domain] at hs₀ 
      have hs₀ := CosetFftDomain.zero_is_not_in_domain hs₀
      simp at hs₀
  · rintro ⟨⟨y, h'⟩, h⟩
    simp only [FftDomain.subdomainNatReversed,
      FftDomain.subdomainNat,
      finRangeTo.eq_1, Subtype.mk.injEq]
    simp only [finRangeTo.eq_1, cosetG, k_le_n,
      ↓reduceDIte, mem_image, mem_univ, cosetEnum, Subtype.mk.injEq, true_and] at h
    exact h

def invertibleDomain (s₀ : evalDomainSigma s ω ↑i) : Invertible (VDM n s s₀) := by
  haveI : NeZero (VDM n s s₀).det := by
    constructor
    unfold VDM
    split_ifs with cond
    · simp only [Matrix.det_vandermonde]
      rw [Finset.prod_ne_zero_iff]
      intros i' _
      rw [Finset.prod_ne_zero_iff]
      intros j' h'
      have : i' ≠ j' := by
        rename_i a
        simp_all only [mem_univ, mem_Ioi, ne_eq]
        obtain ⟨val, property⟩ := s₀
        simp_all only [finRangeTo]
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [lt_self_iff_false]
      intros contra
      apply this
      rw [sub_eq_zero, cosetEnum, cosetEnum] at contra
      simp only [Nat.succ_eq_add_one, finRangeTo, Fin.ofNat_eq_cast, Fin.val_natCast,
        Set.mem_setOf_eq, mul_eq_mul_left_iff] at contra
      rcases contra with contra | contra
      · simp only [FftDomain.subdomainNatReversed, FftDomain.subdomainNat] at contra
        have h := FftDomain.injective contra
        simp only [Fin.mk.injEq] at h
        ext
        exact (symm h)
      · rcases s₀ with ⟨s₀, hs₀⟩
        subst contra
        simp only [Nat.succ_eq_add_one, finRangeTo.eq_1, Fin.ofNat_eq_cast, Fin.val_natCast,
          evalDomainSigma, CosetFftDomain.subdomainNatReversed, CosetFftDomain.subdomainNat] at hs₀
        rw [CosetFftDomain.mem_coset_finset_iff_mem_coset_domain] at hs₀
        have hs₀ := CosetFftDomain.zero_is_not_in_domain hs₀
        simp at hs₀
    · simp
  apply @Matrix.invertibleOfDetInvertible

noncomputable def VDMInv (s₀ : evalDomainSigma s ω ↑i)
  (k_le_n : ∑ j', (s j').1 ≤ n) :
  Matrix (Fin (2 ^ (s i).1)) (cosetG n s s₀) 𝔽 :=
  Matrix.reindex (Equiv.refl _) (fin_equiv_coset n s s₀ k_le_n)
  (invertibleDomain n s s₀).invOf

lemma g_elem_zpower_iff_exists_nat {G : Type} [Group G] [Finite G] {gen g : G} :
    g ∈ Subgroup.zpowers gen ↔ ∃ n : ℕ, g = gen ^ n ∧ n < orderOf gen := by
  have := isOfFinOrder_of_finite gen
  refine ⟨fun h ↦ ?p₁, ?p₂⟩
  · obtain ⟨k, h⟩ := Subgroup.mem_zpowers_iff.1 h
    let k' := k % orderOf gen
    have pow_pos : 0 ≤ k' := by apply Int.emod_nonneg; simp [*]
    obtain ⟨n, h'⟩ : ∃ n : ℕ, n = k' := by rcases k' with k' | k' <;> [(use k'; grind); aesop]
    use n
    have : gen ^ n = gen ^ k := by have := zpow_mod_orderOf gen k; grind [zpow_natCast]
    have : n < orderOf gen := by zify; rw [h']; apply Int.emod_lt; simp [isOfFinOrder_of_finite gen]
    grind
  · grind [Subgroup.npow_mem_zpowers]

open Matrix in
noncomputable def f_succ'
  (f : evalDomainSigma s ω ↑i → 𝔽)
  (z : 𝔽) (k_le_n : ∑ j', ↑(s j') ≤ n)
  (s₀' : evalDomainSigma s ω (↑i + 1)) : 𝔽 :=
  have :
    ∃ s₀ : (ω.subdomainNatReversed (∑ j' ∈ finRangeTo _ (i.1), (s j').1)).toFinset,
      s₀.1 ^ (2 ^ (s i).1) = s₀'.1 := by
    rcases s₀' with ⟨s₀', hs₀'⟩
    simp only [Fin.val_natCast]
    simp only [evalDomainSigma] at hs₀' 
    rw [CosetFftDomain.mem_coset_finset_iff_mem_coset_domain] at hs₀'
    rw [CosetFftDomain.subdomainNatReversed_mem_of_eq 
      (ω := ω)
      (k := (∑ j' ∈ finRangeTo (k + 1) ↑i, (s j').1 + (s i).1))
      (by {
        rw [←sum_finRangeTo_add_one]
        rfl
    })] at hs₀'
    have h := CosetFftDomain.subdomainNatReversed_root_exists (ω := ω)
      (i := (∑ j' ∈ finRangeTo (k + 1) ↑i, ↑(s j')))
      (j := (s i).1)
      (by {
        trans (∑ j' ∈ finRangeTo _ (i.1 + 1), (s j').1)
        rw [sum_finRangeTo_add_one]
        rfl
        apply (swap le_trans) k_le_n
        apply Finset.sum_le_sum_of_subset (by simp)
      })
      hs₀' 
    rcases h with ⟨y, ⟨h1, h2⟩⟩
    exists ⟨y, by {
      rw [CosetFftDomain.mem_coset_finset_iff_mem_coset_domain]
      exact h1
    }⟩
  let s₀ := Classical.choose this
  (pows z _ *ᵥ VDMInv n s s₀ k_le_n *ᵥ Finset.restrict (cosetG n s s₀) f) ()

/-- This theorem asserts that given an appropriate codeword,
  `f` of an appropriate Reed-Solomon code, the result of honestly folding the corresponding
  polynomial is then itself a member of the next Reed-Solomon code.

  Corresponds to Claim 8.1 of [BCIKS20] -/
lemma fri_round_consistency_completeness
  {f : ReedSolomon.code
    (⟨fun x => x, by simp⟩ : evalDomainSigma s ω i ↪ 𝔽)
    (2 ^ (n - (∑ j' ∈ finRangeTo _ i, (s j' : ℕ))))}
  {z : 𝔽}
  (k_le_n : ∑ j', ↑(s j') ≤ n)
  :
  f_succ' n s f.val z k_le_n ∈
    (ReedSolomon.code
      (⟨fun x => x, by simp⟩ : (evalDomainSigma s ω (i.1 + 1)).toFinset ↪ 𝔽)
      (2 ^ (n - (∑ j' ∈ finRangeTo _ (i.1 + 1), (s j' : ℕ))))
    ).carrier
  := by sorry

end Completeness

section Soundness

variable (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)

/-- Affine space: {g | ∃ x : Fin t.succ → 𝔽, x 0 = 1 ∧ g = ∑ i, x i • f i  }
-/
def Fₛ {ι : Type} [Fintype ι] {t : ℕ} (f : Fin t.succ → (ι → 𝔽)) : AffineSubspace 𝔽 (ι → 𝔽) :=
  f 0 +ᵥ affineSpan 𝔽 (Finset.univ.image (f ∘ Fin.succ))

noncomputable def correlated_agreement_density {ι : Type} [Fintype ι]
  [Fintype 𝔽]
  (Fₛ : AffineSubspace 𝔽 (ι → 𝔽)) (V : Submodule 𝔽 (ι → 𝔽)) : ℝ :=
  haveI : Fintype Fₛ.carrier := Set.Finite.fintype (Set.toFinite _)
  haveI : Fintype V.carrier := Set.Finite.fintype (Set.toFinite _)
  let Fc := Fₛ.carrier.toFinset
  let Vc := V.carrier.toFinset  
  (Fc ∩ Vc).card / Fc.card

open Polynomial

noncomputable def oracleImpl
    (l : ℕ) (z : Fin (k + 1) → 𝔽) (f : (ω.subdomainNatReversed 0) → 𝔽) :
  QueryImpl
    ([]ₒ + ([Spec.FinalOracleStatement s ω]ₒ + [(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ))
    (OracleComp [(Spec.QueryRound.pSpec (ω := ω) l).Message]ₒ) := by
  intro q
  rcases q with i | q
  · exact PEmpty.elim i
  · rcases q with q | q
    · rcases q with ⟨i, dom⟩
      let f0 := Lagrange.interpolate Finset.univ (fun v => v.1) f
      let chals : List (Fin (k + 1) × 𝔽) :=
        ((List.finRange (k + 1)).map fun i => (i, z i)).take i.1
      let fi : 𝔽[X] := List.foldl (fun f (i, α) => Polynomial.foldNth (s i) f α) f0 chals
      let st : Spec.FinalOracleStatement (F := 𝔽) s ω i :=
        if h : i.1 = k + 1 then
          cast (by simp [Spec.FinalOracleStatement, h]) fi
        else
          cast
            (by {
              simp [Spec.FinalOracleStatement, h]
              rfl
            })
            (fun x : ω.subdomainNatReversed (∑ j' ∈ finRangeTo _ i.1, s j') => fi.eval x.1)
      exact pure <| (Spec.finalOracleStatementInterface s (ω := ω) i).answer st dom
    · rcases q with ⟨i, t⟩
      exact liftM <|
        cast
          (β := OracleQuery
            [(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ
            (([]ₒ +
                ([Spec.FinalOracleStatement s (ω := ω)]ₒ +
                  [(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ)).Range
              (Sum.inr (Sum.inr ⟨i, t⟩))))
          (by simp [OracleSpec.Range])
          (query (spec := [(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ) ⟨i, t⟩)

instance {l : ℕ} : ([(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ).Inhabited where
  inhabited_B := by
    intro i
    unfold Spec.QueryRound.pSpec MessageIdx at i
    have : i.1.1 = 0 := by omega
    have h := this ▸ i.1.2
    simp at h

instance {l : ℕ} : ([(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ).Fintype where
  fintype_B := by
    intro i
    unfold Spec.QueryRound.pSpec MessageIdx at i
    have : i.1.1 = 0 := by omega
    have h := this ▸ i.1.2
    simp at h

open ENNReal in
noncomputable def εC
    (𝔽 : Type) [Fintype 𝔽] (n : ℕ) {k : ℕ} (s : Fin (k + 1) → ℕ+) (m : ℕ) (ρ_sqrt : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal <|
      (m + (1 : ℚ)/2)^7 * (2^n)^2
        / ((2 * ρ_sqrt ^ 3) * (Fintype.card 𝔽))
      + (∑ i, 2 ^ (s i).1) * (2 * m + 1) * (2 ^ n + 1) / (Fintype.card 𝔽 * ρ_sqrt)

private abbrev fullChallengeProtocol (t l : ℕ) (ω : SmoothCosetFftDomain n 𝔽) :=
  (BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
    (Spec.pSpecFold k (ω := ω) s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ Spec.QueryRound.pSpec l (ω := ω))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ∀ j,
      Inhabited
        ((fullChallengeProtocol
            n
            (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge j) := by
  letI : ∀ j, Inhabited ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge j) := by
    infer_instance
  letI : ∀ j, Inhabited ((Spec.pSpecFold k (ω := ω) s).Challenge j) := by
    infer_instance
  letI : ∀ j, Inhabited ((Spec.FinalFoldPhase.pSpec 𝔽).Challenge j) := by
    infer_instance
  letI : ∀ j, Inhabited ((Spec.QueryRound.pSpec (ω := ω) l).Challenge j) := by
    infer_instance
  letI :
      ∀ j,
        Inhabited
          ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Challenge j) := by
    intro ⟨i, h⟩
    exact Fin.fappend₂ (A := Direction) (B := Type)
      (F := fun dir type => (h : dir = .V_to_P) → Inhabited type)
      (α₁ := (Spec.pSpecFold k s).dir)
      (β₁ := (Spec.FinalFoldPhase.pSpec 𝔽).dir)
      (α₂ := (Spec.pSpecFold k s).Type)
      (β₂ := (Spec.FinalFoldPhase.pSpec 𝔽).Type)
      (fun i h =>
        inferInstanceAs (Inhabited ((Spec.pSpecFold k s).Challenge ⟨i, h⟩)))
      (fun i h =>
        inferInstanceAs (Inhabited ((Spec.FinalFoldPhase.pSpec 𝔽).Challenge ⟨i, h⟩)))
      i h
  letI :
      ∀ j,
        Inhabited
          ((Spec.pSpecFold k (ω := ω) s ++ₚ
              Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                Spec.QueryRound.pSpec (ω := ω) l).Challenge j) := by
    intro ⟨i, h⟩
    exact Fin.fappend₂ (A := Direction) (B := Type)
      (F := fun dir type => (h : dir = .V_to_P) → Inhabited type)
      (α₁ := (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).dir)
      (β₁ := (Spec.QueryRound.pSpec (ω := ω) l).dir)
      (α₂ := (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Type)
      (β₂ := (Spec.QueryRound.pSpec (ω := ω) l).Type)
      (fun i h =>
        inferInstanceAs
          (Inhabited
            ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Challenge
              ⟨i, h⟩)))
      (fun i h =>
        inferInstanceAs (Inhabited ((Spec.QueryRound.pSpec (ω := ω) l).Challenge ⟨i, h⟩)))
      i h
  intro ⟨i, h⟩
  exact Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .V_to_P) → Inhabited type)
    (α₁ := (BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).dir)
    (β₁ := (Spec.pSpecFold (ω := ω) k s ++ₚ
      Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
        Spec.QueryRound.pSpec (ω := ω) l).dir)
    (α₂ := (BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Type)
    (β₂ := (Spec.pSpecFold (ω := ω) k s ++ₚ
      Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
        Spec.QueryRound.pSpec (ω := ω) l).Type)
    (fun i h =>
      inferInstanceAs (Inhabited ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge ⟨i, h⟩)))
    (fun i h =>
      inferInstanceAs
        (Inhabited
          ((Spec.pSpecFold (ω := ω) k s ++ₚ
              Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                Spec.QueryRound.pSpec (ω := ω) l).Challenge
            ⟨i, h⟩)))
    i h

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ∀ j,
      Fintype
        ((fullChallengeProtocol
            n
            (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge j) := by
  letI : ∀ j, Fintype ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge j) := by
    infer_instance
  letI : ∀ j, Fintype ((Spec.pSpecFold (ω := ω) k s).Challenge j) := by
    infer_instance
  letI : ∀ j, Fintype ((Spec.FinalFoldPhase.pSpec 𝔽).Challenge j) := by
    infer_instance
  letI : ∀ j, Fintype ((Spec.QueryRound.pSpec (ω := ω) l).Challenge j) := by
    infer_instance
  letI :
      ∀ j,
        Fintype
          ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Challenge j) := by
    intro ⟨i, h⟩
    exact Fin.fappend₂ (A := Direction) (B := Type)
      (F := fun dir type => (h : dir = .V_to_P) → Fintype type)
      (α₁ := (Spec.pSpecFold (ω := ω) k s).dir)
      (β₁ := (Spec.FinalFoldPhase.pSpec 𝔽).dir)
      (α₂ := (Spec.pSpecFold (ω := ω) k s).Type)
      (β₂ := (Spec.FinalFoldPhase.pSpec 𝔽).Type)
      (fun i h =>
        inferInstanceAs (Fintype ((Spec.pSpecFold (ω := ω) k s).Challenge ⟨i, h⟩)))
      (fun i h =>
        inferInstanceAs (Fintype ((Spec.FinalFoldPhase.pSpec 𝔽).Challenge ⟨i, h⟩)))
      i h
  letI :
      ∀ j,
        Fintype
          ((Spec.pSpecFold (ω := ω) k s ++ₚ
              Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                Spec.QueryRound.pSpec (ω := ω) l).Challenge j) := by
    intro ⟨i, h⟩
    exact Fin.fappend₂ (A := Direction) (B := Type)
      (F := fun dir type => (h : dir = .V_to_P) → Fintype type)
      (α₁ := (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).dir)
      (β₁ := (Spec.QueryRound.pSpec (ω := ω) l).dir)
      (α₂ := (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Type)
      (β₂ := (Spec.QueryRound.pSpec (ω := ω) l).Type)
      (fun i h =>
        inferInstanceAs
          (Fintype
            ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Challenge
              ⟨i, h⟩)))
      (fun i h =>
        inferInstanceAs (Fintype ((Spec.QueryRound.pSpec (ω := ω) l).Challenge ⟨i, h⟩)))
      i h
  intro ⟨i, h⟩
  exact Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .V_to_P) → Fintype type)
    (α₁ := (BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).dir)
    (β₁ := (Spec.pSpecFold k (ω := ω) s ++ₚ
      Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
        Spec.QueryRound.pSpec (ω := ω) l).dir)
    (α₂ := (BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Type)
    (β₂ := (Spec.pSpecFold k (ω := ω) s ++ₚ
      Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
        Spec.QueryRound.pSpec l (ω := ω)).Type)
    (fun i h =>
      inferInstanceAs (Fintype ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge ⟨i, h⟩)))
    (fun i h =>
      inferInstanceAs
        (Fintype
          ((Spec.pSpecFold k (ω := ω) s ++ₚ
              Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                Spec.QueryRound.pSpec l (ω := ω)).Challenge
            ⟨i, h⟩)))
    i h

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ([(fullChallengeProtocol
        n (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge]ₒ).Inhabited where
  inhabited_B := by
    intro q
    rcases q with ⟨i, u⟩
    cases u
    change Inhabited
      ((fullChallengeProtocol n (𝔽 := 𝔽) (k := k) (s := s) t l ω).Challenge i)
    infer_instance

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ([(fullChallengeProtocol
        n (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge]ₒ).Fintype where
  fintype_B := by
    intro q
    rcases q with ⟨i, u⟩
    cases u
    change Fintype
      ((fullChallengeProtocol n (𝔽 := 𝔽) (k := k) (s := s) t l (ω := ω)).Challenge i)
    infer_instance

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ∀ j, Inhabited
      (((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
          (Spec.pSpecFold k (ω := ω) s ++ₚ
            Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec (ω := ω) l)).Challenge j) := by
  simpa [fullChallengeProtocol] using
    (inferInstance :
      ∀ j,
        Inhabited
          ((fullChallengeProtocol
              n (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge j))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ∀ j, Fintype
      (((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
          (Spec.pSpecFold (ω := ω) k s ++ₚ
            Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec (ω := ω) l)).Challenge j) := by
  simpa [fullChallengeProtocol] using
    (inferInstance :
      ∀ j,
        Fintype
          ((fullChallengeProtocol
              n (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge j))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ([((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
        (Spec.pSpecFold (ω := ω) k s ++ₚ
          Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
            Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Inhabited := by
  infer_instance

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ([((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
        (Spec.pSpecFold (ω := ω) k s ++ₚ
          Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
            Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Fintype := by
  infer_instance

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ([]ₒ +
      [((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
          (Spec.pSpecFold (ω := ω) k s ++ₚ
            Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Inhabited where
  inhabited_B := by
    intro q
    cases q with
    | inl q => exact PEmpty.elim q
    | inr q =>
        simpa using
          (inferInstance :
            Inhabited
              (([((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
                  (Spec.pSpecFold (ω := ω) k s ++ₚ
                    Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                      Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Range q))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ([]ₒ +
      [((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
          (Spec.pSpecFold (ω := ω) k s ++ₚ
            Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Fintype where
  fintype_B := by
    intro q
    cases q with
    | inl q => exact PEmpty.elim q
    | inr q =>
        simpa using
          (inferInstance :
            Fintype
              (([((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
                  (Spec.pSpecFold (ω := ω) k s ++ₚ
                    Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                      Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Range q))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    HasEvalPMF
      (OracleComp
        ([]ₒ +
          [((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
              (Spec.pSpecFold (ω := ω) k s ++ₚ
                Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                  Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ)) := by
  infer_instance
--HasEvalSPMF
--       (OptionT
--         (OracleComp
--           ([]ₒ +
--             [(BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t ++ₚ
--                   (Spec.pSpecFold k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ Spec.QueryRound.pSpec l)).Challenge]ₒ)))
--
noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    HasEvalSPMF
      (OptionT
        (OracleComp
          ([]ₒ +
            [((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
                (Spec.pSpecFold (ω := ω) k s ++ₚ
                  Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                    Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ))) := by
  infer_instance

open ENNReal in
/-- Corresponds to Claim 8.2 of [BCIKS20] -/
lemma fri_query_soundness
  {t : ℕ}
  {α : ℝ}
  (f : Fin t.succ → (ω.subdomainNatReversed 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomainNatReversed 0 ↪ 𝔽) (2 ^ n))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  :
    let ρ_sqrt :=
      ReedSolomon.sqrtRate
        (2 ^ n)
        (⟨fun x => x, by simp⟩ : ω.subdomainNatReversed 0 ↪ 𝔽)
    let α0 : ℝ≥0∞ := ENNReal.ofReal (max α (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0)))))
    let εQ  (x : Fin t → 𝔽)
            (z : Fin (k + 1) → 𝔽) :=
      Pr_{let samp ←$ᵖ (ω.subdomainNatReversed 0)}[
        Pr[
          fun _ => True |
          (
            (do
              simulateQ
                (oracleImpl n (ω := ω) s 1 z (fun v ↦ f 0 v + ∑ i, x i * f i.succ v))
                ((
                    Fri.Spec.QueryRound.queryVerifier
                      (ω := ω)
                      (n := n) s
                      (
                        by
                          apply Spec.round_bound (d := d)
                          transitivity
                          · exact domain_size_cond
                          · apply pow_le_pow (by decide) (by decide)
                            simp
                      )
                      1
                  ).verify
                    z
                    (fun i =>
                      by
                        simpa only
                          [
                            Spec.QueryRound.pSpec, Challenge,
                            show i.1 = 0 by omega, Fin.isValue,
                            Fin.vcons_zero
                          ] using fun _ => samp
                    )
                )
            )
          )]
        = 1
      ]
    Pr_{let x ←$ᵖ (Fin t → 𝔽); let z ←$ᵖ (Fin (k + 1) → 𝔽)}[ εQ x z > α0 ] ≤ εC 𝔽 n s m ρ_sqrt
  := by
  sorry

-- set_option diagnostics true
  -- refine @OracleSpec.instFiniteRangeSumAppend (h₁ := inferInstance) (h₂ := ?_) ..
  -- refine @instFinRangeOfAppend _ _ _ _ ?_ ?_
  -- · unfold BatchedFri.Spec.BatchingRound.batchSpec Challenge OracleInterface.toOracleSpec
  --   simp only [Fin.vcons_fin_zero, Nat.reduceAdd, ChallengeIdx]
  --   constructor
  --   · intros i
  --     unfold OracleSpec.range
  --     simp only
  --     rcases i with ⟨i, h⟩
  --     have : i = 0 := by omega
  --     subst this
  --     simp
  --     unfold OracleInterface.Response challengeOracleInterface
  --     simp only
  --     unfold Challenge
  --     simp
  --     haveI : Inhabited 𝔽 := ⟨0⟩
  --     infer_instance
  --   · intros i
  --     unfold OracleSpec.range
  --     simp only
  --     rcases i with ⟨i, h⟩
  --     have : i = 0 := by omega
  --     subst this
  --     simp
  --     unfold OracleInterface.Response challengeOracleInterface
  --     simp only
  --     unfold Challenge
  --     simp
  --     haveI : Inhabited 𝔽 := ⟨0⟩
  --     infer_instance
  -- · refine @instFinRangeOfAppend _ _ _ _ ?_ ?_
  --   · refine @instFinRangeOfAppend _ _ _ _ ?_ ?_
  --     unfold Spec.pSpecFold Challenge OracleInterface.toOracleSpec
  --     constructor
  --     · intros i
  --       unfold OracleSpec.range
  --       simp only
  --       rcases i with ⟨i, h⟩
  --       have : i = 0 := by omega
  --       subst this
  --       simp
  --       unfold OracleInterface.Response challengeOracleInterface
  --       simp only
  --       unfold Challenge
  --       simp
  --       haveI : Inhabited 𝔽 := ⟨0⟩
  --       infer_instance








  -- refine { range_inhabited' := ?_, range_fintype' := ?_ }
  -- refine fun i ↦ ?_
  -- rcases i with i | i
  -- · rcases i
  -- ·

open ENNReal in
/-- Corresponds to Claim 8.3 of [BCIKS20] -/
lemma fri_soundness
  {t l m : ℕ}
  (f : Fin t.succ → (ω → 𝔽))
  (m_ge_3 : m ≥ 3)
  :
    let ρ_sqrt :=
      ReedSolomon.sqrtRate
        (2 ^ n)
        (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
    let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
    (∃ prov : OracleProver (WitOut := Unit) ..,
        Pr[fun _ => True |
          OracleReduction.run () f ()
            ⟨
              prov,
              (BatchedFri.Spec.batchedFRIreduction (ω := ω) (n := n) k s d domain_size_cond l t).verifier
            ⟩
        ] > εC 𝔽 n s m ρ_sqrt + α ^ l) →
      Code.jointAgreement
        (F := 𝔽)
        (κ := Fin t.succ)
        (ι := ω)
        (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (2 ^ n)).carrier)
        (δ := 1 - α)
        (W := f) := by
  sorry

end Soundness

end Fri
end Fri
