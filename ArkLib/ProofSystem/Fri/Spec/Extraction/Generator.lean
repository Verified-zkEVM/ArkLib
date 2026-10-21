/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.Access
public import ArkLib.ToCompPoly.Univariate.ArithmeticPower
public import ArkLib.Data.Domain.CosetFftDomain.Ops
public import ArkLib.Data.Domain.FftDomain.Subdomain

/-!
# Charged generation of FRI query points

The backend initializes a smooth coset domain from at most two domain reads. Subsequent initial
points, folding projections, and folding blocks use explicit arithmetic instructions. Reference
domain expressions in certificates occur only in erased proofs.
-/

@[expose] public section

namespace Domain

variable {F : Type} [Field F] {n : ℕ}

private theorem fft_subdomain_apply (ω : SmoothFftDomain n F) (i : ℕ)
    (z : Fin (2 ^ (n - i))) :
    (FftDomainClass.subdomain ω i) z =
      ω (CosetFftDomainClass.subdomain_embed i z) := by
  unfold FftDomainClass.subdomain
  rw [CosetFftDomainClass.eval_toFftDomain]
  simp [CosetFftDomainClass.subdomain_apply, CosetFftDomainClass.mkSubgroupUnit,
    CosetFftDomainClass.subdomain_embed_zero, FftDomainClass.apply_zero_eq_one]

/-- Values in a normalized subdomain are fixed powers of the original domain ratio. -/
private theorem normalized_subdomain_apply_eq_ratio_pow (ω : SmoothCosetFftDomain n F)
    (i : ℕ) (z : Fin (2 ^ (n - i))) :
    (ω.toFftDomain.subdomain i) z =
      (ω 1 * (ω 0)⁻¹) ^ (2 ^ i * z.val) := by
  rw [fft_subdomain_apply, FftDomainClass.apply_eq_pow_of_generator,
    CosetFftDomainClass.eval_toFftDomain, mul_comm ((ω 0)⁻¹)]
  congr 1
  by_cases h : n ≤ i
  · have hz : z.val = 0 := by
      simpa [Nat.sub_eq_zero_of_le h] using z.isLt
    simp [CosetFftDomainClass.subdomain_embed, h, hz]
  · simp [CosetFftDomainClass.subdomain_embed, h]

end Domain

namespace Fri.Spec.Extractor

open Domain OracleComp OracleSpec CompPoly

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+)

/-- The two field values used to generate a smooth coset domain. -/
structure Generator {K : Type} [Field K] {m : ℕ} (ω : SmoothCosetFftDomain m K) where
  point0 : K
  ratio : K
  point0_eq : point0 = ω 0
  ratio_eq : ratio = ω 1 * (ω 0)⁻¹

private theorem domain_apply_eq {K : Type} [Field K] {m : ℕ}
    (ω : SmoothCosetFftDomain m K) (z : Fin (2 ^ m)) :
    ω z = ω 0 * (ω 1 * (ω 0)⁻¹) ^ z.val := by
  have h := FftDomainClass.apply_eq_pow_of_generator
    (ω := CosetFftDomainClass.toFftDomain ω) z
  rw [CosetFftDomainClass.eval_toFftDomain, CosetFftDomainClass.eval_toFftDomain] at h
  calc
    ω z = ω 0 * ((ω 0)⁻¹ * ω z) :=
      (mul_inv_cancel_left₀ (CosetFftDomainClass.ne_zero ω 0) _).symm
    _ = ω 0 * ((ω 0)⁻¹ * ω 1) ^ z.val := congrArg (ω 0 * ·) h
    _ = ω 0 * (ω 1 * (ω 0)⁻¹) ^ z.val := by rw [mul_comm ((ω 0)⁻¹)]

/-- Read a domain value through its charged immutable access instruction. -/
def readDomain (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (z : Fin (2 ^ n)) : OracleComp (InstructionSpec s o α) {x : F // x = ω z} :=
  liftM (OracleSpec.query (spec := InstructionSpec s o α) (.inr (.domainRead z)))

/-- Initialize the generator from two charged domain accesses, or one for a singleton domain. -/
def initGenerator (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k) :
    OracleComp (InstructionSpec s o α) (Generator ω) := do
  let a ← readDomain s o α 0
  if hn : n = 0 then
    pure ⟨a.val, 1, a.property, by
      subst n
      have h1 : (1 : Fin (2 ^ 0)) = 0 := rfl
      rw [h1, mul_inv_cancel₀ (CosetFftDomainClass.ne_zero ω 0)]⟩
  else
    have hN : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
    let z₁ : Fin (2 ^ n) := ⟨1, hN⟩
    let b ← readDomain s o α z₁
    let aInv ← liftComp (Arithmetic.inv a.val) _
    let g ← liftComp (Arithmetic.mul b.val aInv.val) _
    pure ⟨a.val, g.val, a.property, by
      rw [g.property, aInv.property, a.property, b.property]
      have hz : z₁ = (1 : Fin (2 ^ n)) := by
        apply Fin.ext
        simp [z₁, Nat.mod_eq_of_lt hN]
      rw [hz]⟩

/-- Generate a domain point using charged binary powers and one final multiplication. -/
def initialPoint (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (gen : Generator ω) (z : Fin (2 ^ n)) :
    OracleComp (InstructionSpec s o α) {x : F // x = ω z} := do
  let p ← liftComp (Arithmetic.powerBits gen.ratio n z.val z.isLt) _
  let x ← liftComp (Arithmetic.mul gen.point0 p.val) _
  pure ⟨x.val, by
    rw [x.property, p.property, gen.point0_eq, gen.ratio_eq]
    exact (domain_apply_eq ω z).symm⟩

end Fri.Spec.Extractor

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+)

private theorem round_le (hs : (∑ j, (s j).val) ≤ n) (i : Fin (k + 1)) :
    (s i).val ≤ n :=
  (Finset.single_le_sum (f := fun j ↦ (s j).val) (by simp) (by simp)).trans hs

/-- The verifier's block node at an explicit block index, used as a reference in certificates. -/
def blockNode (hs : (∑ j, (s j).val) ≤ n) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset) (j : Fin (2 ^ (s i).val)) :
    (ω.subdomain (foldingPrefix s i.castSucc)).toFinset :=
  (QueryRound.queryBlock s hs i x).get
    (j.cast (QueryRound.queryBlock_length s hs i x).symm)

omit [Fintype F] in
private theorem blockNode_val (hs : (∑ j, (s j).val) ≤ n) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset) (j : Fin (2 ^ (s i).val)) :
    (blockNode s hs i x j).val =
      (ω 1 * (ω 0)⁻¹) ^ (2 ^ (n - (s i).val) * j.val) *
        (QueryRound.queryPoint s hs i x).val := by
  have hi := round_le s hs i
  have hsize : 2 ^ (s i).val = 2 ^ (n - (n - (s i).val)) := by
    rw [Nat.sub_sub_self hi]
  let j' : Fin (2 ^ (n - (n - (s i).val))) := j.cast hsize
  have hroot := normalized_subdomain_apply_eq_ratio_pow ω (n - (s i).val) j'
  convert congrArg (fun a : F ↦ a * (QueryRound.queryPoint s hs i x).val) hroot using 1 <;>
    simp only [blockNode, QueryRound.queryBlock, FftDomain.toList, j',
      List.get_eq_getElem, List.getElem_map, List.getElem_finRange, Fin.val_cast]
  congr 2

/-- The cached multiplicative generator for one folding block. -/
structure RoundGenerator {K : Type} [Field K] {m r : ℕ}
    (s : Fin (r + 1) → ℕ+) {ω : SmoothCosetFftDomain m K}
    (gen : Generator ω) (i : Fin (r + 1)) where
  root : K
  root_eq : root = gen.ratio ^ (2 ^ (m - (s i).val))

/-- Compute one folding-block generator using charged squarings. -/
def initRoundGenerator (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (gen : Generator ω) (i : Fin (k + 1)) :
    OracleComp (InstructionSpec s o α) (RoundGenerator s gen i) := do
  let r ← liftComp (Arithmetic.squareIter gen.ratio (n - (s i).val)) _
  pure ⟨r.val, r.property⟩

/-- Generate one block point without evaluating the original domain function. -/
def generateBlockNode (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : FinalStatement F k)
    (gen : Generator ω) (i : Fin (k + 1)) (roundGen : RoundGenerator s gen i)
    (x : (ω.subdomain 0).toFinset)
    (projected : {a : F // a = (QueryRound.queryPoint s hs i x).val})
    (j : Fin (2 ^ (s i).val)) :
    OracleComp (InstructionSpec s o α)
      {q : (ω.subdomain (foldingPrefix s i.castSucc)).toFinset //
        q = blockNode s hs i x j} := do
  let r ← liftComp (Arithmetic.powerBits roundGen.root (s i).val j.val j.isLt) _
  let a ← liftComp (Arithmetic.mul r.val projected.val) _
  have ha : a.val = (blockNode s hs i x j).val := by
    rw [a.property, r.property, roundGen.root_eq, ← pow_mul, projected.property,
      gen.ratio_eq, blockNode_val]
  pure ⟨⟨a.val, by rw [ha]; exact (blockNode s hs i x j).property⟩,
    Subtype.ext ha⟩

end Fri.Spec.Extractor
