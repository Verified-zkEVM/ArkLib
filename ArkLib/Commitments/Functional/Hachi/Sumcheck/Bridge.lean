/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas, Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Reduction

/-!
  # Sumcheck bridge — point claims to hypercube sums (zero-round)

  Zero-round bridge from the zero-check's *point-evaluation* claims to the *initial sumcheck*
  claims consumed by the round loop:

  * `relIn = relNestedZeroCheck` — `H₀^{w̃}(τ₀) = 0 ∧ H_α^{w̃}(τα) = 0` at the direct points;
  * `relOut = nestedRoundRel 0` — `∑_{x ∈ {0,1}^{m₀}} F_{0,τ₀}(x) = 0` and
    `∑_{x ∈ {0,1}^{m₀}} F_{α,τ_α}(x) = a`, where the initial linear target
    `a := zcTargetAlpha = ∑ᵢ eq̃(τ_α, i)·ŷᵢ(α)` is computed by the verifier from the
    statement alone.

  The statement map installs the empty challenge prefix and the initial target pair
  `(0, zcTargetAlpha)`. The bridge is pure reshaping: soundness is the pair of algebraic
  identities `∑ F_{0,τ₀} = H₀(τ₀)` and `∑ F_{α,τ_α} = H_α(τ_α) + zcTargetAlpha`
  (`sum_sumcheckPolyZero` / `sum_sumcheckPolyAlpha`, `ZeroCheck/Constraints.lean`).

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₀ m₁ : ℕ) (bound ρBound : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The bridge's statement map. It retains the independently sampled scalar-round
points and installs the empty sumcheck challenge prefix and initial target pair. -/
def nestedToRoundStatement {TCom : Type} (φF : ZMod q →+* F)
    (s : NestedZeroCheckStatement Φ TCom F n μ m₀ m₁) :
    NestedRoundStatement Φ TCom F n μ m₀ m₁ 0 :=
  ⟨s, fun j => j.elim0, 0, zcTargetAlpha Φ m₁ φF s.rlin s.α s.τα⟩

omit [NeZero q] in
/-- Sum-to-point pull-back: the initial hypercube-sum claims at the installed targets imply
the zero-check's direct point-evaluation claims, through the identities
`∑ F_{0,τ₀} = H₀(τ₀)` and `∑ F_{α,τ_α} = H_α(τ_α) + zcTargetAlpha`. The commitment,
shortness and bound-sanity conjuncts are shared verbatim. -/
theorem mem_relNestedZeroCheck_of_nestedRoundRel
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ)
    (hd : 0 < Φ.φ.natDegree) (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (s : NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁)
    (w : LiftedWitness Φ μ n)
    (h : (nestedToRoundStatement Φ m₀ m₁ φF s, w) ∈
      nestedRoundRel Φ m₀ m₁ bound ρBound K φF b 0) :
    (s, w) ∈ relNestedZeroCheck Φ m₀ m₁ bound ρBound K φF b := by
  rw [nestedRoundRel, Set.mem_ofPred_eq] at h
  rw [relNestedZeroCheck, Set.mem_ofPred_eq]
  rcases h with ⟨hCom, hShort, hZero, hAlpha, hBound⟩
  change K.com w = s.t at hCom
  change hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b s.τ₀ w) 0
    (fun j => j.elim0) = 0 at hZero
  change hypercubeSum m₀ (sumcheckPolyAlpha Φ m₀ m₁ φF b s.rlin s.α s.τα w) 0
    (fun j => j.elim0) = zcTargetAlpha Φ m₁ φF s.rlin s.α s.τα at hAlpha
  change bound ≤ s.rlin.bound at hBound
  refine ⟨hCom, hShort, ?_, ?_, hBound⟩
  · rw [hZero_eval_eq]
    rw [sum_sumcheckPolyZero' Φ m₀ φF b s.τ₀ w] at hZero
    exact hZero
  · rw [hAlpha_eval_eq]
    rw [sum_sumcheckPolyAlpha' Φ m₀ m₁ φF b s.rlin s.α s.τα w hd hμn] at hAlpha
    exact add_eq_right.mp hAlpha

/-- The sumcheck bridge as a (plain) `CWSSPackage`: zero-round `ReduceClaim` at
`mapStmt := nestedToRoundStatement`, reducing `relNestedZeroCheck` to the round-`0`
`nestedRoundRel`. -/
noncomputable def nestedSumcheckBridgePackage (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ)
    (hd : 0 < Φ.φ.natDegree) (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    CWSSPackage init impl
      (NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁) (LiftedWitness Φ μ n)
      (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ 0) (LiftedWitness Φ μ n)
      (!p[] : ProtocolSpec 0) where
  verifier := ReduceClaim.verifier oSpec (nestedToRoundStatement Φ m₀ m₁ φF)
  struct := CWSSStructure.ofIsEmpty
  relIn := relNestedZeroCheck Φ m₀ m₁ bound ρBound K φF b
  relOut := nestedRoundRel Φ m₀ m₁ bound ρBound K φF b 0
  isPure :=
    ⟨fun stmt _ => nestedToRoundStatement Φ m₀ m₁ φF stmt, fun _ _ => rfl⟩
  extractor := ReduceClaim.treeExtractor (mapStmt := nestedToRoundStatement Φ m₀ m₁ φF)
    (nestedRoundRel Φ m₀ m₁ bound ρBound K φF b 0) (fun _ w => w) CWSSStructure.ofIsEmpty
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSoundWith
    (relIn := relNestedZeroCheck Φ m₀ m₁ bound ρBound K φF b)
    (relOut := nestedRoundRel Φ m₀ m₁ bound ρBound K φF b 0)
    (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
    (mem_relNestedZeroCheck_of_nestedRoundRel Φ m₀ m₁ bound ρBound K φF b hd hμn)

end ArkLib.Lattices.Ajtai.InnerOuter
