/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Reduction

/-!
  # Sumcheck bridge — point claims to hypercube sums — skeleton (zero-round)

  Zero-round bridge from the zero-check's *point-evaluation* claims to the *initial sumcheck*
  claims consumed by the round loop ([NOZ26] §4.3, "finish the proof using sumcheck protocols"):

  * `relIn = relZeroCheckE` — `H₀^{w̃}(τ₀) = 0 ∧ H_α^{w̃}(τ_α) = 0` at the derived Kronecker
    points;
  * `relOut = roundRelE 0` — `∑_{x ∈ {0,1}^{m₀}} F_{0,τ₀}(x) = 0` and
    `∑_{x ∈ {0,1}^{m₀}} F_{α,τ_α}(x) = a`, where the initial linear target
    `a := zcTargetAlpha = ∑ᵢ eq̃(τ_α, i)·ŷᵢ(α)` is computed by the verifier from the statement
    alone.

  The statement map installs the empty challenge prefix and the initial target pair
  `(0, zcTargetAlpha)`. The bridge is pure reshaping — the two directions are the algebraic
  identities `∑ F_{0,τ₀} = H₀(τ₀)` and `∑ F_{α,τ_α} = H_α(τ_α) + zcTargetAlpha`
  (`sum_sumcheckPolyZero` / `sum_sumcheckPolyAlpha`, `ZeroCheck/Constraints.lean`) — so the
  only sorried piece is the pull-back through those (themselves sorried F5) identities.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {E : Type} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₀ m₁ : ℕ) (bound rBound : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The bridge's statement map: install the empty challenge prefix and the initial target pair
`(0, zcTargetAlpha)` on the zero-check statement. -/
def toRoundStatement {TCom : Type} (φF : ZMod q →+* F)
    (s : ZeroCheckStatement Φ TCom F n μ) : RoundStatement Φ TCom F n μ 0 :=
  ⟨s, fun j => j.elim0, 0, zcTargetAlpha Φ m₁ φF s.rlin s.α (kroneckerPoint m₁ s.seedα)⟩

/-- The corrected bridge's statement map.  It retains the independently sampled scalar-round
points and installs the empty sumcheck challenge prefix and initial target pair. -/
def nestedToRoundStatement {TCom : Type} (φF : ZMod q →+* F)
    (s : NestedZeroCheckStatement Φ TCom F n μ m₀ m₁) :
    NestedRoundStatement Φ TCom F n μ m₀ m₁ 0 :=
  ⟨s, fun j => j.elim0, 0, zcTargetAlpha Φ m₁ φF s.rlin s.α s.τα⟩

omit [NeZero q] in
/-- Pull the corrected initial sumcheck claims back to the direct computable point claims.
No Kronecker seed or curve occurs in this bridge. -/
theorem mem_relNestedZeroCheckE_of_nestedRoundRelE
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ)
    (s : NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁)
    (w : LiftedWitness Φ μ n ⊕ E)
    (h : (nestedToRoundStatement Φ m₀ m₁ φF s, w) ∈
      nestedRoundRelE Φ m₀ m₁ bound rBound K φF b 0) :
    (s, w) ∈ relNestedZeroCheckE Φ m₀ m₁ bound rBound K φF b := by
  rcases w with w | e
  · rw [nestedRoundRelE, Set.mem_withEscape_inl, nestedRoundRel,
      Set.mem_setOf_eq] at h
    rw [relNestedZeroCheckE, Set.mem_withEscape_inl, relNestedZeroCheck,
      Set.mem_setOf_eq]
    rcases h with ⟨hCom, hShort, hZero, hAlpha, hBound⟩
    change K.com w = s.t at hCom
    change liftShort Φ bound rBound w at hShort
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
      rw [sum_sumcheckPolyAlpha' Φ m₀ m₁ φF b s.rlin s.α s.τα w] at hAlpha
      exact add_eq_right.mp hAlpha
  · rw [nestedRoundRelE, Set.mem_withEscape_inr] at h
    rw [relNestedZeroCheckE, Set.mem_withEscape_inr]
    exact h

/-- Zero-round sumcheck bridge for the corrected scalar-round zero-check. -/
def nestedSumcheckBridgePackage (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    CWSSPackage init impl
      (NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁) (LiftedWitness Φ μ n ⊕ E)
      (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ 0) (LiftedWitness Φ μ n ⊕ E)
      (!p[] : ProtocolSpec 0) where
  verifier := ReduceClaim.verifier oSpec (nestedToRoundStatement Φ m₀ m₁ φF)
  struct := CWSSStructure.ofIsEmpty
  relIn := relNestedZeroCheckE Φ m₀ m₁ bound rBound K φF b
  relOut := nestedRoundRelE Φ m₀ m₁ bound rBound K φF b 0
  isPure :=
    ⟨fun stmt _ => nestedToRoundStatement Φ m₀ m₁ φF stmt, fun _ _ => rfl⟩
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSound
    (relIn := relNestedZeroCheckE Φ m₀ m₁ bound rBound K φF b)
    (relOut := nestedRoundRelE Φ m₀ m₁ bound rBound K φF b 0)
    (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
    (mem_relNestedZeroCheckE_of_nestedRoundRelE Φ m₀ m₁ bound rBound K φF b)

/-- **Sum-to-point pull-back** (the bridge's `hRel`): the initial hypercube-sum claims at the
installed targets imply the zero-check's point-evaluation claims, through the batching
identities `∑ F_{0,τ₀} = H₀(τ₀)` and `∑ F_{α,τ_α} = H_α(τ_α) + zcTargetAlpha`. Escapes pass
through; the bound-sanity conjunct is shared verbatim.

**Sorried** (a corollary of the sorried F5 identities `sum_sumcheckPolyZero` /
`sum_sumcheckPolyAlpha`, plus `challenges`-uniqueness `Fin 0 → F`). -/
theorem mem_relZeroCheckE_of_roundRelE
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ)
    (s : ZeroCheckStatement Φ K.TCom F n μ) (w : LiftedWitness Φ μ n ⊕ E)
    (h : (toRoundStatement Φ m₁ φF s, w) ∈ roundRelE Φ m₀ m₁ bound rBound K φF b 0) :
    (s, w) ∈ relZeroCheckE Φ m₀ m₁ bound rBound K φF b := by
  sorry

/-- **The sumcheck bridge as a `CWSSPackage`**: zero-round `ReduceClaim` at
`mapStmt := toRoundStatement`, reducing `relZeroCheckE` to the round-`0` seam `roundRelE 0`
with no soundness error. -/
def sumcheckBridgePackage (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound rBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    CWSSPackage init impl
      (ZeroCheckStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n ⊕ E)
      (RoundStatement Φ K.TCom F n μ 0) (LiftedWitness Φ μ n ⊕ E)
      (!p[] : ProtocolSpec 0) where
  verifier := ReduceClaim.verifier oSpec (toRoundStatement Φ m₁ φF)
  struct := CWSSStructure.ofIsEmpty
  relIn := relZeroCheckE Φ m₀ m₁ bound rBound K φF b
  relOut := roundRelE Φ m₀ m₁ bound rBound K φF b 0
  isPure := ⟨fun stmt _ => toRoundStatement Φ m₁ φF stmt, fun _ _ => rfl⟩
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSound
    (relIn := relZeroCheckE Φ m₀ m₁ bound rBound K φF b)
    (relOut := roundRelE Φ m₀ m₁ bound rBound K φF b 0)
    (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
    (mem_relZeroCheckE_of_roundRelE Φ m₀ m₁ bound rBound K φF b)

end ArkLib.Lattices.Ajtai.InnerOuter
