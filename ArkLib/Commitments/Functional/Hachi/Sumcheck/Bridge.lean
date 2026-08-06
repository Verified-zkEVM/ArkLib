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

  * `relIn = relZeroCheck` — `H₀^{w̃}(τ₀) = 0 ∧ H_α^{w̃}(τ_α) = 0` at the derived Kronecker
    points;
  * `relOut = roundRel 0` — `∑_{x ∈ {0,1}^{m₀}} F_{0,τ₀}(x) = 0` and
    `∑_{x ∈ {0,1}^{m₀}} F_{α,τ_α}(x) = a`, where the initial linear target
    `a := zcTargetAlpha = ∑ᵢ eq̃(τ_α, i)·ŷᵢ(α)` is computed by the verifier from the statement
    alone.

  The statement map installs the empty challenge prefix and the initial target pair
  `(0, zcTargetAlpha)`. The bridge is pure reshaping — the two directions are the algebraic
  identities `∑ F_{0,τ₀} = H₀(τ₀)` and `∑ F_{α,τ_α} = H_α(τ_α) + zcTargetAlpha`
  (`sum_sumcheckPolyZero` / `sum_sumcheckPolyAlpha`, `ZeroCheck/Constraints.lean`) — so the
  only sorried piece is the pull-back through those (themselves sorried) identities.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {F : Type} [Field F]
variable (m₀ m₁ : ℕ) (bound ρBound : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The bridge's statement map: install the empty challenge prefix and the initial target pair
`(0, zcTargetAlpha)` on the zero-check statement. -/
noncomputable def toRoundStatement {TCom : Type} (φF : ZMod q →+* F)
    (s : ZeroCheckStatement Φ TCom F n μ) : RoundStatement Φ TCom F n μ 0 :=
  ⟨s, fun j => j.elim0, 0, zcTargetAlpha Φ m₁ φF s.rlin s.α (kroneckerPoint m₁ s.seedα)⟩

/-- **Sum-to-point pull-back** (the bridge's `hRel`): the initial hypercube-sum claims at the
installed targets imply the zero-check's point-evaluation claims, through the batching
identities `∑ F_{0,τ₀} = H₀(τ₀)` and `∑ F_{α,τ_α} = H_α(τ_α) + zcTargetAlpha`. The bound-sanity
conjunct is shared verbatim.

**Sorried** (a corollary of the sorried batching identities `sum_sumcheckPolyZero` /
`sum_sumcheckPolyAlpha`, plus `challenges`-uniqueness `Fin 0 → F`). -/
theorem mem_relZeroCheck_of_roundRel
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ)
    (s : ZeroCheckStatement Φ K.TCom F n μ) (w : LiftedWitness Φ μ n)
    (h : (toRoundStatement Φ m₁ φF s, w) ∈ roundRel Φ m₀ m₁ bound ρBound K φF b 0) :
    (s, w) ∈ relZeroCheck Φ m₀ m₁ bound ρBound K φF b := by
  sorry

/-- **The sumcheck bridge as a (plain) `CWSSPackage`**: zero-round `ReduceClaim` at
`mapStmt := toRoundStatement`, reducing `relZeroCheck` to the round-`0` `roundRel` with no soundness
error, hence escape-free. -/
noncomputable def sumcheckBridgePackage (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) :
    CWSSPackage init impl
      (ZeroCheckStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (RoundStatement Φ K.TCom F n μ 0) (LiftedWitness Φ μ n)
      (!p[] : ProtocolSpec 0) where
  verifier := ReduceClaim.verifier oSpec (toRoundStatement Φ m₁ φF)
  struct := CWSSStructure.ofIsEmpty
  relIn := relZeroCheck Φ m₀ m₁ bound ρBound K φF b
  relOut := roundRel Φ m₀ m₁ bound ρBound K φF b 0
  isPure := ⟨fun stmt _ => toRoundStatement Φ m₁ φF stmt, fun _ _ => rfl⟩
  extractor := ReduceClaim.treeExtractor (mapStmt := toRoundStatement Φ m₁ φF)
    (roundRel Φ m₀ m₁ bound ρBound K φF b 0) (fun _ w => w) CWSSStructure.ofIsEmpty
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSoundWith
    (relIn := relZeroCheck Φ m₀ m₁ bound ρBound K φF b)
    (relOut := roundRel Φ m₀ m₁ bound ρBound K φF b 0)
    (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
    (fun s w h => mem_relZeroCheck_of_roundRel Φ m₀ m₁ bound ρBound K φF b s w h)

end ArkLib.Lattices.Ajtai.InnerOuter
