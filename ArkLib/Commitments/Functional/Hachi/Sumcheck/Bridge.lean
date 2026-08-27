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
    `a := zcTargetAlpha = ∑ᵢ eq̃(τ_α, i)·ŷᵢ(α)` is computed by the verifier from the statement
    alone.

  The statement map installs the empty challenge prefix and the initial target pair
  `(0, zcTargetAlpha)`. The bridge is pure reshaping: both directions are the pair of algebraic
  identities `∑ F_{0,τ₀} = H₀(τ₀)` and `∑ F_{α,τ_α} = H_α(τ_α) + zcTargetAlpha`
  (`sum_sumcheckPolyZero` / `sum_sumcheckPolyAlpha`, `ZeroCheck/Constraints.lean`), read in
  opposite orientations — the pull-back `mem_relNestedZeroCheck_of_nestedRoundRel` for soundness,
  the push-forward `mem_nestedRoundRel_of_relNestedZeroCheck` for the honest side. The latter gives
  `nestedSumcheckBridgeReduction_perfectCompleteness` (error `0`, through
  `ReduceClaim.reduction_completeness_of_imp`), about the same verifier as the package
  (`nestedSumcheckBridgeReduction_verifier`).

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
variable (m₀ m₁ : ℕ) (bound bDig : ℕ)
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
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F) (b : ℕ)
    (s : NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁)
    (w : LiftedWitness Φ μ n)
    (hb : 1 < b) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (h : (nestedToRoundStatement Φ m₀ m₁ φF s, w) ∈
      nestedRoundRel Φ m₀ m₁ bound bDig K φF b 0) :
    (s, w) ∈ relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b := by
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
    rw [sum_sumcheckPolyAlpha' Φ m₀ m₁ φF b hb s.rlin s.α s.τα w hd hμn] at hAlpha
    exact add_eq_right.mp hAlpha

/-! ## The honest direction -/

omit [NeZero q] in
/-- **Point-to-sum push-forward** (converse of `mem_relNestedZeroCheck_of_nestedRoundRel`): the
zero-check's direct point claims give the initial hypercube-sum claims at the installed targets.

The same two identities, run the other way: `∑ F_{0,τ₀} = H₀(τ₀)` turns `H₀(τ₀) = 0` into the
initial target `0`, and `∑ F_{α,τ_α} = H_α(τ_α) + zcTargetAlpha` turns `H_α(τ_α) = 0` into the
initial target `zcTargetAlpha`. Commitment, shortness and bound sanity pass through verbatim, so
with the pull-back this makes `nestedRoundRel 0` at the mapped statement *equivalent* to
`relNestedZeroCheck`. -/
theorem mem_nestedRoundRel_of_relNestedZeroCheck
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F) (b : ℕ)
    (hb : 1 < b) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (s : NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁)
    (w : LiftedWitness Φ μ n)
    (h : (s, w) ∈ relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b) :
    (nestedToRoundStatement Φ m₀ m₁ φF s, w) ∈
      nestedRoundRel Φ m₀ m₁ bound bDig K φF b 0 := by
  rw [relNestedZeroCheck, Set.mem_setOf_eq] at h
  rcases h with ⟨hCom, hShort, hZero, hAlpha, hBound⟩
  rw [hZero_eval_eq] at hZero
  rw [hAlpha_eval_eq] at hAlpha
  refine ⟨hCom, hShort, ?_, ?_, hBound⟩
  · change hypercubeSum m₀ (sumcheckPolyZero Φ m₀ φF b s.τ₀ w) 0 (fun j => j.elim0) = 0
    rw [sum_sumcheckPolyZero' Φ m₀ φF b s.τ₀ w]
    exact hZero
  · change hypercubeSum m₀ (sumcheckPolyAlpha Φ m₀ m₁ φF b s.rlin s.α s.τα w) 0
      (fun j => j.elim0) = zcTargetAlpha Φ m₁ φF s.rlin s.α s.τα
    rw [sum_sumcheckPolyAlpha' Φ m₀ m₁ φF b hb s.rlin s.α s.τα w hd hμn, hAlpha, zero_add]

/-- **The sumcheck bridge as a protocol object**: the zero-round `ReduceClaim` reduction at
`mapStmt := nestedToRoundStatement`, with the witness passed through. Its verifier is
`nestedSumcheckBridgePackage`'s on the nose (`nestedSumcheckBridgeReduction_verifier`, stated after
the package). -/
def nestedSumcheckBridgeReduction {TCom : Type} (φF : ZMod q →+* F) :
    Reduction oSpec
      (NestedZeroCheckStatement Φ TCom F n μ m₀ m₁) (LiftedWitness Φ μ n)
      (NestedRoundStatement Φ TCom F n μ m₀ m₁ 0) (LiftedWitness Φ μ n)
      (!p[] : ProtocolSpec 0) :=
  ReduceClaim.reduction oSpec (nestedToRoundStatement Φ m₀ m₁ φF) (fun _ w => w)

omit [NeZero q] in
/-- **Perfect completeness of the zero-round sumcheck bridge**, error `0` and unconditional beyond
the two arity/positivity conditions the sum identities need (`0 < deg φ`,
`(μ + n·δ)·deg φ ≤ 2^{m₀}`).

All of the content is `mem_nestedRoundRel_of_relNestedZeroCheck`; a zero-round `ReduceClaim` head
draws no challenge and performs no check, so `ReduceClaim.reduction_completeness_of_imp` discharges
the execution layer. -/
theorem nestedSumcheckBridgeReduction_perfectCompleteness
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F) (b : ℕ)
    (hb : 1 < b) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    (nestedSumcheckBridgeReduction (oSpec := oSpec) (TCom := K.TCom)
        Φ m₀ m₁ φF).perfectCompleteness init impl
      (relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b)
      (nestedRoundRel Φ m₀ m₁ bound bDig K φF b 0) :=
  ReduceClaim.reduction_completeness_of_imp
    (relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b)
    (nestedRoundRel Φ m₀ m₁ bound bDig K φF b 0)
    (fun s w h =>
      mem_nestedRoundRel_of_relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b hb hd hμn s w h)

/-- The nested sumcheck bridge verifier's purity as computable data (`Verifier.PureForm`): the
verdict is `nestedToRoundStatement`, read off the zero-round `ReduceClaim` head, so `verify_eq`
is `rfl`.

The package carries this instead of a `Verifier.IsPure` instance, because the composed chain must
*run* this verdict at the seam and reading it off the `IsPure` existential would cost
`Classical.choice`. -/
def nestedSumcheckBridgeVerifierPureForm
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig)) (φF : ZMod q →+* F) :
    (ReduceClaim.verifier oSpec
      (nestedToRoundStatement (TCom := K.TCom) (n := n) (μ := μ) Φ m₀ m₁ φF)).PureForm where
  verify := fun stmt _ => nestedToRoundStatement Φ m₀ m₁ φF stmt
  verify_eq := fun _ _ => rfl

/-- The sumcheck bridge as a (plain) `CWSSPackage`: zero-round `ReduceClaim` at
`mapStmt := nestedToRoundStatement`, reducing `relNestedZeroCheck` to the round-`0`
`nestedRoundRel`. -/
def nestedSumcheckBridgePackage (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F) (b : ℕ) (hb : 1 < b) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    CWSSPackage init impl
      (NestedZeroCheckStatement Φ K.TCom F n μ m₀ m₁) (LiftedWitness Φ μ n)
      (NestedRoundStatement Φ K.TCom F n μ m₀ m₁ 0) (LiftedWitness Φ μ n)
      (!p[] : ProtocolSpec 0) where
  verifier := ReduceClaim.verifier oSpec (nestedToRoundStatement Φ m₀ m₁ φF)
  struct := CWSSStructure.ofIsEmpty
  relIn := relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b
  relOut := nestedRoundRel Φ m₀ m₁ bound bDig K φF b 0
  isPure := nestedSumcheckBridgeVerifierPureForm Φ m₀ m₁ bound bDig K φF
  extractor := ReduceClaim.treeExtractor (fun _ w => w) CWSSStructure.ofIsEmpty
  isCWSS := ReduceClaim.verifier_coordinateWiseSpecialSoundWith
    (relIn := relNestedZeroCheck Φ m₀ m₁ bound bDig K φF b)
    (relOut := nestedRoundRel Φ m₀ m₁ bound bDig K φF b 0)
    (mapWitInv := fun _ w => w) (D := CWSSStructure.ofIsEmpty)
    (fun s w =>
      mem_relNestedZeroCheck_of_nestedRoundRel Φ m₀ m₁ bound bDig K φF b s w hb hd hμn)

set_option linter.unusedSectionVars false in
/-- The bridge's protocol object and its certificate speak about the same verifier. Holds by
`rfl`. -/
@[simp] theorem nestedSumcheckBridgeReduction_verifier (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F) (b : ℕ)
    (hb : 1 < b) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n * rhoDigitCount q b) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    (nestedSumcheckBridgeReduction (oSpec := oSpec) (TCom := K.TCom) Φ m₀ m₁ φF).verifier
      = (nestedSumcheckBridgePackage Φ m₀ m₁ bound bDig init impl K φF b hb hd hμn).verifier :=
  rfl

end ArkLib.Lattices.Ajtai.InnerOuter
