/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Reduction

/-!
  # `RingSwitch` — completeness (Hachi §4.3 entry: the `R^lin` adapter and the HMZ25 lift)

  The honest direction of the two links this folder owns. `Rlin.lean` and `Reduction.lean` certify
  that *any* prover the verifier accepts yields a witness (coordinate-wise special soundness, at
  `rlinPackage.isCWSS` and `liftPackage.isCWSS`); this file proves the converse for both — the
  honest prover is accepted with probability one.

  ## What is proved here

  * `rlinReduction_perfectCompleteness` — the zero-round `R^lin` adapter. Both relation directions
    were already available (`mem_relOut_of_relRlin` / `mem_relRlin_of_relOut`, both proven in
    `Rlin.lean`), so all that was missing is the `ReduceClaim` plumbing: the honest prover *is* the
    statement reshaping `rlinStmt` together with the witness reshaping `stack`, and
    `ReduceClaim.reduction_completeness` turns the relation equivalence into perfect completeness.
    Error `0`, no challenge involved.
  * `liftReduction_perfectCompleteness` — the HMZ25 lift (Figure 4 / Lemma 9). Error `0` as well,
    and for the structural reason recorded in `RingSwitching.Lift.checkAt_honestWitness`: the honest
    quotients make each lifted row an *exact* identity in `ZMod q[X]`, so it survives evaluation at
    every `α`, not merely at a random one. Nothing about the challenge distribution is used; the
    `SampleableType F` instance is needed only so that execution can draw `α` at all.

  Both are `Reduction.perfectCompleteness` in full, for arbitrary shared oracles `oSpec`, state
  initialization `init` and query implementation `impl`, and both are proved *generically* one layer
  up (`RingSwitching.Lift.reduction_perfectCompleteness`, itself resting on the new
  `CoordinateWise.CommittedScalar.reduction_perfectCompleteness` — the honest execution of the
  commit-then-challenge shape, owned once where the shape is owned). This file supplies only the
  cyclotomic instantiation, exactly as `liftPackage` supplies only the cyclotomic instantiation of
  the soundness side.

  ## The two hypotheses of the lift, and why they are hypotheses

  `liftReduction_perfectCompleteness` assumes what an honest Hachi prover has to be *given*, not
  what it can derive:

  * `hbound` — the protocol's global norm parameter is dominated by the statement's public bound
    (`bound ≤ s.bound`, the `sideCond` of the generic switch). This is a statement-family
    convention, invisible to `relRlin`.
  * `hshort` — the honest lifted witness `(z, ρ)` is **admissible**: `liftShort`, i.e. Figure 4's
    range checks `‖z‖∞ ≤ bound` and `RhoShort ρBound ρ`. Neither half follows from `relRlin`:
    `relRlin` bounds `z` by the *statement's* bound while `liftShort` bounds it by the
    *protocol's*, and the quotient bound is a coefficient-growth statement about
    `(rowSum − rep yᵢ) /ₘ φ` at the concrete parameters — the `ℓ∞` norm-growth theory that
    `Gadget/Norms` and `CyclotomicRing/NormBounds` develop for the other links, not yet available
    for polynomial division.

  Assuming the honest values are in range is the same shape as `QuadEval`'s completeness assuming
  its digit bounds (`hddCarrier` / `hddZ`): a parameter-choice fact of the paper, discharged when
  concrete parameters are pinned. See `docs/wiki/repo-map.md` for the remaining gap list.

  ## References

  * [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open RingSwitching RingSwitching.Lift
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.ScalarRound

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-! ## The `R^lin` adapter (zero-round) -/

section Rlin

variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}

/-- **The `R^lin` adapter as a protocol object**: the zero-round `ReduceClaim` reduction that
reshapes an Eq. (20) transcript claim into the unstructured linear claim `R^lin` — the statement by
`rlinStmt`, the witness by `stack`. Its verifier is `rlinPackage`'s verifier on the nose
(`rlinReduction_verifier`), so the two security directions of this link cannot drift apart.

`noncomputable` only because `rlinStmt` is (it is assembled through the `stack`/`unstack` reshapes
of `Rlin.lean`); nothing probabilistic or classical enters the protocol. -/
noncomputable def rlinReduction
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ) :
    Reduction oSpec
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
      (QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
      (RlinStatement Φ (rlinRows innerRows outerRows dRows)
        (rlinCols innerRows messageDigits innerDigits zDigits m r))
      (ArkLib.Lattices.PolyVec (Rq Φ)
        (rlinCols innerRows messageDigits innerDigits zDigits m r))
      !p[] :=
  ReduceClaim.reduction oSpec (rlinStmt (zDigits := zDigits) Φ pp base ω γ)
    (fun _ w => stack Φ w)

omit [NeZero q] in
/-- The adapter's protocol object and its soundness certificate share a verifier. Holds by
`rfl`. -/
@[simp] theorem rlinReduction_verifier
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ) :
    (rlinReduction (oSpec := oSpec) (zDigits := zDigits) Φ pp base ω γ).verifier
      = (rlinPackage (oSpec := oSpec) (zDigits := zDigits) Φ init impl pp base ω γ).verifier :=
  rfl

omit [NeZero q] in
/-- **Perfect completeness of the `R^lin` adapter.** An honest prover holding an Eq. (20)-valid
`QuadEvalResponse` is accepted with probability one, and the stacked witness satisfies `relRlin` at
the assembled statement, with the prover's and the verifier's output statements equal.

All of the content is the relation equivalence `relOut ↔ relRlin ∘ (rlinStmt, stack)`, whose two
halves are the proven block-row lemmas of `Rlin.lean`; the zero-round `ReduceClaim` head draws no
challenge and performs no check, so `ReduceClaim.reduction_completeness` discharges everything
else. -/
theorem rlinReduction_perfectCompleteness
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ) :
    (rlinReduction (oSpec := oSpec) (zDigits := zDigits) Φ pp base ω γ).perfectCompleteness
      init impl (relOut (zDigits := zDigits) Φ pp base ω γ) (relRlin Φ) :=
  ReduceClaim.reduction_completeness
    (relOut (zDigits := zDigits) Φ pp base ω γ) (relRlin Φ)
    (fun X w =>
      ⟨fun h => mem_relRlin_of_relOut Φ pp base ω γ X w h,
        fun h => by
          have h' := (rlin_iff_relOut Φ pp base ω γ X (stack Φ w)).mp h
          rwa [unstack_stack] at h'⟩)

end Rlin

/-! ## The HMZ25 lift (Figure 4 / Lemma 9) -/

section Lift

variable {n μ : ℕ} {F : Type} [Field F] (bound ρBound : ℕ)

/-- **The honest lifted witness of Hachi's lift**: the `R^lin` witness `z` together with the
per-row honest quotients of the cyclotomic presentation — the generic
`RingSwitching.Lift.honestWitness` at `cyclotomicPresentation`. This is what the honest Figure-4
prover commits to and later outputs, and it is the term the admissibility hypothesis of
`liftReduction_perfectCompleteness` is stated about.

`noncomputable`, because the quotients are Mathlib polynomials produced by division: the lifted
witness type `LiftedWitness` stores `Polynomial (ZMod q)`, not the computable `CPolynomial`. An
extraction-facing honest prover would have to restate the quotient over the computable
representation. -/
noncomputable def honestLiftWitness (hd : 0 < Φ.φ.natDegree)
    (s : RlinStatement Φ n μ) (z : ArkLib.Lattices.PolyVec (Rq Φ) μ) : LiftedWitness Φ μ n :=
  haveI := isPresentation_cyclotomic Φ hd
  Lift.honestWitness (cyclotomicPresentation Φ) (fun s => s.M) (fun s => s.yvec)
    (cyclotomicPresentation_modulus_natDegree Φ) s z

/-- **Hachi's lift as a protocol object** (Figure 4): the committed-scalar protocol of the
cyclotomic quotient-evaluation switch — commit to the honest lifted witness `w̃`, receive `α`,
output `(statement, t, α)` together with `w̃`.

Note it does not mention the embedding `φF : ZMod q →+* F`: the honest prover's data is the lifted
witness, and `φF` enters only through the *relation* `relLift` (via `liftCheckAt`), which is where
the row identities are evaluated. Its verifier is `liftPackage`'s
(`liftReduction_verifier`). -/
noncomputable def liftReduction
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (hd : 0 < Φ.φ.natDegree) :
    Reduction oSpec (RlinStatement Φ n μ) (ArkLib.Lattices.PolyVec (Rq Φ) μ)
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (pSpecScalar K.TCom F) :=
  haveI := isPresentation_cyclotomic Φ hd
  Lift.reduction (cyclotomicPresentation Φ) (fun s => s.M) (fun s => s.yvec) K
    (cyclotomicPresentation_modulus_natDegree Φ)

omit [NeZero q] in
/-- The lift's protocol object and its escape-aware soundness certificate share a verifier. Holds
by `rfl`. -/
@[simp] theorem liftReduction_verifier
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound)) (φF : ZMod q →+* F)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hd : 0 < Φ.φ.natDegree) :
    (liftReduction (oSpec := oSpec) (F := F) Φ bound ρBound K hd).verifier
      = (liftPackage (oSpec := oSpec) Φ bound ρBound K φF init impl hd).verifier :=
  rfl

omit [NeZero q] in
/-- **Perfect completeness of Hachi's HMZ25 lift** (Figure 4 / Lemma 9), at error exactly `0`.

An honest prover holding a short solution `z` of the `R^lin` system commits to the lifted witness
`(z, ρ)` with the honest quotients, and whatever `α` the verifier draws, the resulting
statement/witness pair lies in `relLift`, with the prover's and the verifier's output statements
equal. The error is `0` because the honest quotients satisfy each lifted row identity *as
polynomials* (`RingSwitching.Lift.checkAt_honestWitness`), so no property of `α` is used — the
mirror image of why the soundness side needs `2d` distinct challenges.

The two hypotheses `hbound` and `hshort` are the honest-side range conditions of Figure 4; see the
module docstring for why neither is derivable from `relRlin`. Everything else is discharged
generically by `RingSwitching.Lift.reduction_perfectCompleteness`. -/
theorem liftReduction_perfectCompleteness [SampleableType F]
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound)) (φF : ZMod q →+* F)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hd : 0 < Φ.φ.natDegree)
    (hbound : ∀ s : RlinStatement Φ n μ, bound ≤ s.bound)
    (hshort : ∀ (s : RlinStatement Φ n μ) (z : ArkLib.Lattices.PolyVec (Rq Φ) μ),
      (s, z) ∈ relRlin Φ → liftShort Φ bound ρBound (honestLiftWitness Φ hd s z)) :
    (liftReduction (oSpec := oSpec) (F := F) Φ bound ρBound K hd).perfectCompleteness init impl
      (relRlin Φ) (relLift Φ bound ρBound K φF) :=
  by
  haveI := isPresentation_cyclotomic Φ hd
  have h := Lift.reduction_perfectCompleteness (cyclotomicPresentation Φ) φF
    (fun s : RlinStatement Φ n μ => s.M) (fun s : RlinStatement Φ n μ => s.yvec)
    (fun (s : RlinStatement Φ n μ) (z : ArkLib.Lattices.PolyVec (Rq Φ) μ) =>
      vecLInftyNorm Φ z ≤ s.bound)
    (fun s : RlinStatement Φ n μ => bound ≤ s.bound) K
    (cyclotomicPresentation_modulus_natDegree Φ)
    (fun s _ _ => hbound s) (fun s z hIn => hshort s z hIn) init impl
  exact h

end Lift

end ArkLib.Lattices.Ajtai.InnerOuter
