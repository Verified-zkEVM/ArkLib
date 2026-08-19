/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Reduction

/-!
  # `RingSwitch` — completeness (Hachi §4.3 entry: the `R^lin` adapter and the HMZ25 lift)

  The honest direction of the two links this folder owns; `Rlin.lean` and `Reduction.lean` carry the
  soundness certificates (`rlinPackage.isCWSS`, `liftPackage.isCWSS`). Each theorem states its own
  exact boundary; in summary:

  * `rlinReduction_perfectCompleteness` — the zero-round `R^lin` adapter, into `relRlin`.
    Unconditional, error `0`.
  * `rlinReduction_perfectCompleteness_bounded` — the same adapter into the honest chain's seam
    relation `relRlinFor Φ bound`, under the parameter condition `bound ≤ γ`.
  * `liftReduction_perfectCompleteness_of_honestShort` — the lift (Figure 4 / Lemma 9), error `0`,
    **conditional**: it assumes `liftShort` of the honest lifted witness, an undischarged
    coefficient-growth bound through polynomial division. Its input relation is `relRlinFor`, not
    `relRlin`, because the lift's side condition has to be carried by the seam relation rather than
    assumed of every statement (see `relRlinFor`).

  Both protocol objects share their package's verifier by `rfl`
  (`rlinReduction_verifier`, `liftReduction_verifier`). The execution and algebra are generic
  (`RingSwitching.Lift.honestWitness` / `checkAt_honestWitness` /
  `reduction_perfectCompleteness_of_relIn`, over
  `CoordinateWise.CommittedScalar.reduction_perfectCompleteness`); this file only instantiates
  at `cyclotomicPresentation`, exactly as `liftPackage` does on the soundness side.

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

omit [NeZero q] in
/-- **The adapter lands in the honest chain's seam relation `relRlinFor`** under the single
parameter condition `bound ≤ γ`. `rlinStmt` sets the assembled statement's public bound to `γ`
(`rlinStmt_bound`), so this is where the lift's side condition `bound ≤ s.bound` is *established*
rather than assumed — see `relRlinFor`'s docstring for why assuming it of every `RlinStatement` is
not an option. -/
theorem rlinReduction_perfectCompleteness_bounded
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ) {bound : ℕ} (hbγ : bound ≤ γ) :
    (rlinReduction (oSpec := oSpec) (zDigits := zDigits) Φ pp base ω γ).perfectCompleteness
      init impl (relOut (zDigits := zDigits) Φ pp base ω γ) (relRlinFor Φ bound) :=
  ReduceClaim.reduction_completeness
    (relOut (zDigits := zDigits) Φ pp base ω γ) (relRlinFor Φ bound)
    (fun X w =>
      ⟨fun h => ⟨mem_relRlin_of_relOut Φ pp base ω γ X w h, hbγ⟩,
        fun h => by
          have h' := (rlin_iff_relOut Φ pp base ω γ X (stack Φ w)).mp h.1
          rwa [unstack_stack] at h'⟩)

end Rlin

/-! ## The HMZ25 lift (Figure 4 / Lemma 9) -/

section Lift

variable {n μ : ℕ} {F : Type} [Field F] (bound ρBound : ℕ)

/-- **The honest lifted witness of Hachi's lift**: the `R^lin` witness `z` together with the
per-row honest quotients of the cyclotomic presentation — the generic
`RingSwitching.Lift.honestWitness` at `cyclotomicPresentation`. This is what the honest Figure-4
prover commits to and later outputs, and it is the term the admissibility hypothesis of
`liftReduction_perfectCompleteness_of_honestShort` is stated about.

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
/-- **Conditional perfect completeness of Hachi's HMZ25 lift** (Figure 4 / Lemma 9), at error
exactly `0`.

An honest prover holding a short solution `z` of the `R^lin` system commits to the lifted witness
`(z, ρ)` with the honest quotients, and whatever `α` the verifier draws, the resulting
statement/witness pair lies in `relLift`, with the prover's and the verifier's output statements
equal. Error `0` because the honest quotients satisfy each lifted row identity *as polynomials*
(`RingSwitching.Lift.checkAt_honestWitness`), so no property of `α` is used — the mirror image of
why the soundness side needs `2d` distinct challenges.

**Exact boundary of this theorem.**

* Input relation is `relRlinFor Φ bound`, not `relRlin Φ`: the lift's `sideCond`
  (`bound ≤ s.bound`) is *carried by the seam relation*, established by the preceding adapter
  (`rlinReduction_perfectCompleteness_bounded`, under `bound ≤ γ`). It cannot be a hypothesis about
  all statements — see `relRlinFor`.
* `hshort` is a **genuine undischarged obligation**, which is why this is *conditional* perfect
  completeness: the honest lifted witness must be admissible for the commitment's shortness regime
  (`liftShort`, Figure 4's `‖z‖∞ ≤ bound` and `RhoShort ρBound ρ`). Neither half follows from
  `relRlinFor`: it bounds `z` by the *statement's* bound while `liftShort` bounds it by the
  *protocol's*, and the `ρ`-half is a coefficient-growth bound on `(rowSum − rep yᵢ) /ₘ φ`, i.e.
  `ℓ∞` growth through **polynomial division**, which the norm theory
  (`Gadget/Norms`, `CyclotomicRing/NormBounds`) does not yet cover. Until it is proved at concrete
  parameters this link is complete only relative to `hshort`. -/
theorem liftReduction_perfectCompleteness_of_honestShort [SampleableType F]
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound)) (φF : ZMod q →+* F)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hd : 0 < Φ.φ.natDegree)
    (hshort : ∀ (s : RlinStatement Φ n μ) (z : ArkLib.Lattices.PolyVec (Rq Φ) μ),
      (s, z) ∈ relRlinFor Φ bound → liftShort Φ bound ρBound (honestLiftWitness Φ hd s z)) :
    (liftReduction (oSpec := oSpec) (F := F) Φ bound ρBound K hd).perfectCompleteness init impl
      (relRlinFor Φ bound) (relLift Φ bound ρBound K φF) := by
  haveI := isPresentation_cyclotomic Φ hd
  have h := Lift.reduction_perfectCompleteness_of_relIn (cyclotomicPresentation Φ) φF
    (fun s : RlinStatement Φ n μ => s.M) (fun s : RlinStatement Φ n μ => s.yvec)
    (fun s : RlinStatement Φ n μ => bound ≤ s.bound) K
    (cyclotomicPresentation_modulus_natDegree Φ) (relRlinFor Φ bound)
    (fun _ _ h => h.1.1) (fun _ _ h => h.2) (fun s z hIn => hshort s z hIn) init impl
  exact h

end Lift

end ArkLib.Lattices.Ajtai.InnerOuter
