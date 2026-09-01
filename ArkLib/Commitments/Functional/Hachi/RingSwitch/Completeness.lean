/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.ComputableWitness
import ArkLib.Commitments.Functional.Hachi.RingSwitch.QuotientNorms

/-!
  # `RingSwitch` — completeness (Hachi §4.3 entry: the `R^lin` adapter and the HMZ25 lift)

  The honest direction of the two links this folder owns; `Rlin.lean` and `Reduction.lean` carry the
  soundness certificates (`rlinPackage.isCWSS`, `liftPackage.isCWSS`). Each theorem states its own
  exact boundary; in summary:

  * `rlinReduction_perfectCompleteness_image` — the zero-round `R^lin` adapter, into the honest
    chain's seam relation `relRlinImage` (the *image* of the adapter's two maps on `relOut`).
    Unconditional, error `0`. Uses `ReduceClaim.reduction_completeness_of_imp`, since the `↔` form
    would require `rlinStmt` to be injective.
  * `rlinReduction_perfectCompleteness` — its coarsening along `relRlinImage ⊆ relRlin`, for callers
    that only need the soundness-facing relation.
  * `liftReduction_perfectCompleteness_image` — the lift (Figure 4 / Lemma 9) on that seam:
    **unconditional**, error `0`, at `bound = γ` and an admissible digit base. Both halves of
    `liftShort` are discharged — the `z`-bound from seam membership
    (`vecLInftyNorm_le_of_mem_relRlinImage`), the quotient bound from the digit encoding
    (`rhoDigitsShort_of_digitBaseOk`) — so no admissibility hypothesis on the witness remains.
    `…_of_zShort` is the parameterized form over an arbitrary input relation.
  * `rhoShort_honestLiftWitness` — the `ρ`-half of `liftShort` at the sharp quotient bound
    `μ · 2d · βM · βz`, for a caller whose `R^lin` matrix is short.

  The lift consumes `relRlinImage`, not `relRlin`: `relRlin` forgets the matrix provenance and the
  value of `s.bound`, and `∀ s, bound ≤ s.bound` is false for positive `bound`, so the honest side
  needs the image seam (see `relRlinImage` in `Rlin.lean`). The seam refines `relRlin`, so no
  relation is weakened for soundness.

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
def rlinReduction
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
/-- **Perfect completeness of the `R^lin` adapter, into the honest seam `relRlinImage`**
(unconditional, error `0`). The honest prover of a zero-round `ReduceClaim` link *is* the pair of
maps, so its output lands in their image by construction — this is the seam's defining property, and
it is what carries the Eq. (20) provenance (matrix shape, public bound `γ`, `z`-range) forward
to the lift. See `relRlinImage` for why the honest side needs provenance that `relRlin` discards.

Only the forward relation implication is needed, via
`ReduceClaim.reduction_completeness_of_imp`; the `↔` form could not be used here, since it would
require `rlinStmt` to be injective. -/
theorem rlinReduction_perfectCompleteness_image
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ) :
    (rlinReduction (oSpec := oSpec) (zDigits := zDigits) Φ pp base ω γ).perfectCompleteness
      init impl (relOut (zDigits := zDigits) Φ pp base ω γ)
      (relRlinImage (zDigits := zDigits) Φ pp base ω γ) :=
  ReduceClaim.reduction_completeness_of_imp
    (relOut (zDigits := zDigits) Φ pp base ω γ)
    (relRlinImage (zDigits := zDigits) Φ pp base ω γ)
    (fun X w h => ⟨X, w, h, rfl⟩)

omit [NeZero q] in
/-- **Perfect completeness of the `R^lin` adapter at the soundness relation `relRlin`.** The
coarsening of `…_image` along `relRlinImage ⊆ relRlin`
(`mem_relRlin_of_mem_relRlinImage`) — so the two statements are ordered, not competing: the image
seam is the honest chain's interface, `relRlin` the soundness-facing abstraction.

All of the content is the block-row equivalence of `Rlin.lean`; the zero-round `ReduceClaim` head
draws no challenge and performs no check. -/
theorem rlinReduction_perfectCompleteness
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ) :
    (rlinReduction (oSpec := oSpec) (zDigits := zDigits) Φ pp base ω γ).perfectCompleteness
      init impl (relOut (zDigits := zDigits) Φ pp base ω γ) (relRlin Φ) :=
  Reduction.completeness_relOut_mono init impl
    (fun _ h => mem_relRlin_of_mem_relRlinImage Φ pp base ω γ h)
    (rlinReduction_perfectCompleteness_image Φ init impl pp base ω γ)

end Rlin

/-! ## The HMZ25 lift (Figure 4 / Lemma 9) -/

section Lift

variable {n μ : ℕ} {F : Type} [Field F] (bound bDig : ℕ)

/-- **The honest lifted witness of Hachi's lift**: the `R^lin` witness `z` together with the
per-row honest quotients of the cyclotomic presentation — the generic
`RingSwitching.Lift.honestWitness` at `cyclotomicPresentation`. This is what the honest Figure-4
prover commits to and later outputs, and it is the term whose `liftShort` admissibility the
completeness theorems discharge — the quotient half from the digit encoding, the
`z` half from the image seam (`liftReduction_perfectCompleteness_image`).

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
(`liftReduction_verifier`).

**Computable**, and stated at the computable honest witness `honestLiftWitnessC`
(`RingSwitch/ComputableWitness.lean`) rather than at generic `Lift.honestWitness`. That is the
*same value* (`honestLiftWitnessC_eq_honestWitness`), so nothing about this link changes except
that it can be run: `liftReduction_eq` re-expresses it as generic `Lift.reduction` and every
completeness theorem below goes through that rewrite. The noncomputable
`honestLiftWitness`/`Lift.honestWitness` remain as the spec-side definitions, and the soundness
side (`liftPackage`) is untouched — it consumes the verifier, which is the same on the nose
(`liftReduction_verifier`). -/
def liftReduction
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (hd : 0 < Φ.φ.natDegree) :
    Reduction oSpec (RlinStatement Φ n μ) (ArkLib.Lattices.PolyVec (Rq Φ) μ)
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (pSpecScalar K.TCom F) :=
  CommittedScalar.reduction K (honestLiftWitnessC Φ hd)

omit [NeZero q] [Field F] in
/-- **The protocol object is the generic one.** `liftReduction` and generic `Lift.reduction`
differ only in which honest-witness function they carry, and those are equal
(`honestLiftWitnessC_eq_honestWitness`), so the reductions are. This is the rewrite every
completeness theorem below uses to reach the generic execution lemmas. -/
theorem liftReduction_eq
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (hd : 0 < Φ.φ.natDegree) :
    haveI := isPresentation_cyclotomic Φ hd
    liftReduction (oSpec := oSpec) (F := F) Φ bound bDig K hd
      = Lift.reduction (cyclotomicPresentation Φ) (fun s => s.M) (fun s => s.yvec) K
          (cyclotomicPresentation_modulus_natDegree Φ) := by
  haveI := isPresentation_cyclotomic Φ hd
  exact congrArg _ (funext fun s => funext fun z =>
    honestLiftWitnessC_eq_honestWitness Φ hd s z)

omit [NeZero q] in
/-- The lift's protocol object and its escape-aware soundness certificate share a verifier. Holds
by `rfl`. -/
@[simp] theorem liftReduction_verifier
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig)) (φF : ZMod q →+* F)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hd : 0 < Φ.φ.natDegree) :
    (liftReduction (oSpec := oSpec) (F := F) Φ bound bDig K hd).verifier
      = (liftPackage (oSpec := oSpec) Φ bound bDig K φF init impl hd).verifier := by
  haveI := isPresentation_cyclotomic Φ hd
  rw [liftReduction_eq]
  rfl

omit [NeZero q] in
/-- **The `ρ`-half of `liftShort` for the honest lifted witness**, at the explicit growth bound
`μ · 2d · βM · βz`: the honest quotients are coefficientwise selections from the row sum
(`valMinAbs_natAbs_coeff_quotient_le`), so coefficient bounds on the `R^lin` matrix and on the
witness transfer with **no growth from the division itself**. No wraparound hypothesis is needed
(centered representatives are minimal among integer representatives). -/
theorem rhoShort_honestLiftWitness {d : ℕ} (hφ : Φ.φ.toPoly = Polynomial.X ^ d + 1) (hdpos : 0 < d)
    (hd : 0 < Φ.φ.natDegree) {βM βz : ℕ} (s : RlinStatement Φ n μ)
    (z : ArkLib.Lattices.PolyVec (Rq Φ) μ)
    (hM : ∀ i j, Rq.lInftyNorm Φ (s.M i j) ≤ βM) (hz : ∀ j, Rq.lInftyNorm Φ (z j) ≤ βz) :
    RhoShort (μ * (2 * d * (βM * βz))) (honestLiftWitness Φ hd s z).ρ :=
  fun i k => by
    rw [CPolynomial.coeff_toPoly,
      show ((honestLiftWitness Φ hd s z).ρ i).toPoly
          = (cyclotomicPresentation Φ).quotient s.M z s.yvec i
        from CPolynomial.toPoly_mk_toImpl _]
    exact valMinAbs_natAbs_coeff_quotient_le Φ hφ hdpos s.M z s.yvec hM hz i k

omit [NeZero q] in
/-- **Perfect completeness of Hachi's lift from an honest seam, at the digit base `bDig`** —
error `0`,
and with **no admissibility hypothesis on the witness**: the quotient half of `liftShort` is
discharged for an *arbitrary* quotient (`rhoDigitsShort_of_half_le`), so beyond the
parameter-level digit-base facts `hb`/`hbq`/`hdig` (the `DigitBaseOk` triple, unbundled) the
only premises are the three facts the seam relation supplies about its own members.

* `hrow` — the linear system `M z = y`;
* `hside` — the statement-level side condition `bound ≤ s.bound`;
* `hzShort` — the protocol-level norm bound `‖z‖∞ ≤ bound`.

All three hold on the honest seam `relRlinImage` (see
`liftReduction_perfectCompleteness_image`, where they are discharged and nothing at all is
assumed). Error `0` because the honest quotients satisfy each lifted row identity as polynomials
(`RingSwitching.Lift.checkAt_honestWitness`), so no property of `α` is used. -/
theorem liftReduction_perfectCompleteness_of_zShort [SampleableType F]
    (hb : 1 < bDig) (hbq : bDig ≤ q / 2) (hdig : bDig / 2 ≤ bound)
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig)) (φF : ZMod q →+* F)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hd : 0 < Φ.φ.natDegree)
    (relIn : Set (RlinStatement Φ n μ × ArkLib.Lattices.PolyVec (Rq Φ) μ))
    (hrow : ∀ s z, (s, z) ∈ relIn → s.M *ᵥ z = s.yvec)
    (hside : ∀ s z, (s, z) ∈ relIn → bound ≤ s.bound)
    (hzShort : ∀ s z, (s, z) ∈ relIn → vecLInftyNorm Φ z ≤ bound) :
    (liftReduction (oSpec := oSpec) (F := F) Φ bound bDig K hd).perfectCompleteness init impl
      relIn (relLift Φ bound bDig K φF) := by
  haveI := isPresentation_cyclotomic Φ hd
  have h := Lift.reduction_perfectCompleteness_of_relIn (cyclotomicPresentation Φ) φF
    (fun s : RlinStatement Φ n μ => s.M) (fun s : RlinStatement Φ n μ => s.yvec)
    (fun s : RlinStatement Φ n μ => bound ≤ s.bound) K
    (cyclotomicPresentation_modulus_natDegree Φ) relIn hrow hside
    (fun s z hIn => ⟨hzShort s z hIn,
      rhoDigitsShort_of_half_le Φ hb hbq hdig _⟩) init impl
  rw [liftReduction_eq]
  exact h

end Lift

/-! ## The honest chain: adapter ▷ lift, at the seam -/

section HonestChain

variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}
variable {F : Type} [Field F]

omit [NeZero q] in
/-- **Perfect completeness of Hachi's HMZ25 lift on the honest chain — unconditional, error `0`.**

This is the lift's completeness with *nothing* assumed beyond membership in the honest seam and the
Hachi parameter conditions: the three premises of
`liftReduction_perfectCompleteness_of_zShort` are all read off `relRlinImage`
(`matVecMul_eq_of_mem_relRlinImage`, `bound_eq_of_mem_relRlinImage`,
`vecLInftyNorm_le_of_mem_relRlinImage`), and the `ρ`-half of `liftShort` is discharged by the
quotient bound. No `hshort`, no `hbound`, no admissibility hypothesis.

Two parameter choices are *forced* by the chain and worth naming:

* `bound = γ`. The seam gives `‖z‖∞ ≤ γ` and `s.bound = γ`, so the lift's protocol bound must be
  `≥ γ` (shortness) and `≤ γ` (its side condition `bound ≤ s.bound`).
* the digit base `bDig`, with `⌊bDig/2⌋ ≤ γ`. Because the committed quotient block is its digits,
  the quotient half of `liftShort` is discharged by `rhoDigitsShort_of_half_le` for *any* quotient.
  A raw quotient block would instead force the bound `q/2` (`rhoShort_half`), and with it the
  degeneracy `γ = q/2 = bZero − 1`. -/
theorem liftReduction_perfectCompleteness_image [SampleableType F] {γ bDig : ℕ}
    (hb : 1 < bDig) (hbq : bDig ≤ q / 2) (hdig : bDig / 2 ≤ γ)
    (K : LiftCom
      (LiftedWitness Φ (rlinCols innerRows messageDigits innerDigits zDigits m r)
        (rlinRows innerRows outerRows dRows))
      (liftShort Φ γ bDig))
    (φF : ZMod q →+* F)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hd : 0 < Φ.φ.natDegree)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω : ℕ) :
    (liftReduction (oSpec := oSpec) (F := F) Φ γ bDig K hd).perfectCompleteness init impl
      (relRlinImage (zDigits := zDigits) Φ pp base ω γ) (relLift Φ γ bDig K φF) := by
  -- Each seam projection is stated with a fully explicit type; feeding them in as `have`s keeps the
  -- unifier away from the large dimension expressions.
  have h1 : ∀ s z, (s, z) ∈ relRlinImage (zDigits := zDigits) Φ pp base ω γ →
      s.M *ᵥ z = s.yvec :=
    fun s z h => matVecMul_eq_of_mem_relRlinImage (zDigits := zDigits) Φ pp base ω γ s z h
  have h2 : ∀ s z, (s, z) ∈ relRlinImage (zDigits := zDigits) Φ pp base ω γ → γ ≤ s.bound :=
    fun s z h =>
      le_of_eq (bound_eq_of_mem_relRlinImage (zDigits := zDigits) Φ pp base ω γ s z h).symm
  have h3 : ∀ s z, (s, z) ∈ relRlinImage (zDigits := zDigits) Φ pp base ω γ →
      vecLInftyNorm Φ z ≤ γ :=
    fun s z h => vecLInftyNorm_le_of_mem_relRlinImage (zDigits := zDigits) Φ pp base ω γ s z h
  exact liftReduction_perfectCompleteness_of_zShort Φ γ bDig hb hbq hdig K φF init impl hd
    _ h1 h2 h3

end HonestChain


end ArkLib.Lattices.Ajtai.InnerOuter
