/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.Commitment
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Completeness
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Completeness
import ArkLib.Commitments.Functional.Hachi.Sumcheck.Completeness
import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
# The honest Hachi chain: parameters and per-seam corollaries

Each Hachi link is proved complete in its own file. What is easy to lose across those files is the
*parameter bookkeeping*: one numeric quantity appears as an Eq. (20) ball radius, an `R^lin` public
bound and the lift's `bound`, and another as the zero-check range base. `HonestRangeParams` bundles
the relations the **honest** direction needs, and the corollaries below re-state each link's
completeness at those parameters, so the seams visibly line up:

```
paper-exact QuadEval  relInBox        → paperRelOut b    (balanced digits)
      ↓  paperRelOut ⊆ relOut γ      (needs ⌊b/2⌋ ≤ γ)
R^lin adapter         relOut γ        → relRlinImage γ   (image seam, provenance kept)
      ↓  identity
HMZ25 lift            relRlinImage γ  → relLift γ (q/2)  (bound = γ forced by the seam)
      ↓  identity
batching bridge       relLift γ (q/2) → relBatched bZero (γ, q/2 ≤ bZero − 1)
```

## The composed reductions, and what they cost

The seam corollaries above are **per-link theorems at compatible relations**: they establish that
the relation interfaces match, with no reference to composition. Two composed statements are also
here — `completePrefixReduction_perfectCompleteness` (through the nested zero-check) and
`completeThroughSumcheckReduction_perfectCompleteness` (through the sumcheck, to
`relWEvalClaim`) — but both are **`sorryAx`-tainted by construction**: appending completeness needs
`Reduction.append_completeness` (`OracleReduction/Composition/Sequential/Append.lean`), still
`sorry`, and the context-lifted links would additionally need `liftContext_completeness`
(`OracleReduction/LiftContext/Reduction.lean`), also still `sorry`. Every per-link input is
axiom-clean; nothing beyond `relWEvalClaim` is composed at all (the recursion tail's honest layer
does not exist yet), and `Composition.lean` composes the *soundness* certificates only.

## What the non-short honest quotient costs

The honest lift quotient is **not short**: for a Hachi `R^lin` instance the matrix carries the Ajtai
key blocks and the gadget powers, so `ρBound = q/2` is its true bound (`rhoShort_half`). Since the
batching bridge range-checks the `z` **and** quotient halves of the table `w̃` against a *single*
base `bZero` (`ZeroCheck/Constraints`), the honest direction needs `q/2 ≤ bZero − 1`: the zero-check
range base must be at least `q/2 + 1`, hence a range polynomial of degree linear in `q`.

It does **not** force a large Eq. (20) ball radius. Honest completeness of the batching bridge uses
only `bound ≤ bZero − 1` and `ρBound ≤ bZero − 1` (`batchReduction_perfectCompleteness`, via
`ReduceClaim.reduction_completeness_of_imp`), so `γ` stays free — `HonestRangeParams.ofDigitBase`
witnesses the parameters at `γ = ⌊b/2⌋`, where Eq. (20)'s `c6` check is a real constraint. The
collapse `γ = q/2 = bZero − 1` appears only if one insists on a *single* parameterization that also
serves the bridge's pull-back, which needs the reverse orientations; that is
`HonestRangeParams.pinned_of_soundness_orientations`. Removing it needs a range table with separate
bases for the two halves. -/

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open RingSwitching RingSwitching.Lift
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.ScalarRound

namespace ArkLib.Lattices.Ajtai.InnerOuter

/-- **Range parameters of the honest Hachi chain**, with the relations its seams need — *honest
direction only*.

* `b` — the balanced digit base of the honest committer and of Eq. (20)'s box `S_b`; `hb`/`hbq` are
  the balanced-digit conditions (`balancedZmodDigit_valMinAbs_mem`).
* `γ` — Eq. (20)'s `c6` ball radius, the `R^lin` statement's public bound (`rlinStmt` sets
  `bound := γ`) and, forced by the honest seam, the lift's own `bound`. `hbγ` is the box→ball
  transport condition of `paperRelOut_subset_relOut`.
* `bZero` — the zero-check range base of `relBatched`. `hγZero` and `hρZero` are the two conditions
  the batching bridge's *honest* direction needs, at `ρBound = q/2`.

Note what is **not** here: the reverse (soundness) orientations `bZero − 1 ≤ γ` and
`bZero − 1 ≤ q/2`. They are what would pin the parameters; honest completeness does not need them
(`batchReduction_perfectCompleteness` goes through `ReduceClaim.reduction_completeness_of_imp`), so
`γ` stays free — see `ofDigitBase` for a witness with `γ = ⌊b/2⌋`, arbitrarily small. The pinning
statement, and the parameterization it applies to, is `pinned_of_soundness_orientations`. -/
structure HonestRangeParams (q : ℕ) where
  /-- Balanced digit base (also Eq. (20)'s box base `S_b`). -/
  b : ℕ
  /-- Eq. (20) ball radius = `R^lin` public bound = the lift's `bound`. -/
  γ : ℕ
  /-- Zero-check range base of `relBatched`. -/
  bZero : ℕ
  /-- The digit base is nontrivial. -/
  hb : 1 < b
  /-- Anti-wraparound for balanced digits: they are centered representatives. -/
  hbq : b ≤ q / 2
  /-- Box ⊆ ball: `paperRelOut b ⊆ relOut γ`. -/
  hbγ : b / 2 ≤ γ
  /-- Batching bridge, honest direction, `z` half. -/
  hγZero : γ ≤ bZero - 1
  /-- Batching bridge, honest direction, quotient half (at `ρBound = q/2`). -/
  hρZero : q / 2 ≤ bZero - 1

namespace HonestRangeParams

variable {q : ℕ}

/-- **The honest parameters are satisfiable with a small `γ`.** At `γ = ⌊b/2⌋` — the radius the
balanced digits actually meet, so Eq. (20)'s `c6` check is a real constraint — everything holds,
with `bZero = q/2 + 1`.

This is the accurate form of the chain's cost: what the non-short honest quotient forces is a large
*zero-check range base* (`bZero − 1 ≥ q/2`, hence a range polynomial of degree linear in `q`),
**not** a large Eq. (20) ball radius. -/
def ofDigitBase (b : ℕ) (hb : 1 < b) (hbq : b ≤ q / 2) : HonestRangeParams q where
  b := b
  γ := b / 2
  bZero := q / 2 + 1
  hb := hb
  hbq := hbq
  hbγ := le_refl _
  hγZero := by omega
  hρZero := by omega

variable (P : HonestRangeParams q)

/-- The zero-check range base dominates both declared bounds — the honest direction's requirement,
restated. -/
theorem le_bZero_sub_one : max P.γ (q / 2) ≤ P.bZero - 1 := max_le P.hγZero P.hρZero

/-- **The pinch, correctly attributed.** *If* one insists on a single parameterization that also
serves the batching bridge's pull-back — which needs the reverse orientations `bZero − 1 ≤ bound`
and `bZero − 1 ≤ ρBound` (`mem_relLift_of_relBatched`) — then, at the honest chain's `bound = γ` and
`ρBound = q/2`, all three quantities collapse: `γ = q/2 = bZero − 1`, and Eq. (20)'s ball check
becomes vacuous.

That is a statement about *two-sided* parameterizations, not about honest completeness: the
hypotheses below are exactly the two soundness-side inequalities that `HonestRangeParams`
deliberately omits. Removing the collapse needs a range table checking the `z` half and the quotient
half at separate bases (`ZeroCheck/Constraints`'s `w̃` uses one base for both). -/
theorem pinned_of_soundness_orientations (hγ' : P.bZero - 1 ≤ P.γ) (hρ' : P.bZero - 1 ≤ q / 2) :
    P.γ = q / 2 ∧ P.bZero - 1 = q / 2 := by
  have h1 := P.hγZero
  have h2 := P.hρZero
  exact ⟨by omega, by omega⟩

end HonestRangeParams

/-! ## The seams, at bundled parameters -/

section Seams

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat} {ω : ℕ}

omit [NeZero q] in
/-- **Seam 1 — paper-exact `QuadEval` feeds the `R^lin` adapter.** The honest `QuadEval` response
lands in `paperRelOut` at the digit base `b` (`mem_paperRelOut_of_relIn`), while the adapter's
input is `relOut` at the ball radius `γ`; the bundled `hbγ : ⌊b/2⌋ ≤ γ` is exactly the transport
condition of `paperRelOut_subset_relOut`. -/
theorem paperRelOut_subset_relOut_params (P : HonestRangeParams q)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) :
    paperRelOut (zDigits := zDigits) Φ pp base ω P.b
      ⊆ relOut (zDigits := zDigits) Φ pp base ω P.γ :=
  paperRelOut_subset_relOut Φ pp base ω P.hbγ

omit [NeZero q] in
/-- **Seam 2 — the adapter feeds the honest lift seam.** Unconditional; the seam is the adapter's
image, so nothing beyond the parameters is needed. -/
theorem rlinReduction_perfectCompleteness_params (P : HonestRangeParams q)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) :
    (rlinReduction (oSpec := oSpec) (zDigits := zDigits) Φ pp base ω P.γ).perfectCompleteness
      init impl (relOut (zDigits := zDigits) Φ pp base ω P.γ)
      (relRlinImage (zDigits := zDigits) Φ pp base ω P.γ) :=
  rlinReduction_perfectCompleteness_image Φ init impl pp base ω P.γ

omit [NeZero q] in
/-- **Seam 3 — the lift consumes that seam, at `bound = γ` and `ρBound = q/2`.** Unconditional: both
halves of `liftShort` are discharged (`liftReduction_perfectCompleteness_image`). -/
theorem liftReduction_perfectCompleteness_params {F : Type} [Field F] [SampleableType F]
    (P : HonestRangeParams q)
    (K : LiftCom
      (LiftedWitness Φ (rlinCols innerRows messageDigits innerDigits zDigits m r)
        (rlinRows innerRows outerRows dRows))
      (liftShort Φ P.γ (q / 2)))
    (φF : ZMod q →+* F)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hd : 0 < Φ.φ.natDegree)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) :
    (liftReduction (oSpec := oSpec) (F := F) Φ P.γ (q / 2) K hd).perfectCompleteness init impl
      (relRlinImage (zDigits := zDigits) Φ pp base ω P.γ) (relLift Φ P.γ (q / 2) K φF) :=
  liftReduction_perfectCompleteness_image Φ K φF init impl hd pp base ω

omit [NeZero q] in
/-- **Seam 4 — the lift's output feeds the batching bridge**, at the bundled `bZero`. The bridge's
two honest range hypotheses are exactly the bundled ones, and `relLift γ (q/2)` is *literally* the
bridge's input relation, so the two links meet on the nose. No arity conditions are needed on this
side (they belong to the pull-back). -/
theorem batchReduction_perfectCompleteness_params {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n μ m₀ m₁ : ℕ} (P : HonestRangeParams q)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ P.γ (q / 2)))
    (φF : ZMod q →+* F) (hd : 0 < Φ.φ.natDegree) :
    (batchReduction (oSpec := oSpec) Φ P.γ (q / 2) K).perfectCompleteness init impl
      (relLift Φ P.γ (q / 2) K φF)
      (relBatched Φ m₀ m₁ P.γ (q / 2) K φF P.bZero) :=
  batchReduction_perfectCompleteness Φ m₀ m₁ P.γ (q / 2) init impl K φF P.bZero hd
    P.hγZero P.hρZero

end Seams

/-! ## The complete proved prefix, composed

The reduction below appends every Hachi protocol object whose honest direction is currently proved:
the polynomial bridge, `QuadEval`, the `R^lin` adapter, the HMZ25 lift, the batching bridge, and the
nested zero-check. Its completeness theorem uses `Reduction.append_perfectCompleteness`; until the
generic append theorem is made an explicit project axiom, this declaration inherits its existing
`sorryAx` dependency.

There is one additional parameter boundary compared with the per-seam results above. The batching
bridge itself needs only the honest orientations in `HonestRangeParams`, but
`nestedZeroCheckReduction_perfectCompleteness` is stated on all of `relBatched`: because that
relation forgets shortness, the theorem re-derives it from the range identity and needs the reverse
inequalities `bZero - 1 ≤ γ` and `bZero - 1 ≤ q / 2`. Thus the complete prefix is presently
available only at a bidirectional (hence pinned) parameterization. Removing these two hypotheses
requires a shortness-preserving honest seam between batching and zero-check. -/

section CompletePrefix

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r m₀ m₁ : Nat} {ω : ℕ}
variable {F : Type} [Field F] [BEq F] [LawfulBEq F] [SampleableType F]

local notation "μ₀" => rlinCols innerRows messageDigits innerDigits zDigits m r
local notation "n₀" => rlinRows innerRows outerRows dRows

/-- Sampleability of the complete prefix's nested wire format, assembled explicitly because the
generic append instance does not reliably fire through a deeply nested `ProtocolSpec`. -/
@[reducible] instance completePrefixSpecSampleable
    {TCom : Type}
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
        (CarrierCom Φ dRows) (ShortChallenge Φ ω) r).Challenge i)] :
    ∀ i, SampleableType
      (((!p[] : ProtocolSpec 0) ++ₚ
        (CoordinateWise.SingleRound.pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r ++ₚ
          ((!p[] : ProtocolSpec 0) ++ₚ
            (pSpecScalar TCom F ++ₚ
              ((!p[] : ProtocolSpec 0) ++ₚ pSpecNestedZeroCheck F m₀ m₁))))).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend
    (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
    (h₂ := ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := by infer_instance)
      (h₂ := ProtocolSpec.instSampleableTypeChallengeAppend
        (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
        (h₂ := ProtocolSpec.instSampleableTypeChallengeAppend
          (h₁ := CoordinateWise.ScalarRound.instSampleableTypeChallengePSpecScalar)
          (h₂ := ProtocolSpec.instSampleableTypeChallengeAppend
            (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
            (h₂ := instSampleableTypeChallengePSpecNestedZeroCheck)))))

/-- The honest protocol obtained by appending every currently complete Hachi link, from the
polynomial-level evaluation bridge through the nested zero-check. -/
noncomputable def completePrefixReduction (P : HonestRangeParams q)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hqm : q ≤ P.b ^ messageDigits) (hqz : q ≤ P.b ^ zDigits)
    (K : LiftCom (LiftedWitness Φ μ₀ n₀) (liftShort Φ P.γ (q / 2)))
    (hd : 0 < Φ.φ.natDegree) : Reduction oSpec
      (PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (NestedZeroCheckStatement Φ K.TCom F n₀ μ₀ m₀ m₁)
      (LiftedWitness Φ μ₀ n₀)
      ((!p[] : ProtocolSpec 0) ++ₚ
        (CoordinateWise.SingleRound.pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r ++ₚ
          ((!p[] : ProtocolSpec 0) ++ₚ
            (pSpecScalar K.TCom F ++ₚ
              ((!p[] : ProtocolSpec 0) ++ₚ pSpecNestedZeroCheck F m₀ m₁))))) :=
  (bridgeReduction (oSpec := oSpec) Φ).append
    ((quadEvalReduction (oSpec := oSpec) (zDigits := zDigits) (ω := ω) Φ pp
      (balancedZmodDigitDecomposition P.b messageDigits P.hb hqm)
      (balancedZmodDigitDecomposition P.b zDigits P.hb hqz)).append
    ((rlinReduction (oSpec := oSpec) (zDigits := zDigits) Φ pp (P.b : ZMod q) ω P.γ).append
    ((liftReduction (oSpec := oSpec) (F := F) Φ P.γ (q / 2) K hd).append
    ((batchReduction (oSpec := oSpec) Φ P.γ (q / 2) K).append
      (nestedZeroCheckReduction (oSpec := oSpec) (TCom := K.TCom)
        (Wit := LiftedWitness Φ μ₀ n₀) Φ m₀ m₁)))))

/-- **Perfect completeness of the complete currently proved Hachi prefix**, from the
polynomial-level evaluation relation through `relNestedZeroCheck`.

The two reverse range hypotheses are needed only by the last link, as explained above. Together
with `P.hγZero` and `P.hρZero` they imply the pinned parameterization; this theorem does not conceal
that cost. All individual links have error zero, so the composed prefix has error zero as well. -/
theorem completePrefixReduction_perfectCompleteness
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
        (CarrierCom Φ dRows) (ShortChallenge Φ ω) r).Challenge i)]
    {m₀ m₁ : ℕ} (P : HonestRangeParams q)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hqm : q ≤ P.b ^ messageDigits) (hqz : q ≤ P.b ^ zDigits)
    (hmd : 0 < messageDigits) (hτ : 0 < zDigits) (hd : 0 < Φ.φ.natDegree)
    (K : LiftCom (LiftedWitness Φ μ₀ n₀) (liftShort Φ P.γ (q / 2)))
    (φF : ZMod q →+* F) (hμn : (μ₀ + n₀) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hZeroγ : P.bZero - 1 ≤ P.γ) (hZeroρ : P.bZero - 1 ≤ q / 2)
    {βSq κ : ℕ} :
    (completePrefixReduction (oSpec := oSpec) (F := F) (ω := ω) (m₀ := m₀) (m₁ := m₁)
      Φ P pp hqm hqz K hd).perfectCompleteness init impl
      (relPolyEval Φ pp (P.b : ZMod q) βSq P.γ κ)
      (relNestedZeroCheck Φ m₀ m₁ P.γ (q / 2) K φF P.bZero) := by
  have hBridge :=
    bridgeReduction_perfectCompleteness Φ init impl pp (P.b : ZMod q) βSq P.γ κ
  have hQuad := quadEvalReduction_perfectCompleteness (zDigits := zDigits) (ω := ω)
      (βSq := βSq) (γ := P.γ) (κ := κ)
      Φ init impl pp _ _ hmd hτ hd
      (fun x e => le_trans (balancedZmodDigit_natAbs_le P.hb hqm P.hbq x e) P.hbγ)
      (fun x e => le_trans (balancedZmodDigit_natAbs_le P.hb hqz P.hbq x e) P.hbγ)
  have hRlin := rlinReduction_perfectCompleteness_params (zDigits := zDigits) (ω := ω)
    Φ P init impl pp (P.b : ZMod q)
  have hLift := liftReduction_perfectCompleteness_params (zDigits := zDigits) (ω := ω)
    Φ P K φF init impl hd pp (P.b : ZMod q)
  have hBatch := batchReduction_perfectCompleteness_params (m₀ := m₀) (m₁ := m₁)
    Φ P init impl K φF hd
  have hZero := nestedZeroCheckReduction_perfectCompleteness
    Φ m₀ m₁ P.γ (q / 2) init impl K φF P.bZero hd hμn hZeroγ hZeroρ
  letI sampleEmptyNested : ∀ i, SampleableType
      (((!p[] : ProtocolSpec 0) ++ₚ pSpecNestedZeroCheck F m₀ m₁).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
      (h₂ := instSampleableTypeChallengePSpecNestedZeroCheck)
  letI sampleScalarTail : ∀ i, SampleableType
      ((pSpecScalar K.TCom F ++ₚ
        ((!p[] : ProtocolSpec 0) ++ₚ pSpecNestedZeroCheck F m₀ m₁)).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := CoordinateWise.ScalarRound.instSampleableTypeChallengePSpecScalar)
      (h₂ := sampleEmptyNested)
  letI sampleEmptyScalarTail : ∀ i, SampleableType
      (((!p[] : ProtocolSpec 0) ++ₚ
        (pSpecScalar K.TCom F ++ₚ
          ((!p[] : ProtocolSpec 0) ++ₚ pSpecNestedZeroCheck F m₀ m₁))).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
      (h₂ := sampleScalarTail)
  letI sampleQuadTail : ∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
          (CarrierCom Φ dRows) (ShortChallenge Φ ω) r ++ₚ
        ((!p[] : ProtocolSpec 0) ++ₚ
          (pSpecScalar K.TCom F ++ₚ
            ((!p[] : ProtocolSpec 0) ++ₚ pSpecNestedZeroCheck F m₀ m₁)))).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := by infer_instance)
      (h₂ := sampleEmptyScalarTail)
  have hBatchZero := Reduction.append_perfectCompleteness _ _ hBatch hZero
  have hLiftZero := Reduction.append_perfectCompleteness _ _ hLift hBatchZero
  have hRlinZero := Reduction.append_perfectCompleteness _ _ hRlin hLiftZero
  have hQuadZero := Reduction.append_perfectCompleteness _ _ hQuad hRlinZero
  have hPrefix := Reduction.append_perfectCompleteness _ _ hBridge hQuadZero
  exact hPrefix

end CompletePrefix

/-! ## Through the sumcheck

`completePrefixReduction` stops at `relNestedZeroCheck`. `Sumcheck/Completeness.lean` carries that
relation on to the evaluation claim `relWEvalClaim` — bridge, `m₀` paired rounds, final
evaluation — so the two compose into an honest protocol from the polynomial-evaluation relation
all the way to the claim the `Recursion/` adapters consume.

The prefix is left untouched: this is a new definition appending to it, so nothing already proved
about `completePrefixReduction` moves.

Two boundaries are visible in the statement:

* the sumcheck's arity is `m₀ = M + 1` — the loop needs at least one cube coordinate to fold, the
  same successor shape `Sumcheck/RoundPoly.lean` and the round soundness theorem use;
* like everything appended, this inherits `sorryAx` from the generic
  `Reduction.append_completeness`. The links it is built from are individually axiom-clean. -/

section ThroughSumcheck

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r M m₁ : Nat} {ω : ℕ}
variable {F : Type} [Field F] [BEq F] [LawfulBEq F] [SampleableType F]

local notation "μ₀" => rlinCols innerRows messageDigits innerDigits zDigits m r
local notation "n₀" => rlinRows innerRows outerRows dRows

/-- The honest Hachi protocol from the polynomial-evaluation claim through the sumcheck: the
complete proved prefix (`completePrefixReduction`) followed by the local sumcheck
(`sumcheckReduction`). -/
noncomputable def completeThroughSumcheckReduction (P : HonestRangeParams q)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hqm : q ≤ P.b ^ messageDigits) (hqz : q ≤ P.b ^ zDigits)
    (K : LiftCom (LiftedWitness Φ μ₀ n₀) (liftShort Φ P.γ (q / 2)))
    (hd : 0 < Φ.φ.natDegree) (hbZero : 0 < P.bZero) (φF : ZMod q →+* F) : Reduction oSpec
      (PolyEvalStatement Φ innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (WEvalStatement K.TCom F (M + 1))
      (LiftedWitness Φ μ₀ n₀)
      (((!p[] : ProtocolSpec 0) ++ₚ
        (CoordinateWise.SingleRound.pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r ++ₚ
          ((!p[] : ProtocolSpec 0) ++ₚ
            (pSpecScalar K.TCom F ++ₚ
              ((!p[] : ProtocolSpec 0) ++ₚ pSpecNestedZeroCheck F (M + 1) m₁))))) ++ₚ
        sumcheckSpec F P.bZero (M + 1)) :=
  (completePrefixReduction (oSpec := oSpec) (F := F) (ω := ω) (m₀ := M + 1) (m₁ := m₁)
      Φ P pp hqm hqz K hd).append
    (sumcheckReduction (oSpec := oSpec) (TCom := K.TCom) Φ m₁ P.γ P.bZero hbZero φF)

/-- Sampleability of the through-sumcheck wire format: the prefix's own instance appended to the
sumcheck's, assembled explicitly for the same reason `completePrefixSpecSampleable` is — the
generic append instance does not fire reliably through a deeply nested `ProtocolSpec`. -/
@[reducible] instance throughSumcheckSpecSampleable {TCom : Type} (bZero : ℕ)
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
        (CarrierCom Φ dRows) (ShortChallenge Φ ω) r).Challenge i)] :
    ∀ i, SampleableType
      ((((!p[] : ProtocolSpec 0) ++ₚ
        (CoordinateWise.SingleRound.pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r ++ₚ
          ((!p[] : ProtocolSpec 0) ++ₚ
            (pSpecScalar TCom F ++ₚ
              ((!p[] : ProtocolSpec 0) ++ₚ pSpecNestedZeroCheck F (M + 1) m₁))))) ++ₚ
        sumcheckSpec F bZero (M + 1)).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend
    (h₁ := completePrefixSpecSampleable Φ) (h₂ := sumcheckSpecSampleable bZero (M + 1))

set_option linter.unusedSectionVars false in
/-- **Perfect completeness of the honest Hachi chain through the sumcheck**, from `relPolyEval` to
the evaluation claim `relWEvalClaim`, error `0`.

Hypotheses are the prefix's (`completePrefixReduction_perfectCompleteness`, including the two
reverse range orientations the nested zero-check's honest seam needs) plus the sumcheck's
`0 < bZero` and `(μ₀ + n₀)·deg φ ≤ 2^{m₀}`. The seam itself needs nothing: the prefix's output
relation `relNestedZeroCheck` *is* the sumcheck's input relation, at the same parameters.

⚠ **Inherits `sorryAx`** through `Reduction.append_perfectCompleteness` — the generic
`Reduction.append_completeness` is still `sorry`. Each link is axiom-clean on its own. -/
theorem completeThroughSumcheckReduction_perfectCompleteness
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
        (CarrierCom Φ dRows) (ShortChallenge Φ ω) r).Challenge i)]
    (P : HonestRangeParams q)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hqm : q ≤ P.b ^ messageDigits) (hqz : q ≤ P.b ^ zDigits)
    (hmd : 0 < messageDigits) (hτ : 0 < zDigits) (hd : 0 < Φ.φ.natDegree)
    (hbZero : 0 < P.bZero)
    (K : LiftCom (LiftedWitness Φ μ₀ n₀) (liftShort Φ P.γ (q / 2)))
    (φF : ZMod q →+* F) (hμn : (μ₀ + n₀) * Φ.φ.natDegree ≤ 2 ^ (M + 1))
    (hZeroγ : P.bZero - 1 ≤ P.γ) (hZeroρ : P.bZero - 1 ≤ q / 2)
    {βSq κ : ℕ} :
    (completeThroughSumcheckReduction (oSpec := oSpec) (F := F) (ω := ω) (M := M) (m₁ := m₁)
      Φ P pp hqm hqz K hd hbZero φF).perfectCompleteness init impl
      (relPolyEval Φ pp (P.b : ZMod q) βSq P.γ κ)
      (relWEvalClaim Φ (M + 1) P.γ (q / 2) P.bZero K φF) :=
  Reduction.append_perfectCompleteness _ _
    (completePrefixReduction_perfectCompleteness (zDigits := zDigits) (ω := ω)
      (m₀ := M + 1) (m₁ := m₁) (βSq := βSq) (κ := κ)
      Φ P init impl pp hqm hqz hmd hτ hd K φF hμn hZeroγ hZeroρ)
    (sumcheckReduction_perfectCompleteness Φ m₁ P.γ (q / 2) P.bZero init impl K hbZero φF hd hμn)

end ThroughSumcheck



end ArkLib.Lattices.Ajtai.InnerOuter
