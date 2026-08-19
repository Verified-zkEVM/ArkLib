/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.Commitment
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Completeness
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Completeness

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

## What is *not* here: the composed reduction

These are **per-link theorems at compatible relations**, not completeness of an appended reduction.
Composing them into one statement about the opening protocol needs
`Reduction.append_completeness` (`OracleReduction/Composition/Sequential/Append.lean`) and, for the
context-lifted links, `liftContext_completeness` (`OracleReduction/LiftContext/Reduction.lean`) —
**both still `sorry`**. Nothing in this file, or anywhere in the Hachi tree, states completeness of
the composed opening; `Composition.lean` composes the *soundness* certificates only. What the seam
corollaries do establish is that the relation interfaces match, so no relation-level obstruction
remains once the generic composition lemmas land.

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

end ArkLib.Lattices.Ajtai.InnerOuter
