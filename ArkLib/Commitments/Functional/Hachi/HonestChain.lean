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
*parameter bookkeeping*: the same numeric quantity appears as an Eq. (20) ball radius, an `R^lin`
public bound, the lift's `bound`, and a zero-check range base, and the links constrain it in both
directions. `HonestRangeParams` bundles those relations once, and the corollaries below re-state
each link's completeness at the bundled parameters, so the seams visibly line up:

```
paper-exact QuadEval  relInBox        → paperRelOut b   (balanced digits)
      ↓  paperRelOut ⊆ relOut γ      (needs ⌊b/2⌋ ≤ γ)
R^lin adapter         relOut γ        → relRlinImage γ  (image seam, provenance kept)
      ↓  identity
HMZ25 lift            relRlinImage γ  → relLift γ (q/2) (bound = γ forced by the seam)
      ↓  identity
batching bridge       relLift γ (q/2) → relBatched bZero (both orientations ⇒ pinned)
```

Composition of the *reductions* is out of scope (it needs `Reduction.append_completeness`, still
sorried); what is established here is per-link completeness at one coherent parameter choice, plus
the relation implications that make the outputs and inputs match.

## The pinch, stated plainly

`HonestRangeParams` is inhabited (`HonestRangeParams.trivial`), but only at
`γ = q/2` and `bZero = q/2 + 1`, and that is forced, not a modelling artefact:

* the honest lift quotient is **not short** — for a Hachi `R^lin` instance the matrix carries the
  Ajtai key blocks and gadget powers, so `ρBound = q/2` is the true bound (`rhoShort_half`);
* the batching bridge range-checks `z` and `ρ` against a **single** base `bZero`
  (`ZeroCheck/Constraints`'s table `w̃` holds both halves), and its two directions force
  `bound = ρBound = bZero − 1`.

So `bZero − 1 = q/2`, hence `γ = q/2`, hence Eq. (20)'s `c6` ball check is vacuous at these
parameters. This is a real limitation of the *single-range* table, not of the honest prover: a table
that range-checked the `z` half at `b` and the quotient half at its own base would remove it. Until
then, the honest chain is complete at coherent-but-trivial ranges, and every link's individual
completeness statement (which is what the files prove) holds at arbitrary parameters satisfying its
own hypotheses.
-/

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open RingSwitching RingSwitching.Lift
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.ScalarRound

namespace ArkLib.Lattices.Ajtai.InnerOuter

/-- **Range parameters of the honest Hachi chain**, with the relations its seams need.

* `b` — the balanced digit base of the honest committer and of Eq. (20)'s box `S_b`; `hb`/`hbq` are
  the balanced-digit conditions (`balancedZmodDigit_valMinAbs_mem`).
* `γ` — Eq. (20)'s `c6` ball radius, the `R^lin` statement's public bound (`rlinStmt` sets
  `bound := γ`) and, forced by the honest seam, the lift's own `bound`. `hbγ` is the box→ball
  transport condition of `paperRelOut_subset_relOut`.
* `bZero` — the zero-check range base of `relBatched`. `hγZero`/`hZeroγ` and `hρZero`/`hZeroρ` are
  the two orientations the batching equivalence needs, at `ρBound = q/2`; together they pin
  `γ = q/2 = bZero − 1` (see the module docstring). -/
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
  /-- Batching bridge, honest direction (`z` half). -/
  hγZero : γ ≤ bZero - 1
  /-- Batching bridge, soundness direction (`z` half). -/
  hZeroγ : bZero - 1 ≤ γ
  /-- Batching bridge, honest direction (quotient half, at `ρBound = q/2`). -/
  hρZero : q / 2 ≤ bZero - 1
  /-- Batching bridge, soundness direction (quotient half). -/
  hZeroρ : bZero - 1 ≤ q / 2

namespace HonestRangeParams

variable {q : ℕ}

/-- The parameters are **satisfiable**: at `γ = q/2` and `bZero = q/2 + 1` every relation holds, for
any digit base `b` with `1 < b ≤ q/2`. Recorded so that the corollaries below are not vacuous — and
so that the price is explicit: `γ = q/2` makes Eq. (20)'s ball check trivial, and `bZero = q/2 + 1`
makes the range polynomial's degree linear in `q`. See the module docstring. -/
def trivial (b : ℕ) (hb : 1 < b) (hbq : b ≤ q / 2) : HonestRangeParams q where
  b := b
  γ := q / 2
  bZero := q / 2 + 1
  hb := hb
  hbq := hbq
  hbγ := by omega
  hγZero := by omega
  hZeroγ := by omega
  hρZero := by omega
  hZeroρ := by omega

variable (P : HonestRangeParams q)

/-- `γ = bZero − 1`, from the two orientations. -/
theorem gamma_eq : P.γ = P.bZero - 1 := le_antisymm P.hγZero P.hZeroγ

/-- `q/2 = bZero − 1`, from the two orientations at the quotient half. -/
theorem half_eq : q / 2 = P.bZero - 1 := le_antisymm P.hρZero P.hZeroρ

/-- Consequently `γ = q/2`: the honest chain's ball radius is the trivial one. Not an artefact — see
the module docstring's discussion of the single-range table. -/
theorem gamma_eq_half : P.γ = q / 2 := by rw [P.gamma_eq, ← P.half_eq]

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
/-- **Seam 4 — the lift's output feeds the batching bridge**, at the bundled `bZero`. The
bridge's four range hypotheses are exactly the bundled orientations; `relLift γ (q/2)` is
*literally* the bridge's input relation, so the two links meet on the nose. -/
theorem batchReduction_perfectCompleteness_params {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n μ m₀ m₁ : ℕ} (P : HonestRangeParams q)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ P.γ (q / 2)))
    (φF : ZMod q →+* F) (hn : n ≤ 2 ^ m₁) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀) :
    (batchReduction (oSpec := oSpec) Φ P.γ (q / 2) K).perfectCompleteness init impl
      (relLift Φ P.γ (q / 2) K φF)
      (relBatched Φ m₀ m₁ P.γ (q / 2) K φF P.bZero) :=
  batchReduction_perfectCompleteness Φ m₀ m₁ P.γ (q / 2) init impl K φF P.bZero hn hd hμn
    P.hZeroγ P.hZeroρ P.hγZero P.hρZero

end Seams

end ArkLib.Lattices.Ajtai.InnerOuter
