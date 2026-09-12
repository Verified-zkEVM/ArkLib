/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
module

public import ArkLib.Commitments.Functional.Hachi.Commitment
public import ArkLib.Commitments.Functional.Hachi.RingSwitch.Completeness
public import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Completeness
public import ArkLib.Commitments.Functional.Hachi.Sumcheck.Completeness
public import ArkLib.OracleReduction.Composition.Sequential.Append
public import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness

/-!
# The honest Hachi chain: parameters and per-seam corollaries

Each Hachi link is proved complete in its own file. What is easy to lose across those files is the
*parameter bookkeeping*: one numeric quantity appears as an Eq. (20) ball radius, an `R^lin` public
bound and the lift's `bound`, and another as the zero-check range base. `HonestRangeParams` bundles
the relations the **honest** direction needs, and the corollaries below re-state the adapter, lift,
and batching links' completeness at those parameters, so the seams visibly line up. (The first
box→ball transport, `paperRelOut ⊆ relOut` from `QuadEval/Completeness.lean`, has no corollary
here: the composed proof applies the bundled `hbγ` directly to the balanced-digit bounds.)

```
paper-exact QuadEval  relInBox        → paperRelOut b    (balanced digits)
      ↓  paperRelOut ⊆ relOut γ      (needs ⌊b/2⌋ ≤ γ)
R^lin adapter         relOut γ        → relRlinImage γ   (image seam, provenance kept)
      ↓  identity
HMZ25 lift            relRlinImage γ  → relLift γ bZero  (bound = γ forced by the seam)
      ↓  identity
batching bridge       relLift γ bZero → relBatched bZero (γ ≤ bZero − 1)
```

## The composed reductions, and what they cost

The seam corollaries above establish that each link's relation matches its neighbour's.
`completePrefixReduction_perfectCompleteness`, through the nested zero-check, composes the
axiom-clean inputs with `Reduction.append_perfectCompleteness_of_pure_verifiers`.
`completeThroughSumcheckReduction_perfectCompleteness`, through sumcheck to `relWEvalClaim`, uses
`Reduction.append_perfectCompleteness_of_guarded_verifiers` to retain the sumcheck runtime checks.
Every suffix's completeness holds from every shared oracle state, so both composed theorems are
axiom-clean. No context lifting is needed. `Composition.lean` composes the soundness certificates;
beyond `relWEvalClaim` the run is closed by the terminal reveal-and-check in `Correctness.lean`.

## Why the quotient is committed as digits

The honest lift quotient is **not** short: for a Hachi `R^lin` instance the matrix carries the Ajtai
key blocks and the gadget powers, so `q/2` is its true bound (`rhoShort_half`, whose docstring
records why nothing sharper is available). A committed table `w̃` holding the **raw** quotient rows
would therefore force `q/2 ≤ bZero − 1` on the batching bridge's honest direction — a zero-check
range base of at least `q/2 + 1`, hence a range polynomial of degree linear in `q` — and, with the
bridge's *pull-back* orientations, `γ = q/2 = bZero − 1`, at which Eq. (20)'s ball check and the
Module-SIS escape target are both empty of content.

So `ZeroCheck/Constraints`'s `w̃` carries the quotient's balanced base-`bZero` **digits**
([NOZ26] §4.3's hidden gadget decomposition, `rhoDigits`), which are `⌊bZero/2⌋`-bounded for
*every* quotient with no hypothesis at all (`rhoDigits_valMinAbs_natAbs_le`). The quotient half of
both directions is then free at the small base, and what `HonestRangeParams` carries for it is the
digit-base admissibility triple `hbZero`/`hbZeroq`/`hbZeroγ` (`DigitBaseOk`), satisfiable at
`bZero = b = O(1)`. Adding the soundness orientations pins at `γ = bZero − 1 < q/2` — see
`pinned_of_soundness_orientations`.

This is the paper's own presentation: [NOZ26] §4.3 (p. 19) gadget-decomposes the
quotient into base-`b` digits before committing ("we omit the subscript u … there is a hidden
gadget decomposition of r"); Eq. (21)'s simplified table, which omits the decomposition, is a
presentational convenience of the paper rather than its protocol.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26] -/

@[expose] public section

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
* `bZero` — the zero-check range base of `relBatched`, and (the same number, deliberately) the
  base of the quotient's hidden gadget decomposition, so that the digits `w̃` range-checks are the
  digits the commitment binds. `hγZero` is the batching bridge's honest `z`-half condition;
  `hbZero`/`hbZeroq`/`hbZeroγ` are the digit-base admissibility triple `DigitBaseOk q γ bZero`,
  satisfiable at `bZero = b`.

Note what is **not** here: the reverse (soundness) orientation `bZero − 1 ≤ γ`. Honest completeness
does not need it (`batchReduction_perfectCompleteness` goes through
`ReduceClaim.reduction_completeness_of_imp`), so this structure leaves `γ` free. Adding that
orientation pins `γ = bZero − 1 < q/2` (`pinned_of_soundness_orientations`), a point realized by
`ofPinnedDigitBase`. -/
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
  /-- The quotient's digit base is nontrivial. -/
  hbZero : 1 < bZero
  /-- Anti-wraparound for the quotient digits: they are centered representatives. -/
  hbZeroq : bZero ≤ q / 2
  /-- The quotient digit radius fits Eq. (20)'s ball: `⌊bZero/2⌋ ≤ γ`. -/
  hbZeroγ : bZero / 2 ≤ γ

namespace HonestRangeParams

variable {q : ℕ}

/-- **The parameters are satisfiable at `O(b)`**, at `γ = bZero − 1 = b − 1` and `bZero = b`: the
value the batching bridge's pull-back orientation `bZero − 1 ≤ γ` forces on top of the honest
inequalities. So the pinned point of `pinned_of_soundness_orientations` is not merely consistent —
it is realized, at a `γ` and a range base that are both `O(b)` and, since `b ≤ q/2`, strictly
below `q/2`.

This is what the gadget decomposition of the quotient buys. Range-checking raw quotient rows
instead makes the same demand unsatisfiable below `q/2`: `rhoShort_half` forces
`bZero ≥ q/2 + 1`, hence `γ = q/2`. -/
def ofPinnedDigitBase (b : ℕ) (hb : 1 < b) (hbq : b ≤ q / 2) : HonestRangeParams q where
  b := b
  γ := b - 1
  bZero := b
  hb := hb
  hbq := hbq
  hbγ := by omega
  hγZero := le_refl _
  hbZero := hb
  hbZeroq := hbq
  hbZeroγ := by omega

variable (P : HonestRangeParams q)

/-- **Where the parameters pin, with the digit-committed quotient.** Adding the batching bridge's
*pull-back* orientation `bZero − 1 ≤ γ` — the one `HonestRangeParams` omits, because honest
completeness does not need it — forces `γ = bZero − 1`, and that value is **strictly below** `q/2`.

Both `γ` and the range box `[−(bZero−1), bZero−1]` are therefore real constraints, and at
`ofPinnedDigitBase b` the pinned point is `γ = b − 1 = O(1)`. Were `w̃` to carry raw quotient
rows, the same step would force `γ = q/2 = bZero − 1`, at which Eq. (20)'s ball check
`‖·‖∞ ≤ γ` and the range box are both vacuous over `ZMod q`, and `LiftCom.Collision` would place
no effective norm restriction on the quotient block. -/
theorem pinned_of_soundness_orientations (hγ' : P.bZero - 1 ≤ P.γ) :
    P.γ = P.bZero - 1 ∧ P.γ < q / 2 := by
  have h1 := P.hγZero
  have h2 := P.hbZero
  have h3 := P.hbZeroq
  exact ⟨by omega, by omega⟩

/-- The zero-check digit base is greater than one. -/
theorem one_lt_bZero : 1 < P.bZero := P.hbZero

/-- The quotient's digit base is admissible at the chain's own norm bound `γ` — the bundled form
`DigitBaseOk`, which is what the lift and the batching bridge consume. -/
theorem digitBaseOk : DigitBaseOk q P.γ P.bZero :=
  ⟨P.hbZero, P.hbZeroq, P.hbZeroγ⟩

/-- The same admissibility at the *range* bound `bZero − 1`, the form the batching bridge's honest
direction consumes: `⌊bZero/2⌋ ≤ bZero − 1` holds for every base `> 1`. -/
theorem digitBaseOk_range : DigitBaseOk q (P.bZero - 1) P.bZero :=
  ⟨P.hbZero, P.hbZeroq, by have := P.hbZero; omega⟩

end HonestRangeParams

/-! ## The seams, at bundled parameters -/

section Seams

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat} {ω : ℕ}

omit [NeZero q] in
/-- **Seam 1 — the adapter feeds the honest lift seam.** Unconditional; the seam is the adapter's
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
/-- **Seam 2 — the lift consumes that seam, at `bound = γ` and digit base `bDig = bZero`.** Both
halves of `liftShort` are discharged by `liftReduction_perfectCompleteness_image`; the quotient
half is unconditional in the digits (`rhoDigitsShort_of_half_le`). -/
theorem liftReduction_perfectCompleteness_params {F : Type} [Field F] [SampleableType F]
    (P : HonestRangeParams q)
    (K : LiftCom
      (LiftedWitness Φ (rlinCols innerRows messageDigits innerDigits zDigits m r)
        (rlinRows innerRows outerRows dRows))
      (liftShort Φ P.γ P.bZero))
    (φF : ZMod q →+* F)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp)) (hd : 0 < Φ.φ.natDegree)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) :
    (liftReduction (oSpec := oSpec) (F := F) Φ P.γ P.bZero K hd).perfectCompleteness init impl
      (relRlinImage (zDigits := zDigits) Φ pp base ω P.γ) (relLift Φ P.γ P.bZero K φF) :=
  liftReduction_perfectCompleteness_image Φ P.hbZero P.hbZeroq P.hbZeroγ K φF init impl hd
    pp base ω

omit [NeZero q] in
/-- **Seam 3 — the lift's output feeds the batching bridge**, at the bundled `bZero`. The bridge's
two honest range hypotheses are exactly the bundled ones, and `relLift γ bZero` is *literally* the
bridge's input relation, so the two links meet on the nose. No arity conditions are needed on this
side (they belong to the pull-back). -/
theorem batchReduction_perfectCompleteness_params {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n μ m₀ m₁ : ℕ} (P : HonestRangeParams q)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ P.γ P.bZero))
    (φF : ZMod q →+* F) (hd : 0 < Φ.φ.natDegree) :
    (batchReduction (oSpec := oSpec) Φ P.γ P.bZero K).perfectCompleteness init impl
      (relLift Φ P.γ P.bZero K φF)
      (relBatched Φ m₀ m₁ P.γ P.bZero K φF P.bZero) :=
  batchReduction_perfectCompleteness Φ m₀ m₁ P.γ P.bZero init impl K φF P.bZero
    P.one_lt_bZero hd P.hγZero P.digitBaseOk_range

end Seams

/-! ## The prefix, composed

The reduction below appends the polynomial bridge, `QuadEval`, the `R^lin` adapter, the HMZ25 lift,
the batching bridge, and the nested zero-check.

It carries one parameter boundary the per-seam results above do not. The batching bridge itself
needs only the honest orientations in `HonestRangeParams`, but
`nestedZeroCheckReduction_perfectCompleteness` is stated on all of `relBatched`: since that
relation forgets shortness, the theorem re-derives it from the range identity and needs the reverse
inequalities `bZero - 1 ≤ γ` and `bZero - 1 ≤ q / 2`. The prefix is therefore available only at a
bidirectional — hence pinned — parameterization; a shortness-preserving honest seam between
batching and zero-check is what would remove those two hypotheses. -/

section CompletePrefix

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits zBound m r m₀ m₁ : Nat}
  {ω : ℕ}
variable {F : Type} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] [SampleableType F]

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

/-- The honest protocol from the polynomial-level evaluation bridge through the nested
zero-check. -/
def completePrefixReduction (P : HonestRangeParams q)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hqm : q ≤ P.b ^ messageDigits) (hcap : zBound ≤ balancedDigitCapacity P.b zDigits)
    (K : LiftCom (LiftedWitness Φ μ₀ n₀) (liftShort Φ P.γ P.bZero))
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
      (boundedBalancedZmodDigitDecomposition P.b zDigits zBound P.hb hcap)).append
    ((rlinReduction (oSpec := oSpec) (zDigits := zDigits) Φ pp (P.b : ZMod q) ω P.γ).append
    ((liftReduction (oSpec := oSpec) (F := F) Φ P.γ P.bZero K hd).append
    ((batchReduction (oSpec := oSpec) Φ P.γ P.bZero K).append
      (nestedZeroCheckReduction (oSpec := oSpec) (TCom := K.TCom)
        (Wit := LiftedWitness Φ μ₀ n₀) Φ m₀ m₁)))))

/-- The honest prefix's verifier is a total deterministic verdict on its transcript. -/
def completePrefixReductionPureForm (P : HonestRangeParams q)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hqm : q ≤ P.b ^ messageDigits) (hcap : zBound ≤ balancedDigitCapacity P.b zDigits)
    (K : LiftCom (LiftedWitness Φ μ₀ n₀) (liftShort Φ P.γ P.bZero))
    (hd : 0 < Φ.φ.natDegree) :
    (completePrefixReduction (oSpec := oSpec) (F := F) (ω := ω) (m₀ := m₀) (m₁ := m₁)
      Φ P pp hqm hcap K hd).verifier.PureForm :=
  ⟨_, fun _ _ => rfl⟩

omit [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] [SampleableType F] in
/-- The honest prefix prover returns its output without oracle queries. -/
theorem completePrefixReduction_outputIsPure (P : HonestRangeParams q)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hqm : q ≤ P.b ^ messageDigits) (hcap : zBound ≤ balancedDigitCapacity P.b zDigits)
    (K : LiftCom (LiftedWitness Φ μ₀ n₀) (liftShort Φ P.γ P.bZero))
    (hd : 0 < Φ.φ.natDegree) :
    (completePrefixReduction (oSpec := oSpec) (F := F) (ω := ω) (m₀ := m₀) (m₁ := m₁)
      Φ P pp hqm hcap K hd).prover.OutputIsPure := by
  repeat' apply Prover.OutputIsPure.append
  all_goals exact ⟨_, fun _ => rfl⟩

omit [DecidableEq F] in
/-- The honest Hachi prefix is perfectly complete from the short-message evaluation relation
to the nested zero-check relation. -/
theorem completePrefixReduction_perfectCompleteness
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
        (CarrierCom Φ dRows) (ShortChallenge Φ ω) r).Challenge i)]
    {m₀ m₁ : ℕ} (P : HonestRangeParams q)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hqm : q ≤ P.b ^ messageDigits) (hcap : zBound ≤ balancedDigitCapacity P.b zDigits)
    (hmul : Rq.HasMulLInftyBound Φ) (hzb : 2 ^ r * ω * (P.b / 2) ≤ zBound)
    (hmd : 0 < messageDigits) (hτ : 0 < zDigits) (hd : 0 < Φ.φ.natDegree)
    (K : LiftCom (LiftedWitness Φ μ₀ n₀) (liftShort Φ P.γ P.bZero))
    (φF : ZMod q →+* F) (hμn : (μ₀ + n₀ * rhoDigitCount q P.bZero) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hZeroγ : P.bZero - 1 ≤ P.γ)
    {βSq κ : ℕ} :
    (completePrefixReduction (oSpec := oSpec) (F := F) (ω := ω) (m₀ := m₀) (m₁ := m₁)
      Φ P pp hqm hcap K hd).perfectCompleteness init impl
      (relPolyEvalMsgShort Φ pp (P.b : ZMod q) βSq P.γ κ (P.b / 2))
      (relNestedZeroCheck Φ m₀ m₁ P.γ P.bZero K φF P.bZero) := by
  have hBridge (start : ProbComp σ) :=
    bridgeReduction_perfectCompleteness_msgShort Φ start impl pp (P.b : ZMod q) βSq P.γ κ
      (P.b / 2)
  have hQuad (start : ProbComp σ) :=
    quadEvalReduction_perfectCompleteness (zDigits := zDigits) (ω := ω)
      (βSq := βSq) (γ := P.γ) (κ := κ) (msgBound := P.b / 2)
      Φ start impl pp (balancedZmodDigitDecomposition P.b messageDigits P.hb hqm)
      (boundedBalancedZmodDigitDecomposition P.b zDigits zBound P.hb hcap)
      hmul hmd hτ hd hzb
      (fun x e => le_trans (balancedZmodDigit_natAbs_le P.hb hqm P.hbq x e) P.hbγ)
      (fun x e => le_trans (boundedBalancedZmodDigit_natAbs_le P.hb P.hbq x e) P.hbγ)
  have hRlin (start : ProbComp σ) :=
    rlinReduction_perfectCompleteness_params (zDigits := zDigits) (ω := ω)
    Φ P start impl pp (P.b : ZMod q)
  have hLift (start : ProbComp σ) :=
    liftReduction_perfectCompleteness_params (zDigits := zDigits) (ω := ω)
    Φ P K φF start impl hd pp (P.b : ZMod q)
  have hBatch (start : ProbComp σ) :=
    batchReduction_perfectCompleteness_params (m₀ := m₀) (m₁ := m₁)
    Φ P start impl K φF hd
  have hZero (start : ProbComp σ) := nestedZeroCheckReduction_perfectCompleteness
    Φ m₀ m₁ P.γ P.bZero start impl K φF P.bZero hd hμn hZeroγ P.digitBaseOk
  let sampleEmptyNested : ∀ i, SampleableType
      (((!p[] : ProtocolSpec 0) ++ₚ pSpecNestedZeroCheck F m₀ m₁).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
      (h₂ := instSampleableTypeChallengePSpecNestedZeroCheck)
  let sampleScalarTail : ∀ i, SampleableType
      ((pSpecScalar K.TCom F ++ₚ
        ((!p[] : ProtocolSpec 0) ++ₚ pSpecNestedZeroCheck F m₀ m₁)).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := CoordinateWise.ScalarRound.instSampleableTypeChallengePSpecScalar)
      (h₂ := sampleEmptyNested)
  let sampleEmptyScalarTail : ∀ i, SampleableType
      (((!p[] : ProtocolSpec 0) ++ₚ
        (pSpecScalar K.TCom F ++ₚ
          ((!p[] : ProtocolSpec 0) ++ₚ pSpecNestedZeroCheck F m₀ m₁))).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
      (h₂ := sampleScalarTail)
  let sampleQuadTail : ∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
          (CarrierCom Φ dRows) (ShortChallenge Φ ω) r ++ₚ
        ((!p[] : ProtocolSpec 0) ++ₚ
          (pSpecScalar K.TCom F ++ₚ
            ((!p[] : ProtocolSpec 0) ++ₚ pSpecNestedZeroCheck F m₀ m₁)))).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := by infer_instance)
      (h₂ := sampleEmptyScalarTail)
  have hBatchZero (start : ProbComp σ) := Reduction.append_perfectCompleteness_of_pure_verifiers
    _ _ ⟨_, fun _ _ => rfl⟩ ⟨_, fun _ _ => rfl⟩
    (fun _ => Or.inl ⟨_, fun _ => rfl⟩) (hBatch start) (fun s => hZero (pure s))
  have hLiftZero (start : ProbComp σ) := Reduction.append_perfectCompleteness_of_pure_verifiers
    _ _ ⟨_, fun _ _ => rfl⟩ ⟨_, fun _ _ => rfl⟩
    (fun _ => Or.inl ⟨_, fun _ => rfl⟩) (hLift start) (fun s => hBatchZero (pure s))
  have hRlinZero (start : ProbComp σ) := Reduction.append_perfectCompleteness_of_pure_verifiers
    _ _ ⟨_, fun _ _ => rfl⟩ ⟨_, fun _ _ => rfl⟩
    (fun _ => Or.inl ⟨_, fun _ => rfl⟩) (hRlin start) (fun s => hLiftZero (pure s))
  have hQuadZero (start : ProbComp σ) := Reduction.append_perfectCompleteness_of_pure_verifiers
    _ _ ⟨_, fun _ _ => rfl⟩ ⟨_, fun _ _ => rfl⟩
    (fun _ => Or.inl ⟨_, fun _ => rfl⟩) (hQuad start) (fun s => hRlinZero (pure s))
  exact Reduction.append_perfectCompleteness_of_pure_verifiers
    _ _ ⟨_, fun _ _ => rfl⟩ ⟨_, fun _ _ => rfl⟩
    (fun _ => Or.inl ⟨_, fun _ => rfl⟩) (hBridge init) (fun s => hQuadZero (pure s))

end CompletePrefix

/-! ## Through the sumcheck

`completePrefixReduction` stops at `relNestedZeroCheck`. `Sumcheck/Completeness.lean` carries that
relation on to the evaluation claim `relWEvalClaim` — bridge, `m₀` paired rounds, final
evaluation — so the two compose into an honest protocol from the polynomial-evaluation relation
all the way to the evaluation claim on the committed table.

The sumcheck's arity appears as `m₀ = M + 1`: the loop needs at least one cube coordinate to fold,
the same successor shape `Sumcheck/RoundPoly.lean` and the round soundness theorem use. -/

section ThroughSumcheck

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits zBound m r M m₁ : Nat}
  {ω : ℕ}
variable {F : Type} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] [SampleableType F]

local notation "μ₀" => rlinCols innerRows messageDigits innerDigits zDigits m r
local notation "n₀" => rlinRows innerRows outerRows dRows

/-- The honest Hachi protocol from the polynomial-evaluation claim through the sumcheck: the
prefix (`completePrefixReduction`) followed by the local sumcheck
(`sumcheckReduction`). -/
def completeThroughSumcheckReduction (P : HonestRangeParams q)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hqm : q ≤ P.b ^ messageDigits) (hcap : zBound ≤ balancedDigitCapacity P.b zDigits)
    (K : LiftCom (LiftedWitness Φ μ₀ n₀) (liftShort Φ P.γ P.bZero))
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
      Φ P pp hqm hcap K hd).append
    (sumcheckReduction (oSpec := oSpec) (TCom := K.TCom) Φ m₁ P.γ P.bZero hbZero φF)

/-- The through-sumcheck verifier is deterministic and may reject a failed round check. -/
def completeThroughSumcheckReductionGuardedForm (P : HonestRangeParams q)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hqm : q ≤ P.b ^ messageDigits) (hcap : zBound ≤ balancedDigitCapacity P.b zDigits)
    (K : LiftCom (LiftedWitness Φ μ₀ n₀) (liftShort Φ P.γ P.bZero))
    (hd : 0 < Φ.φ.natDegree) (hbZero : 0 < P.bZero) (φF : ZMod q →+* F) :
    (completeThroughSumcheckReduction (oSpec := oSpec) (F := F) (ω := ω) (M := M) (m₁ := m₁)
      Φ P pp hqm hcap K hd hbZero φF).verifier.GuardedForm :=
  (completePrefixReductionPureForm Φ P pp hqm hcap K hd).toGuardedForm.append
    (sumcheckReductionGuardedForm Φ m₁ P.γ P.bZero P.bZero K hbZero φF)

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

omit [DecidableEq F] in
/-- The honest chain through sumcheck is perfectly complete from the short-message evaluation
relation to the witness-evaluation claim. -/
theorem completeThroughSumcheckReduction_perfectCompleteness
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
        (CarrierCom Φ dRows) (ShortChallenge Φ ω) r).Challenge i)]
    (P : HonestRangeParams q)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hqm : q ≤ P.b ^ messageDigits) (hcap : zBound ≤ balancedDigitCapacity P.b zDigits)
    (hmul : Rq.HasMulLInftyBound Φ) (hzb : 2 ^ r * ω * (P.b / 2) ≤ zBound)
    (hmd : 0 < messageDigits) (hτ : 0 < zDigits) (hd : 0 < Φ.φ.natDegree)
    (hbZero : 0 < P.bZero)
    (K : LiftCom (LiftedWitness Φ μ₀ n₀) (liftShort Φ P.γ P.bZero))
    (φF : ZMod q →+* F) (hμn : (μ₀ + n₀ * rhoDigitCount q P.bZero) * Φ.φ.natDegree ≤ 2 ^ (M + 1))
    (hZeroγ : P.bZero - 1 ≤ P.γ)
    {βSq κ : ℕ} :
    (completeThroughSumcheckReduction (oSpec := oSpec) (F := F) (ω := ω) (M := M) (m₁ := m₁)
      Φ P pp hqm hcap K hd hbZero φF).perfectCompleteness init impl
      (relPolyEvalMsgShort Φ pp (P.b : ZMod q) βSq P.γ κ (P.b / 2))
      (relWEvalClaim Φ (M + 1) P.γ P.bZero P.bZero K φF) :=
  Reduction.append_perfectCompleteness_of_guarded_verifiers _ _
    (completePrefixReductionPureForm Φ P pp hqm hcap K hd).toGuardedForm
    (sumcheckReductionGuardedForm Φ m₁ P.γ P.bZero P.bZero K hbZero φF)
    (fun _ => Or.inl (completePrefixReduction_outputIsPure Φ P pp hqm hcap K hd))
    (completePrefixReduction_perfectCompleteness (zDigits := zDigits) (ω := ω)
      (m₀ := M + 1) (m₁ := m₁) (βSq := βSq) (κ := κ)
      Φ P init impl pp hqm hcap hmul hzb hmd hτ hd K φF hμn hZeroγ)
    (fun s => sumcheckReduction_perfectCompleteness Φ m₁ P.γ P.bZero P.bZero
      (pure s) impl K hbZero P.one_lt_bZero φF hd hμn)

end ThroughSumcheck



end ArkLib.Lattices.Ajtai.InnerOuter
