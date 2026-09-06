/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval.Basic
import ArkLib.Commitments.Functional.Hachi.EndPiece.Basic
import ArkLib.Commitments.Functional.Hachi.Sumcheck.FinalEval
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Package
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

/-!
# Hachi — the composed opening certificate

Each Hachi [NOZ26] subprotocol is formalized in its own file and exported as a CWSS *package*,
bundling a verifier with its proof of coordinate-wise special soundness. This file imports those
packages and chains them with the universal append `▷`, which dispatches on the factors' package
kinds and lifts each to the join automatically. Only the ordinary relation seam has to match;
escape events compose without a seam. The composed chain's `isCWSS` field is the certificate for
the whole reduction. This file hosts no protocol of its own.

The opening decomposes into three pieces:

1. **`iteration`** — the nine chained subprotocols of the table below, reducing the
   polynomial-evaluation claim `relPolyEval` to the evaluation claim `relWEvalClaim`
   (`mle[w̃](a) = y′`) on the committed table.
2. **`endPiece`** (`EndPiece/`) — the closing link: the prover sends the reduced witness and the
   verifier checks the reduced claim against it directly.
3. **`evaluation`** — `iteration ⧺ endPiece`, the complete opening argument.

## The composed verifier chain, seam by seam

Every row's relations are the ordinary protocol relations. The cryptographic failure modes of
extraction live in the rows' **escape events** (`ChallengeTree.EscapeEvent`), which enter each
certificate as a disjunct of its *conclusion* and compose along the chain by
`ChallengeTree.EscapeEvent.append` — so factors tracking breaks of different assumptions need only
match their relation seam.

```text
 # | link (file)                | rounds: wire         | relIn → relOut            | CWSS, k
---+----------------------------+----------------------+---------------------------+---------------
 1 | bridge (QuadEval/Bridge)   | 0                    | relPolyEval → relIn       | any (0 chals)
 2 | QuadEval (QuadEval/*)      | msg v; c ∈ C^{2^r}   | relIn → relOut (Eq. 20)   | ℓ=2^r, k=2 (L8)
 3 | R^lin (RingSwitch/Rlin)    | 0                    | relOut → relRlin          | any
 4 | lift (…/Reduction)         | msg t; α ∈ F         | relRlin → relLift         | ℓ=1, k=2d (L9)
 5 | batch (ZeroCheck/Batch)    | 0                    | relLift → relBatched      | any
 6 | zero-check (…/Reduction)   | scalar coords of τ₀,τα| relBatched → relNestedZeroCheck | k=2/rnd
 7 | sc bridge (Sumcheck/Bridge)| 0                    | relNestedZeroCheck → nestedRoundRel 0 | any
 8 | rounds ×m₀ (…/Rounds)      | (g-pair; aᵢ)ᵢ        | nestedRoundRel 0 → … m₀  | ℓ=1, k=2b+1
   |  — GUARDED: gᵢ(0)+gᵢ(1)=z |                      |                           |  (L11)/round
 9 | final eval (…/FinalEval)   | msg y′ ∈ F           | nestedRoundRel m₀ → relWEvalClaim | GUARDED
```

**Which rows carry an escape event.** Row 2 carries `QuadEval`'s Module-SIS(B/D) break of the fixed
key (`quadEvalEscLocal`); rows 4, 6 and 8 carry the weak-binding collision of the `w̃`-commitment
(`LiftCom.Collision`, via `Lift.escEvent` / `nestedZeroCheckEsc` / `roundEsc`). Every other row is
escape-free and enters the chain at the never-firing event through `▷`'s lossless lift.

Rows 1–7 have **pure** verifiers: every check constrains either retained statement data or the
never-sent witness, so it lives in the output relation. Rows 8 and 9 are **guarded**: their runtime
check reads data the next statement type drops (the previous sumcheck target; the final targets),
and they compose through the guarded append theorem.

Row 6 departs from the paper. Figure 5 is sound as printed, but Lemma 10's *deterministic* star
extraction is not provable — a coordinate-wise star only certifies vanishing on an axis cross.
Each coordinate of `τ₀` and `τα` is therefore sampled in a separate scalar round, so the accepting
transcript tree is a path-dependent complete binary evaluation tree, on which vanishing does
determine a multilinear polynomial. No prover message separates those rounds, so the interactive
protocol is unchanged; only the tree shape the extractor is handed changes. See
`ZeroCheck/Reduction.lean` and `docs/kb/audits/noz26-zero-check-lemma10.md`.

The `Recursion/` adapters that would carry an iteration's evaluation claim to the next ring are
not composed here; see `Recursion/Basic.lean`.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
* [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings and Applications to Lattice-Based Zero-Knowledge Proofs*][LS18]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.SingleRound

section Evaluation

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α : ℕ}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]

/-- Shorthand for the §4.3 chain's `R^lin` column count at the Eq. (20) instantiation. -/
local notation "μ₀" => rlinCols innerRows messageDigits innerDigits zDigits m r
/-- Shorthand for the §4.3 chain's `R^lin` row count at the Eq. (20) instantiation. -/
local notation "n₀" => rlinRows innerRows outerRows dRows

/-- The wire format of the `iteration`'s pure prefix (rows 1–7): bridge (0) ⧺ `QuadEval` (2) ⧺
R^lin adapter (0) ⧺ lift (2) ⧺ batching (0) ⧺ zero-check (m₀+m₁) ⧺ sumcheck bridge (0),
right-associated as `▷` composes them. -/
abbrev coreSpec (ω m₀ m₁ : ℕ) (TCom F : Type) :=
  (((!p[] : ProtocolSpec 0) ++ₚ
      pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r)) ++ₚ
    ((!p[] : ProtocolSpec 0) ++ₚ
      (CoordinateWise.ScalarRound.pSpecScalar TCom F ++ₚ
        ((!p[] : ProtocolSpec 0) ++ₚ
          (pSpecNestedZeroCheck F m₀ m₁ ++ₚ (!p[] : ProtocolSpec 0)))))

/-- Sampleability of the rows 1–7 prefix's challenges, assembled **by name** from the per-link
instances: the generic append instance does not fire through the reducible `++ₚ` (its
discrimination keys degenerate), so compound wire formats get their instances built explicitly.
Takes a sampler for the fold challenges (`ShortChallenge`) as a hypothesis. -/
@[reducible] def coreSpecSampleable (ω m₀ m₁ : ℕ) (TCom F : Type) [SampleableType F]
    [SampleableType (ShortChallenge 𝓜(q, α) ω)] :
    ∀ i, SampleableType
      ((coreSpec (q := q) (α := α) (dRows := dRows) (r := r)
        ω m₀ m₁ TCom F).Challenge i) :=
  ProtocolSpec.instSampleableTypeChallengeAppend
    (h₁ := ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
      (h₂ := CoordinateWise.SingleRound.instSampleableTypeChallengePSpec))
    (h₂ := ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
      (h₂ := ProtocolSpec.instSampleableTypeChallengeAppend
        (h₁ := CoordinateWise.ScalarRound.instSampleableTypeChallengePSpecScalar)
        (h₂ := ProtocolSpec.instSampleableTypeChallengeAppend
          (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
          (h₂ := ProtocolSpec.instSampleableTypeChallengeAppend
          (h₁ := instSampleableTypeChallengePSpecNestedZeroCheck)
            (h₂ := ProtocolSpec.instSampleableTypeChallengeEmpty)))))

/-- **Escape-threaded CWSS of the `Rq`-level polynomial-evaluation step** (Hachi
[NOZ26, §4.2, Figure 3]): rows 1–2, the polynomial-level bridge followed by `QuadEval`, along a
single relation seam. The bridge is escape-free and `QuadEval` escape-aware, so `▷` lifts the
bridge at the never-firing event and the composed event fires exactly when `QuadEval`'s own event
fires on the suffix tree.

The endpoint relations are `relPolyEval` and `relOut`, and the extractor is the composed algorithm
(the bridge's pull-back run on the prefix tree of `QuadEval`'s Lemma 8 extractor).

Named separately from `iteration` because it is the paper's Figure 3 reduction on its own,
independent of the §4.3 chain that follows; `iteration` reuses exactly this composite as its first
two factors. Pinned to `𝓜(q, α)` with the [LS18] hypotheses of
`quadEval_coordinateWiseSpecialSoundWithEscape`. -/
theorem eval_coordinateWiseSpecialSoundWithEscape (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (hq5 : q % 8 = 5) {b ω γ : ℕ}
    (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl
      (CWSSStructure.ofIsEmpty.append
        (foldStructure (CarrierCom := CarrierCom 𝓜(q, α) dRows)
          (C := ShortChallenge 𝓜(q, α) ω) (r := r)))
      ((bridgePackage (oSpec := oSpec) 𝓜(q, α) init impl pp (b : ZMod q)
            (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) ▷
          quadEvalPackage init impl hq5 hκ hτ pp).esc)
      (relPolyEval 𝓜(q, α) pp (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω))
      (relOut (zDigits := zDigits) 𝓜(q, α) pp (b : ZMod q) ω γ)
      ((bridgeVerifier (oSpec := oSpec) (innerRows := innerRows) (messageDigits := messageDigits)
          (outerRows := outerRows) (innerDigits := innerDigits) (dRows := dRows) (m := m) (r := r)
          𝓜(q, α)).append
        (verifier (oSpec := oSpec) (ω := ω) 𝓜(q, α)))
      ((bridgePackage (oSpec := oSpec) 𝓜(q, α) init impl pp (b : ZMod q)
            (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) ▷
          quadEvalPackage init impl hq5 hκ hτ pp).extractor) :=
  (bridgePackage (oSpec := oSpec) 𝓜(q, α) init impl pp (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) ▷
      quadEvalPackage init impl hq5 hκ hτ pp).isCWSS

/-- **One Hachi evaluation iteration** (rows 1–9): the subprotocols in one line of `▷`s — bridge ▷
`QuadEval` ▷ `R^lin` adapter ▷ HMZ25 lift ▷ batching bridge ▷ zero-check ▷ sumcheck bridge (pure
verifiers) — closed by the guarded sumcheck tail: the `m₀` paired sumcheck rounds (Lemma 11) and
the final-evaluation step. Every relation seam is definitional (`roundsChain` re-pins the loop's
relations to the round-`0`/round-`m₀` seam relations), so the whole chain composes by `▷`, with
pure factors lifted into the escape-guarded world automatically.

The iteration reduces `relPolyEval` to the evaluation claim `relWEvalClaim` —
`mle[w̃](a) = y′` for the committed table `w̃` — the claim the end-piece consumes. Its escape event
is the `EscapeEvent.append`-nesting of the per-row events (rows 2, 4, 6, 8), each on its own
subtree; `iteration.isCWSS` is the one-iteration certificate.

Every factor carries its verdict/guard maps as data (`Verifier.PureForm` /
`Verifier.GuardedForm`), so the composed extractor `(iteration …).extractor` is executable — no
`Classical.choice` at any seam. -/
def iteration (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ m₀ m₁ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) (liftShort 𝓜(q, α) γ b))
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (hb : b - 1 ≤ γ)
    (hdig : DigitBaseOk q γ b)
    (hcov : (μ₀ + n₀ * rhoDigitCount q b) * (𝓜(q, α)).φ.natDegree ≤ 2 ^ m₀)
    (hn : n₀ ≤ 2 ^ m₁) :
    EscapeGCWSSPackage init impl
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (WEvalStatement K.TCom F m₀)
      (LiftedWitness 𝓜(q, α) μ₀ n₀)
      (coreSpec (q := q) (α := α) (dRows := dRows) (r := r) ω m₀ m₁ K.TCom F ++ₚ
        roundsSpec F b m₀ ++ₚ pSpecFinalEval F) :=
  haveI : ∀ i, SampleableType
      ((((!p[] : ProtocolSpec 0) ++ₚ
        pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r)).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
      (h₂ := CoordinateWise.SingleRound.instSampleableTypeChallengePSpec)
  haveI i₀ := coreSpecSampleable (q := q) (α := α) (dRows := dRows) (r := r)
    ω m₀ m₁ K.TCom F
  haveI : ∀ i, SampleableType
      (((coreSpec (q := q) (α := α) (dRows := dRows) (r := r)
        ω m₀ m₁ K.TCom F) ++ₚ
        roundsSpec F b m₀).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend (h₁ := i₀)
      (h₂ := roundsSpecSampleable F b m₀)
  have hb1 : 1 < b := hdig.one_lt
  have hbpos : 0 < b := Nat.zero_lt_one.trans hb1
  let bridge := bridgePackage (oSpec := oSpec) 𝓜(q, α) init impl pp (b : ZMod q)
    (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω)
  let quadEval := quadEvalPackage init impl hq5 hκ hτ pp
  let rlin := rlinPackage (zDigits := zDigits) 𝓜(q, α) init impl pp (b : ZMod q) ω γ
  let lift := liftPackage 𝓜(q, α) γ b K φF init impl hd
  let batch := batchPackage 𝓜(q, α) m₀ m₁ γ b init impl K φF b hb1 hn hd hcov hb hdig
  let zeroCheck := nestedZeroCheckPackage 𝓜(q, α) m₀ m₁ γ b init impl K φF b
  let sumcheckBridge :=
    nestedSumcheckBridgePackage 𝓜(q, α) m₀ m₁ γ b init impl K φF b hb1 hd hcov
  let rounds := roundsChain 𝓜(q, α) m₀ m₁ γ b b init impl K φF hbpos m₀ le_rfl
  let finalEval := finalEvalPackage 𝓜(q, α) m₀ m₁ γ b b init impl K φF
  let core : EscapeCWSSPackage init impl
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (NestedRoundStatement 𝓜(q, α) K.TCom F n₀ μ₀ m₀ m₁ 0)
      (LiftedWitness 𝓜(q, α) μ₀ n₀)
      (coreSpec (q := q) (α := α) (dRows := dRows) (r := r) ω m₀ m₁ K.TCom F) :=
    (bridge ▷ quadEval) ▷ rlin ▷ lift ▷ batch ▷ zeroCheck ▷ sumcheckBridge
  (core ▷ rounds) ▷ finalEval

/-- **Escape-threaded coordinate-wise special soundness of one Hachi evaluation iteration.** The
composed verifier of rows 1–9 is CWSS over the endpoint relations `relPolyEval` and
`relWEvalClaim`, at the composed extraction algorithm `(iteration …).extractor`, with
`(iteration …).esc` as the certificate's escape disjunct. -/
theorem hachi_iteration_coordinateWiseSpecialSoundWithEscape (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ m₀ m₁ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) (liftShort 𝓜(q, α) γ b))
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (hb : b - 1 ≤ γ)
    (hdig : DigitBaseOk q γ b)
    (hcov : (μ₀ + n₀ * rhoDigitCount q b) * (𝓜(q, α)).φ.natDegree ≤ 2 ^ m₀)
    (hn : n₀ ≤ 2 ^ m₁) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl
      (iteration (zDigits := zDigits) (ω := ω) (m₀ := m₀) (m₁ := m₁) init impl hq5 hκ hτ
        K pp φF hd hb hdig hcov hn).struct
      (iteration (b := b) (zDigits := zDigits) (ω := ω) (m₀ := m₀) (m₁ := m₁) init impl
        hq5 hκ hτ K pp φF hd hb hdig hcov hn).esc
      (relPolyEval 𝓜(q, α) pp (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω))
      (relWEvalClaim 𝓜(q, α) m₀ γ b b K φF)
      (iteration (zDigits := zDigits) (ω := ω) (m₀ := m₀) (m₁ := m₁) init impl hq5 hκ
        hτ K pp φF hd hb hdig hcov hn).verifier
      (iteration (b := b) (zDigits := zDigits) (ω := ω) (m₀ := m₀) (m₁ := m₁) init impl
        hq5 hκ hτ K pp φF hd hb hdig hcov hn).extractor :=
  (iteration (zDigits := zDigits) (ω := ω) (m₀ := m₀) (m₁ := m₁) init impl hq5 hκ hτ
    K pp φF hd hb hdig hcov hn).isCWSS

/-- **The complete Hachi evaluation** (the opening argument of the commitment scheme): one
`iteration` concatenated with the `endPiece` (`EndPiece/`). The composed reduction takes
`relPolyEval` all the way to the trivial claim — after the end-piece the verifier has checked the
reduced witness against the reduced claim itself, so nothing is left to reduce. The certificate is
`(evaluation …).isCWSS`; the end-piece factor is escape-free, so it adds no disjunct. -/
def evaluation (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ m₀ m₁ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) (liftShort 𝓜(q, α) γ b))
    [BEq K.TCom] [LawfulBEq K.TCom]
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (hb : b - 1 ≤ γ)
    (hdig : DigitBaseOk q γ b)
    (hcov : (μ₀ + n₀ * rhoDigitCount q b) * (𝓜(q, α)).φ.natDegree ≤ 2 ^ m₀)
    (hn : n₀ ≤ 2 ^ m₁) :
    EscapeGCWSSPackage init impl
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      Unit Unit
      ((coreSpec (q := q) (α := α) (dRows := dRows) (r := r) ω m₀ m₁ K.TCom F ++ₚ
          roundsSpec F b m₀ ++ₚ pSpecFinalEval F) ++ₚ
        pSpecEndPiece (LiftedWitness 𝓜(q, α) μ₀ n₀)) :=
  haveI i₀ := coreSpecSampleable (q := q) (α := α) (dRows := dRows) (r := r)
    ω m₀ m₁ K.TCom F
  haveI i₁ : ∀ i, SampleableType
      (((coreSpec (q := q) (α := α) (dRows := dRows) (r := r)
        ω m₀ m₁ K.TCom F) ++ₚ
        roundsSpec F b m₀).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend (h₁ := i₀)
      (h₂ := roundsSpecSampleable F b m₀)
  haveI : ∀ i, SampleableType
      ((((coreSpec (q := q) (α := α) (dRows := dRows) (r := r)
          ω m₀ m₁ K.TCom F) ++ₚ
          roundsSpec F b m₀) ++ₚ pSpecFinalEval F).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend (h₁ := i₁)
      (h₂ := instSampleableTypeChallengePSpecFinalEval)
  let iter := iteration (b := b) (zDigits := zDigits) (ω := ω) (m₀ := m₀) (m₁ := m₁) init impl
    hq5 hκ hτ K pp φF hd hb hdig hcov hn
  let closing := endPiece 𝓜(q, α) m₀ γ b b init impl K φF
  iter ▷ closing

end Evaluation

end ArkLib.Lattices.Ajtai.InnerOuter
