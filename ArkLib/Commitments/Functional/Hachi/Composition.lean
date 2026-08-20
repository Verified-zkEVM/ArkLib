/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval.Basic
import ArkLib.Commitments.Functional.Hachi.Sumcheck.FinalEval
import ArkLib.Commitments.Functional.Hachi.Recursion.TraceHandoff
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Package
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

/-!
# Hachi — the CWSS composition home

This is the designated home of the growing n-ary composition of the subprotocols of Hachi [NOZ26],
a lattice-based multilinear polynomial commitment scheme. Each subprotocol is formalized in its own
file and exported as a CWSS *package* in the weakest of the four kinds it honestly lives in —
`CWSSPackage`, `GCWSSPackage` (guarded verifier: may `failure` at runtime), `EscapeCWSSPackage`
(extraction may exhibit a cryptographic escape), `EscapeGCWSSPackage` (both) — bundling the verifier
with its proof of coordinate-wise special soundness (CWSS), the knowledge-soundness notion under
which a witness is extracted from a suitably structured tree of accepting transcripts. This file
only **imports those packages and chains them** with the universal append `▷`, which dispatches on
the factors' package kinds and lifts each to the join automatically (both lifts are lossless). Only
the ordinary relation seam has to match — escape events compose without a seam. The guarded
composition theorem lives in
`OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean`. The composed chain's
`isCWSS` field is the CWSS certificate for the whole reduction. (Hachi as a `Commitment.Scheme` —
the honest committer `keygen`/`commit` and the `hachi` functional commitment — lives in the
sibling `Commitment.lean`.)

## The three layers of this file

1. **`evalChain`** (sorry-free, finished): the polynomial-level bridge ▷ `QuadEval`
   (§4.2 / Figure 3 / Lemma 8) — an escape-aware package whose event is `QuadEval`'s.
2. **`openCore`** (sorry-free, finished): the escape-aware `evalChain` extended by the
   §4.3 stages up to the sumcheck bridge — R^lin adapter (F2) ▷ HMZ25 lift (Figure 4 / Lemma 9)
   ▷ batching bridge (Eqs. (22)–(23)) ▷ zero-check (Figure 5 / **corrected** Lemma 10) ▷
   sumcheck bridge.
3. **`openingChain`** (finished through row 9, skeleton from row 10): the pure `openCore` ▷ the
   paired sumcheck loop (Figure 6 / Lemma 11, `m₀` guarded rounds) ▷ final evaluation (Figure 7
   tail) — both sorry-free — ▷ the §4.5 recursion adapters (pure partial evaluations ▷ pure
   `Z`-packing bridge ▷ guarded trace handoff), which are the skeleton, landing on
   the **next iteration's** `QuadEval` input relation over the next ring `Φ'` — the recursion
   loop's closing seam. The universal `▷` lifts each pure factor into the escape-guarded world
   automatically (`CoordinateWiseSpecialSoundness/Escape.lean`, package-lattice section); no
   explicit `.toGuarded` calls.

## The composed verifier chain, seam by seam

Top-to-bottom is one opening iteration of the ArkLib Hachi commitment, whose committed data is an
`Rq`-valued multilinear polynomial. The opening starts with the Figure 3 path, not with §3: the §3
packing head (extension-field claims into `Rq`-claims, via the generalized `RingSwitching` packing
phase) is a separate track that wraps *external* extension-field claims in front of `relPolyEval`;
the §4.5 adapters below close the recursion *internally*.

Every row's relations are the ordinary protocol relations. The cryptographic failure modes of
extraction live in the rows' **escape events** (`ChallengeTree.EscapeEvent`), which enter each
certificate as a disjunct of its *conclusion*, and compose along the chain by
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
10 | partials (Recursion/PartialEval)| msg (yᵢ)_{i≠0}  | relWEvalClaim → relPartialEval | any (pure)
11 | Z-pack (…/ZBatchBridge)    | 0                    | relPartialEval → relHatEval | any — ⚠ GAP
12 | handoff (…/TraceHandoff)   | msg p ∈ R′q          | relHatEval → relIn(Φ′) | any — GUARDED
   |                            |                      |  = next iteration's row 2 |
```

**Which rows carry an escape event.** Row 2 carries `QuadEval`'s Module-SIS(B/D) break of the fixed
key (`quadEvalEscLocal`); rows 4, 6 and 8 carry the weak-binding collision of the `w̃`-commitment
(`LiftCom.Collision`, via `Lift.escEvent` / `zeroCheckEsc` / `roundEsc`). Those four are
`EscapeCWSSPackage`/`EscapeGCWSSPackage`s; every other row is escape-free
(`CWSSPackage`/`GCWSSPackage`) and enters the chain at the never-firing event through the universal
`▷`'s lossless lift.

- Rows 1–7 have **pure** verifiers: every check constrains either retained statement data or the
  never-sent witness, so it lives in the output relation (the `QuadEval` precedent). Rows 8, 9,
  12 are **guarded**: their runtime check reads data the next statement type drops
  (the previous sumcheck target; the final targets; the packed claim value) — exactly the paper's
  runtime checks — and compose through the guarded append of `Guarded.lean`, which is proven
  (escape-threaded form included).
- Row 6 implements the **corrected Lemma 10**: the paper's uniform-vector star extraction is not
  provable (axis-cross counterexample). Each coordinate of `τ₀` and `τα` is instead sampled in a
  separate scalar round, so the accepting transcript tree becomes a path-dependent complete
  binary evaluation tree — `k = 2` at every round, and the multilinear identity test extraction
  needs. Since no prover message separates the rounds, the *interactive* protocol is unchanged
  from Figure 5; what changes is the tree shape the extractor is handed. The counterexample, the
  repair and their costs are spelled out in `ZeroCheck/Reduction.lean`; the full analysis is
  `docs/kb/audits/noz26-zero-check-lemma10.md`.
- Row 11 isolates the **§4.5/§3.2 partial-evaluation gap** found while auditing this skeleton:
  the packed claim of Eq. (26) pins only one `F`-linear functional of the per-slice values, so
  the paper's step is (apparently) not knowledge-sound as stated; the bridge's pull-back sorry is
  expected to be unprovable until a repair (batching challenge / generic §3.1 packing) is
  adopted; the analysis and the candidate repairs are in `Recursion/ZBatchBridge.lean`. All other
  sorries in the chain are honest skeleton work.
- Row 12 lands on plain `relIn Φ'`. Iteration
  `i+1` re-enters at `quadEvalPackage Φ'` directly (its bases are `eq`-tensor
  packings, not monomial bases, so the polynomial-level bridge of row 1 is head-only).
  Asymptotic termination (§4.4: reveal the final polynomial once small) and the concrete §4.5
  Greyhound/LaBRADOR cutoff are future zero-round tails at that seam.

## Sorry inventory of the composed chain (provenance of the certificate)

*Generic machinery*: **all of it is proven** (`sorryAx`-free). `Verifier.IsGuarded.append` and
`Verifier.append_coordinateWiseSpecialSoundWithEscape_of_guardedLeft` (`Guarded.lean`; the latter is
the fundamental obligation, stated escape-threaded at explicit guard data — the plain guarded
append is derived from it at the never-firing events). The two scalar-round assemblies
`coordinateWiseSpecialSoundWith(Escape)_of_mkWitness_scalar` and their guarded twin
(`ScalarRound.lean`) are proven, as are their readers, shape recovery, extractor and escape event.
So is the escape layer (`TranscriptTree/Basic.lean`, `CWSS/{Basic,Composition}.lean`,
`Escape.lean`) with its append theorem, the single-round escape assembly and
`quadEval_coordinateWiseSpecialSoundWithEscape`. Each sorried row carries its extraction
*algorithm* as an explicitly sorried `Extractor.TreeBased`.

**Rows 1–9 carry no sorried certificate** — and they compose clean: `#print axioms` on `openCore`,
`roundsChain`, `roundPackage`, `finalEvalPackage` and `nestedSumcheckBridgePackage` reports only
`propext`/`Classical.choice`/`Quot.sound`. The `sorryAx` in `openingChain` (and hence in
`hachi_iteration_coordinateWiseSpecialSoundWithEscape`) comes **only** from rows 10–12. The
remaining sorries inside `Hachi/` number 13: six in `Recursion/PartialEval.lean`, four in
`Recursion/TraceHandoff.lean`, two in `Recursion/ZBatchBridge.lean` (the ⚠ row-11 gap), and
`Commitment.lean`'s `opening`.

The `R^lin` adapter
(`rlinStmt`/`unstack`/`mem_relOut_of_relRlin`) and the HMZ25 lift (Lemma 9, `liftPackage.isCWSS`,
via the generic `Lift` layer on the proven scalar-round engine and the `QuotientLift` algebra)
are sorry-free and axiom-clean (rows 3–4). So are:

* row 5, the batching pull-back `mem_relLift_of_relBatched` — including the range-side soundness
  `H₀ ≡ 0 ⇒ liftShort` (`hZero_eq_zero_imp_liftShort`), so shortness is **derived**, not assumed,
  and `relBatched` stays norm-free;
* row 6, the **corrected Lemma 10**: `nestedZeroCheck_coordinateWiseSpecialSoundWithEscape` with
  its named extractor and the weak-binding event `nestedZeroCheckEsc`, on the concrete
  `CMlPolynomialEval` encodings `hZero`/`hAlpha` and the evaluation-tree zero test;
* row 7, the sum-to-point bridge `mem_relNestedZeroCheck_of_nestedRoundRel`;
* row 8, **Lemma 11**: `round_coordinateWiseSpecialSoundWithEscape` with its named
  `roundExtractor` and the weak-binding event `roundEsc`, on the generic *guarded* scalar-round
  engine plus the round-polynomial layer `Sumcheck/RoundPoly.lean`. It carries two load-bearing
  side conditions, `i < m₀` (a round needs a free cube coordinate) and `0 < b` (the range
  summand's `2b` degree pin degenerates at `b = 0`); the latter is `openingChain`'s `hbpos`.
* row 9, the **final evaluation**: `finalEval_coordinateWiseSpecialSoundWith` with its named
  `finalEvalExtractor` and the `finalCheck` encoding, on the no-challenge CWSS bridge and the
  evaluation factorizations `eval_sumcheckPolyZero` / `eval_sumcheckPolyAlpha`. No challenge round,
  hence no escape event: the step is a guarded *re-reading* of the final targets.

*Per-link math still sorried*: rows 10–12 only — the partial-evaluation head
(`partialEval_coordinateWiseSpecialSoundWith` + its encoding defs) and the trace handoff
(`handoff_coordinateWiseSpecialSoundWith` + `traceCheck`/`toNextQuadEvalStatement`/`hatEval`).
Every sorried encoding def carries an in-situ `**Sorried**` docstring.

*Where the norm sits after row 8.* `relBatched` is deliberately norm-free (row 5 *derives*
`liftShort` from `H₀ ≡ 0`), but from `nestedRoundRel` onwards every seam carries `liftShort` as the
commitment's shortness index — including `relWEvalClaim`, `relPartialEval` and `relHatEval`.
It has to: shortness is a property of the witness, so no guard can re-supply it downstream the way
the bound-sanity conjunct is re-supplied, and the §4.5 handoff needs a norm to push through `ψ`
into the next iteration's `Short`.

*Flagged as open gaps (not merely unproven)*: `mem_relPartialEval_of_relHatEval` (row 11), and
the `Short` obligation on `handoff_coordinateWiseSpecialSoundWith` (row 12), which is **false as
`openingChain` is currently parameterized** — see that theorem's docstring for the two missing
ingredients.

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

section Composition

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α : ℕ}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι} {ω : ℕ}
variable {σ : Type}

/-- The polynomial bridge followed by `QuadEval`, along a single relation seam. The bridge is
escape-free and `QuadEval` escape-aware, so the universal `▷` lifts the bridge at the never-firing
event and the composed event fires exactly when `QuadEval`'s own event fires on the suffix tree. -/
noncomputable def evalChain (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows) :
    EscapeCWSSPackage init impl
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
          innerDigits dRows ×
        CarrierCom 𝓜(q, α) dRows ×
          (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
      (QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r)
        innerDigits zDigits)
      ((!p[] : ProtocolSpec 0) ++ₚ
        pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r) :=
  bridgePackage (oSpec := oSpec) 𝓜(q, α) init impl pp (b : ZMod q)
      (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) ▷
    quadEvalPackage init impl hq5 hκ hτ pp

/-- **Hachi evaluation reduction — escape-threaded coordinate-wise special soundness (Hachi
[NOZ26, §4.2, Figure 3], `Rq`-level), `sorry`-free, at the chain's named extractor.** The endpoint
relations are `relPolyEval` and `relOut`, and the extractor is the composed algorithm
`(evalChain …).extractor` (the bridge's pull-back run on the prefix tree of `QuadEval`'s Lemma 8
extractor). The reduction's Module-SIS(B/D) failure mode is the certificate's escape disjunct
`(evalChain …).esc`, which by `ChallengeTree.EscapeEvent.append` reduces to `QuadEval`'s own event
on the suffix tree at the bridge's verdict.

Pinned to `𝓜(q, α)` with the [LS18] hypotheses of
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
      ((evalChain (b := b) (γ := γ) init impl hq5 hκ hτ pp).esc)
      (relPolyEval 𝓜(q, α) pp (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω))
      (relOut (zDigits := zDigits) 𝓜(q, α) pp (b : ZMod q) ω γ)
      ((bridgeVerifier (oSpec := oSpec) (innerRows := innerRows) (messageDigits := messageDigits)
          (outerRows := outerRows) (innerDigits := innerDigits) (dRows := dRows) (m := m) (r := r)
          𝓜(q, α)).append
        (verifier (oSpec := oSpec) (ω := ω) 𝓜(q, α)))
      ((evalChain (b := b) (γ := γ) init impl hq5 hκ hτ pp).extractor) :=
  (evalChain (b := b) (γ := γ) init impl hq5 hκ hτ pp).isCWSS

end Composition

section OpeningChain

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α : ℕ}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable {E : Type} {F : Type} [Field F] [DecidableEq F] [SampleableType F]

/-- Shorthand for the §4.3 chain's `R^lin` column count at the Eq. (20) instantiation. -/
local notation "μ₀" => rlinCols innerRows messageDigits innerDigits zDigits m r
/-- Shorthand for the §4.3 chain's `R^lin` row count at the Eq. (20) instantiation. -/
local notation "n₀" => rlinRows innerRows outerRows dRows

/-- The wire format of the pure prefix `openCore` (rows 1–7): bridge (0) ⧺ `QuadEval` (2) ⧺
R^lin adapter (0) ⧺ lift (2) ⧺ batching (0) ⧺ zero-check (1) ⧺ sumcheck bridge (0),
right-associated as `▷` composes them. -/
abbrev openCoreSpec (ω m₀ m₁ : ℕ) (TCom F : Type) :=
  (((!p[] : ProtocolSpec 0) ++ₚ
      pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r)) ++ₚ
    ((!p[] : ProtocolSpec 0) ++ₚ
      (CoordinateWise.ScalarRound.pSpecScalar TCom F ++ₚ
        ((!p[] : ProtocolSpec 0) ++ₚ
          (pSpecNestedZeroCheck F m₀ m₁ ++ₚ (!p[] : ProtocolSpec 0)))))

/-- Sampleability of the pure prefix's challenges, assembled **by name** from the per-link
instances (the generic append instance does not fire through the reducible `++ₚ` — its
discrimination keys degenerate — so compound wire formats get their instances built explicitly;
same workaround as `roundsSpecSampleable`). Requires a sampler for the fold challenges
(`ShortChallenge`), which the repo does not yet provide as an instance. -/
@[reducible] def openCoreSpecSampleable (ω m₀ m₁ : ℕ) (TCom F : Type) [SampleableType F]
    [SampleableType (ShortChallenge 𝓜(q, α) ω)] :
    ∀ i, SampleableType
      ((openCoreSpec (q := q) (α := α) (dRows := dRows) (r := r)
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

/-- **The pure prefix of one Hachi opening iteration** (rows 1–7 of the chain table): the
escape-aware evaluation front (`evalChain` = bridge ▷ `QuadEval`) extended by the §4.3 stages
with pure verifiers — the `R^lin` adapter, the HMZ25 lift, the batching bridge, the
(corrected-Lemma-10) zero-check, and the sumcheck bridge. Every relation seam is definitional
(`rfl`). The public result reduces `relPolyEval` to the round-`0` `nestedRoundRel`; the composite's
escape event is the `EscapeEvent.append`-nesting of the honest factor events (`QuadEval`'s
Module-SIS break in row 2, the lift's weak-binding collision in row 4, the zero-check's in row 6),
each on its own subtree. Sorry-free and axiom-clean. -/
noncomputable def openCore (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ ρBound m₀ m₁ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) (liftShort 𝓜(q, α) γ ρBound))
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (hq2 : 2 * b ≤ q + 1) (hb : b - 1 ≤ γ)
    (hρ : b - 1 ≤ ρBound) (hcov : (μ₀ + n₀) * (𝓜(q, α)).φ.natDegree ≤ 2 ^ m₀)
    (hn : n₀ ≤ 2 ^ m₁) :
    EscapeCWSSPackage init impl
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (NestedRoundStatement 𝓜(q, α) K.TCom F n₀ μ₀ m₀ m₁ 0)
      (LiftedWitness 𝓜(q, α) μ₀ n₀)
      (openCoreSpec (q := q) (α := α) (dRows := dRows) (r := r) ω m₀ m₁ K.TCom F) :=
  haveI : ∀ i, SampleableType
      ((((!p[] : ProtocolSpec 0) ++ₚ
        pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r)).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
      (h₂ := CoordinateWise.SingleRound.instSampleableTypeChallengePSpec)
  evalChain (b := b) (γ := γ) init impl hq5 hκ hτ pp ▷
    rlinPackage (zDigits := zDigits) 𝓜(q, α) init impl pp (b : ZMod q) ω γ ▷
    liftPackage 𝓜(q, α) γ ρBound K φF init impl hd ▷
    batchPackage 𝓜(q, α) m₀ m₁ γ ρBound init impl K φF b hn hd hcov hb hρ ▷
    nestedZeroCheckPackage 𝓜(q, α) m₀ m₁ γ ρBound init impl K φF b ▷
    nestedSumcheckBridgePackage 𝓜(q, α) m₀ m₁ γ ρBound init impl K φF b hd hcov

/-- **One full Hachi opening iteration** (rows 1–12 of the chain table): the pure prefix
`openCore` composed with the guarded tail: the `m₀` paired sumcheck rounds (Lemma 11, guarded on
the round checks), the final-evaluation step (guarded on the target checks), and the §4.5
recursion adapters (the pure partial-evaluation head, the ⚠ `Z`-packing bridge with the open
row-11 soundness question, and the guarded trace handoff). Pure factors (`openCore`,
`partialEvalPackage`, `zBatchPackage`) stay pure escape packages and are lifted into the
escape-guarded world by the mixed appends behind the universal `▷` (the two head seams, whose
relation identifications are the named `roundsChain_relIn`/`roundsChain_relOut` lemmas rather than
`rfl`, use `EscapeCWSSPackage.appendEscapeGuarded` / `EscapeGCWSSPackage.appendGuarded`
explicitly). The chain lands on the plain `relIn Φ'` relation — closing the recursion loop:
iteration `i+1` is this chain re-instantiated at `Φ'` (entering at `quadEvalPackage`, without
row 1).

The certificate `openingChain.isCWSS` is the one-iteration CWSS statement; its provenance (which
links are finished, skeleton-sorried, or gap-flagged) is inventoried in the module header — rows
1–9 are sorry-free, so every `sorryAx` this definition carries comes from rows 10–12. The
sumcheck arity is pinned to `m₀ := mLow + κ` so the recursion adapters can peel the top `κ`
variables. -/
noncomputable def openingChain (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ ρBound m₁ mLow κ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) (liftShort 𝓜(q, α) γ ρBound))
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (hq2 : 2 * b ≤ q + 1) (hb : b - 1 ≤ γ) (hbpos : 0 < b)
    (hρ : b - 1 ≤ ρBound) (hcov : (μ₀ + n₀) * (𝓜(q, α)).φ.natDegree ≤ 2 ^ (mLow + κ))
    (hn : n₀ ≤ 2 ^ m₁)
    (zpow : Fin (2 ^ κ) → F)
    (Φ' : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ']
    {innerRows' messageDigits' outerRows' innerDigits' dRows' m' r' : ℕ}
    (pp' : Hachi.PublicParamsD Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r')
      innerDigits' dRows')
    (reinterpretCom : K.TCom → Commitment Φ' outerRows')
    (base' : ZMod q) (βSq' γ' κ' : ℕ) :
    EscapeGCWSSPackage init impl
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (QuadEvalStatement Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r') innerDigits'
        dRows')
      (QuadEvalWitness Φ' innerRows' (2 ^ m') messageDigits' (2 ^ r') innerDigits')
      ((openCoreSpec (q := q) (α := α) (dRows := dRows) (r := r) ω (mLow + κ) m₁ K.TCom F ++ₚ
          roundsSpec F b (mLow + κ) ++ₚ pSpecFinalEval F) ++ₚ
        (pSpecPartialEval F κ ++ₚ ((!p[] : ProtocolSpec 0) ++ₚ pSpecHandoff Φ'))) :=
  haveI i₀ := openCoreSpecSampleable (q := q) (α := α) (dRows := dRows) (r := r)
    ω (mLow + κ) m₁ K.TCom F
  haveI i₁ : ∀ i, SampleableType
      (((openCoreSpec (q := q) (α := α) (dRows := dRows) (r := r)
        ω (mLow + κ) m₁ K.TCom F) ++ₚ
        roundsSpec F b (mLow + κ)).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend (h₁ := i₀)
      (h₂ := roundsSpecSampleable F b (mLow + κ))
  haveI i₂ : ∀ i, SampleableType
      ((((openCoreSpec (q := q) (α := α) (dRows := dRows) (r := r)
          ω (mLow + κ) m₁ K.TCom F) ++ₚ
          roundsSpec F b (mLow + κ)) ++ₚ pSpecFinalEval F).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend (h₁ := i₁)
      (h₂ := instSampleableTypeChallengePSpecFinalEval)
  (((openCore (m₀ := mLow + κ) (m₁ := m₁) init impl hq5 hκ hτ K pp φF hd hq2 hb hρ hcov
      hn).appendEscapeGuarded
      (roundsChain 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF hbpos (mLow + κ) le_rfl)
      (roundsChain_relIn 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF hbpos
        (mLow + κ) le_rfl).symm).appendGuarded
    (finalEvalPackage 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF)
    (roundsChain_relOut 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF hbpos
      (mLow + κ) le_rfl)) ▷
  partialEvalPackage 𝓜(q, α) mLow κ γ ρBound b init impl K φF ▷
  zBatchPackage 𝓜(q, α) mLow κ γ ρBound init impl zpow K φF ▷
  handoffPackage 𝓜(q, α) Φ' mLow κ γ ρBound init impl zpow K φF pp' reinterpretCom base' βSq'
    γ' κ'

/-- **Hachi one-iteration opening — escape-threaded coordinate-wise special soundness (skeleton
certificate), at the chain's named extractor.** The composed verifier of rows 1–12 is CWSS over the
endpoint relations `relPolyEval` (over the current ring `𝓜(q, α)`) and `relIn` (over `Φ'`), at the
composed extraction algorithm `(openingChain …).extractor`, with the composed escape event
`(openingChain …).esc` as the certificate's disjunct — the `EscapeEvent.append`-nesting of the
honest per-row events (rows 2, 4, 6, 8), each on its own subtree. The proof term is just
`openingChain.isCWSS`; its assumptions are exactly the sorried links inventoried in the module
header — rows 10–12 and nothing else, the ⚠ row-11 gap among them. -/
theorem hachi_iteration_coordinateWiseSpecialSoundWithEscape (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ ρBound m₁ mLow κ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) (liftShort 𝓜(q, α) γ ρBound))
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (hq2 : 2 * b ≤ q + 1) (hb : b - 1 ≤ γ) (hbpos : 0 < b)
    (hρ : b - 1 ≤ ρBound) (hcov : (μ₀ + n₀) * (𝓜(q, α)).φ.natDegree ≤ 2 ^ (mLow + κ))
    (hn : n₀ ≤ 2 ^ m₁)
    (zpow : Fin (2 ^ κ) → F)
    (Φ' : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ']
    {innerRows' messageDigits' outerRows' innerDigits' dRows' m' r' : ℕ}
    (pp' : Hachi.PublicParamsD Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r')
      innerDigits' dRows')
    (reinterpretCom : K.TCom → Commitment Φ' outerRows')
    (base' : ZMod q) (βSq' γ' κ' : ℕ) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl
      (openingChain (zDigits := zDigits) (ω := ω) (mLow := mLow) (m₁ := m₁) init impl hq5 hκ hτ
        K pp φF hd hq2 hb hbpos hρ hcov hn zpow Φ' pp' reinterpretCom base' βSq' γ' κ').struct
      (openingChain (b := b) (zDigits := zDigits) (ω := ω) (mLow := mLow) (m₁ := m₁) init impl
        hq5 hκ hτ K pp φF hd hq2 hb hbpos hρ hcov hn zpow Φ' pp' reinterpretCom base' βSq' γ'
        κ').esc
      (relPolyEval 𝓜(q, α) pp (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω))
      (relIn Φ' pp' base' βSq' γ' κ')
      (openingChain (zDigits := zDigits) (ω := ω) (mLow := mLow) (m₁ := m₁) init impl hq5 hκ
        hτ K pp φF hd hq2 hb hbpos hρ hcov hn zpow Φ' pp' reinterpretCom base' βSq' γ' κ').verifier
      (openingChain (b := b) (zDigits := zDigits) (ω := ω) (mLow := mLow) (m₁ := m₁) init impl
        hq5 hκ hτ K pp φF hd hq2 hb hbpos hρ hcov hn zpow Φ' pp' reinterpretCom base' βSq' γ'
        κ').extractor :=
  (openingChain (zDigits := zDigits) (ω := ω) (mLow := mLow) (m₁ := m₁) init impl hq5 hκ hτ
    K pp φF hd hq2 hb hbpos hρ hcov hn zpow Φ' pp' reinterpretCom base' βSq' γ' κ').isCWSS

end OpeningChain

/-! ## TODO — growing the composition

* **§3 packing head (external extension-field claims).** The paper's headline
  multilinear-over-`F_{q^k}` interface (§3.1/§3.2) wraps an extension-field evaluation claim in
  front of `relPolyEval`; it is planned as an instance of the generalized `RingSwitching`
  packing phase, not as a Hachi-local head.
* **Recursion termination.** At the row-12 seam: the §4.4 asymptotic base case (reveal the final
  small polynomial — a `SendWitness`-style tail) and the §4.5 concrete cutoff (switch to
  Greyhound/LaBRADOR, i.e. the JL projection route) are future zero-round/one-message tails.
* **Discharging the skeleton.** What is left is the recursion tail, in this order: a **repair
  decision for the row-11 gap** first (any repair changes the protocol content of rows 10–12, so
  polishing those proofs before deciding is wasted work), then the partial-evaluation head
  (row 10), then the trace handoff (row 12) — which additionally needs the two norm ingredients its
  docstring names, since its `Short` obligation is false as `openingChain` is parameterized today.
* **`LiftCom` instantiation.** The chain is stated at an abstract weak-binding commitment, so the
  escape events of rows 4/6/8 point at `LiftCom.Collision` without yet being tied to the
  inner-outer commitment: instantiating it (no re-decomposition, the collision escape via
  `outputToModuleSIS_valid_of_verified`, and the ring-dimension reinterpretation row 12 consumes)
  is what makes those escapes concrete Module-SIS breaks.
* **Honest-prover / completeness layer.** Each link's prover is a skeleton parameterized by its
  compute functions, and all of them through the sumcheck are now instantiated with a completeness
  proof (`QuadEval`'s `honestComputeV`/`honestComputeResp`, the sumcheck's `honestComputeG` at the
  computable `computableRoundPoly`, the final evaluation's `honestComputeY`); the honest chain is
  appended in `HonestChain.lean` up to `relWEvalClaim`. What is still open is the recursion tail's
  `computeY` (`Recursion/PartialEval.lean`) and — for every *composed* completeness statement,
  including `Commitment.lean`'s `opening` — the sorried generic `Reduction.append_completeness`,
  which those statements inherit as a `sorryAx` dependency.
* **Knowledge-error accounting** (FMN24 Lemma 4), `Commitment.extractability`, and Fiat–Shamir
  remain out of scope. Note what this means for the certificate above: CWSS delivers a witness (or
  an escape) from a *structured accepting tree*, with no probability attached — no per-round
  Schwartz–Zippel error, and no accounting of the tree size the composed structure demands. -/

end ArkLib.Lattices.Ajtai.InnerOuter
