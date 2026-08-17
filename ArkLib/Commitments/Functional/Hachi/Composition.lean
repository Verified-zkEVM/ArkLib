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
# Hachi — the CWSS composition home

This is the designated home of the composition of the subprotocols of Hachi [NOZ26],
a lattice-based multilinear polynomial commitment scheme. Each subprotocol is formalized in its own
file and exported as a CWSS *package*, bundling the verifier
with its proof of coordinate-wise special soundness (CWSS), a soundness notion under
which a witness is extracted from a suitably structured tree of accepting transcripts. This file
**imports those packages and chains them** with the universal append `▷`, which dispatches on
the factors' package kinds and lifts each to the join automatically (both lifts are lossless). Only
the ordinary relation seam has to match — escape events compose without a seam. The composed
chain's `isCWSS` field is the CWSS certificate for the whole reduction. Every link is now imported,
the end-piece included (`EndPiece/Reduction.lean`); this file hosts no protocol of its own.
(Hachi as a `Commitment.Scheme` — the honest committer `keygen`/`commit` and the `hachi` functional
commitment — lives in the sibling `Commitment.lean`.)

## Iteration, end-piece, evaluation

The Hachi evaluation (opening) protocol decomposes into three pieces:

1. **Iteration** (`iteration`): the concatenation of the subprotocols — rows 1–9 of the chain
   table below. One iteration reduces the polynomial-evaluation claim `relPolyEval` to the bare
   multilinear-evaluation claim `relWEvalClaim` (`mle[w̃](a) = y′`) on the committed table.
2. **End-piece** (`endPiece`, `EndPiece/`): the closing component that ends a (possible
   run of) iteration(s): the prover sends the reduced (end) witness itself to the verifier, who
   checks the reduced claim against it directly. Verifier, guard and extractor are complete; only
   its CWSS certificate `endPiece_coordinateWiseSpecialSoundWith` is still sorried.
3. **Evaluation** (`evaluation`): a single iteration concatenated with the end-piece — the
   complete evaluation protocol of the Hachi commitment scheme.

## The composed verifier chain, seam by seam

Top-to-bottom is one iteration of the ArkLib Hachi evaluation, whose committed data is an
`Rq`-valued multilinear polynomial. The iteration starts with the Figure 3 path, not with §3: the
§3 packing head (extension-field claims into `Rq`-claims, via the generalized `RingSwitching`
packing phase) is a separate track that wraps *external* extension-field claims in front of
`relPolyEval`.

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
```

**Which rows carry an escape event.** Row 2 carries `QuadEval`'s Module-SIS(B/D) break of the fixed
key (`quadEvalEscLocal`); rows 4, 6 and 8 carry the weak-binding collision of the `w̃`-commitment
(`LiftCom.Collision`, via `Lift.escEvent` / `nestedZeroCheckEsc` / `roundEsc`). Those four are
`EscapeCWSSPackage`/`EscapeGCWSSPackage`s; every other row is escape-free
(`CWSSPackage`/`GCWSSPackage`) and enters the chain at the never-firing event through the universal
`▷`'s lossless lift.

- Rows 1–7 have **pure** verifiers: every check constrains either retained statement data or the
  never-sent witness, so it lives in the output relation (the `QuadEval` precedent). Rows 8 and 9
  are **guarded**: their runtime check reads data the next statement type drops
  (the previous sumcheck target; the final targets) — exactly the paper's runtime checks — and
  they compose through the proven guarded append theorem.
- Row 6 implements the **corrected Lemma 10**: the paper's uniform-vector star extraction is not
  provable (axis-cross counterexample). Each coordinate of `τ₀` and `τα` is instead sampled in a
  separate scalar round, so the accepting transcript tree becomes a path-dependent complete
  binary evaluation tree — `k = 2` at every round, and the multilinear identity test extraction
  needs. Since no prover message separates the rounds, the *interactive* protocol is unchanged
  from Figure 5; what changes is the tree shape the extractor is handed. The counterexample, the
  repair and their costs are spelled out in `ZeroCheck/Reduction.lean`; the full analysis is
  `docs/kb/audits/noz26-zero-check-lemma10.md`.

## Sorry inventory of the composed chain (provenance of the certificate)

*Generic machinery — proven.* `Verifier.IsGuarded.append` and
`Verifier.append_coordinateWiseSpecialSoundWithEscape_of_guardedLeft` (`Guarded.lean`; the latter is
the escape-threaded fundamental theorem, stated at explicit guard data — the plain guarded append
is its corollary at the never-firing events) are proven, as are the two scalar-round assemblies
`coordinateWiseSpecialSoundWith(Escape)_of_mkWitness_scalar` (`ScalarRound.lean`) with their
readers, shape recovery, extractor and escape event. The escape
layer (`TranscriptTree/Basic.lean`, `CWSS/{Basic,Composition}.lean`, `Escape.lean`) with its append
theorem, the single-round escape assembly and `quadEval_coordinateWiseSpecialSoundWithEscape` are
proven (`sorryAx`-free). Each sorried row carries its extraction *algorithm* as an explicitly
sorried `Extractor.TreeBased`.

**Rows 1–7 carry no sorried certificate — and rows 1–6 are additionally `sorryAx`-free.** The
`R^lin` adapter (`rlinStmt`/`unstack`/`mem_relOut_of_relRlin`) and the HMZ25 lift (Lemma 9,
`liftPackage.isCWSS`, via the generic `Lift` layer on the proven scalar-round engine and the
`QuotientLift` algebra) are sorry-free and axiom-clean (rows 3–4). So are, on this branch:

* row 5, the batching pull-back `mem_relLift_of_relBatched` — including the range-side soundness
  `H₀ ≡ 0 ⇒ liftShort` (`hZero_eq_zero_imp_liftShort`), so shortness is **derived**, not assumed,
  and `relBatched` stays norm-free;
* row 6, the **corrected Lemma 10**: `nestedZeroCheck_coordinateWiseSpecialSoundWithEscape` with
  its named extractor and the weak-binding event `nestedZeroCheckEsc`, on the concrete
  `CMlPolynomialEval` encodings `hZero`/`hAlpha` and the evaluation-tree zero test.

Row 7, the sum-to-point bridge `mem_relNestedZeroCheck_of_nestedRoundRel`, is proved outright in
`Sumcheck/Bridge.lean`, but it routes through the two still-sorried sumcheck identities below, so
it inherits their `sorryAx` and is *not* axiom-clean.

*Per-link math still sorried*: the two sumcheck identities in `Constraints.lean`
(`sum_sumcheckPolyZero`, `sum_sumcheckPolyAlpha` — rows 7–9 depend on them transitively),
Lemma 11 (`round_coordinateWiseSpecialSoundWithEscape` + `roundExtractor`), and the final
evaluation (`finalEval_coordinateWiseSpecialSoundWith` + `finalEvalExtractor` + the `finalCheck`
encoding). The **end-piece** (`EndPiece/Reduction.lean`) is no longer a skeleton: its check
(`endPieceCheck`), verifier, guardedness (`endPieceVerifier_isGuarded`, by `rfl`) and extraction
algorithm (`endPieceWitness`/`endPieceExtractor`) are complete definitions, leaving only the
certificate `endPiece_coordinateWiseSpecialSoundWith` sorried. Every sorried encoding def carries
an in-situ `**Sorried**` docstring.

## References

* [Fenzi, G., Moghaddas, H., and Nguyen, N. K., *Lattice-Based Polynomial Commitments:
    Improved and Extended*][FMN24]
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
instances (the generic append instance does not fire through the reducible `++ₚ` — its
discrimination keys degenerate — so compound wire formats get their instances built explicitly;
same workaround as `roundsSpecSampleable`). Requires a sampler for the fold challenges
(`ShortChallenge`), which the repo does not yet provide as an instance. -/
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

/-- **One Hachi evaluation iteration** (rows 1–9 of the chain table): the concatenation of the
subprotocols, in one line of `▷`s — bridge ▷ `QuadEval` ▷ `R^lin` adapter ▷ HMZ25 lift ▷
batching bridge ▷ (corrected-Lemma-10) zero-check ▷ sumcheck bridge (rows 1–7, pure verifiers,
every relation seam definitional) — closed by the guarded sumcheck tail: the `m₀` paired
sumcheck rounds (Lemma 11, guarded on the round checks) and the final-evaluation step (guarded
on the target checks). Every relation seam is definitional — `roundsChain` re-pins the loop's
relations to the round-`0`/round-`m₀` seam relations — so the whole chain composes by the
universal `▷`, with pure factors lifted into the escape-guarded world automatically. One
iteration reduces the
polynomial-evaluation claim `relPolyEval` to the evaluation claim `relWEvalClaim` —
`mle[w̃](a) = y′` for the committed table `w̃` — the reduced claim the end-piece consumes. The
composite's escape event is the `EscapeEvent.append`-nesting of the honest factor events
(rows 2, 4, 6, 8), each on its own subtree.

The certificate `iteration.isCWSS` is the one-iteration CWSS statement; its provenance (which
links are finished and which are skeleton-sorried) is inventoried in the module header. -/
noncomputable def iteration (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ ρBound m₀ m₁ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) (liftShort 𝓜(q, α) γ ρBound))
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (_hq2 : 2 * b ≤ q + 1) (hb : b - 1 ≤ γ)
    (hρ : b - 1 ≤ ρBound) (hcov : (μ₀ + n₀) * (𝓜(q, α)).φ.natDegree ≤ 2 ^ m₀)
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
  let bridge := bridgePackage (oSpec := oSpec) 𝓜(q, α) init impl pp (b : ZMod q)
    (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω)
  let quadEval := quadEvalPackage init impl hq5 hκ hτ pp
  let rlin := rlinPackage (zDigits := zDigits) 𝓜(q, α) init impl pp (b : ZMod q) ω γ
  let lift := liftPackage 𝓜(q, α) γ ρBound K φF init impl hd
  let batch := batchPackage 𝓜(q, α) m₀ m₁ γ ρBound init impl K φF b hn hd hcov hb hρ
  let zeroCheck := nestedZeroCheckPackage 𝓜(q, α) m₀ m₁ γ ρBound init impl K φF b
  let sumcheckBridge := nestedSumcheckBridgePackage 𝓜(q, α) m₀ m₁ γ ρBound init impl K φF b
  let rounds := roundsChain 𝓜(q, α) m₀ m₁ γ ρBound b init impl K φF m₀
  let finalEval := finalEvalPackage 𝓜(q, α) m₀ m₁ γ ρBound b init impl K φF
  let core : EscapeCWSSPackage init impl
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (NestedRoundStatement 𝓜(q, α) K.TCom F n₀ μ₀ m₀ m₁ 0)
      (LiftedWitness 𝓜(q, α) μ₀ n₀)
      (coreSpec (q := q) (α := α) (dRows := dRows) (r := r) ω m₀ m₁ K.TCom F) :=
    (bridge ▷ quadEval) ▷ rlin ▷ lift ▷ batch ▷ zeroCheck ▷ sumcheckBridge
  (core ▷ rounds) ▷ finalEval

/- There is the possibility of adding recursion at the `relWEvalClaim` seam (the [NOZ26] §4.5
adapters), so that multiple iterations can be concatenated together — followed by a single
end-piece — to reduce the final witness/proof even further. -/

/-- **Hachi one-iteration evaluation reduction — escape-threaded coordinate-wise special soundness
(skeleton certificate), at the chain's named extractor.** The composed verifier of rows 1–9 is CWSS
over the endpoint relations `relPolyEval` and the evaluation claim `relWEvalClaim`, at the composed
extraction algorithm `(iteration …).extractor`, with the composed escape event `(iteration …).esc`
as the certificate's disjunct — the `EscapeEvent.append`-nesting of the honest per-row events
(rows 2, 4, 6, 8), each on its own subtree. The proof term is just `iteration.isCWSS`; its
assumptions are exactly the sorried links inventoried in the module header (Lemma 11, the final
evaluation, and the two `Constraints.lean` sum identities). -/
theorem hachi_iteration_coordinateWiseSpecialSoundWithEscape (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ ρBound m₀ m₁ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) (liftShort 𝓜(q, α) γ ρBound))
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (hq2 : 2 * b ≤ q + 1) (hb : b - 1 ≤ γ)
    (hρ : b - 1 ≤ ρBound) (hcov : (μ₀ + n₀) * (𝓜(q, α)).φ.natDegree ≤ 2 ^ m₀)
    (hn : n₀ ≤ 2 ^ m₁) :
    Verifier.coordinateWiseSpecialSoundWithEscape init impl
      (iteration (zDigits := zDigits) (ω := ω) (m₀ := m₀) (m₁ := m₁) init impl hq5 hκ hτ
        K pp φF hd hq2 hb hρ hcov hn).struct
      (iteration (b := b) (zDigits := zDigits) (ω := ω) (m₀ := m₀) (m₁ := m₁) init impl
        hq5 hκ hτ K pp φF hd hq2 hb hρ hcov hn).esc
      (relPolyEval 𝓜(q, α) pp (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω))
      (relWEvalClaim 𝓜(q, α) m₀ γ ρBound b K φF)
      (iteration (zDigits := zDigits) (ω := ω) (m₀ := m₀) (m₁ := m₁) init impl hq5 hκ
        hτ K pp φF hd hq2 hb hρ hcov hn).verifier
      (iteration (b := b) (zDigits := zDigits) (ω := ω) (m₀ := m₀) (m₁ := m₁) init impl
        hq5 hκ hτ K pp φF hd hq2 hb hρ hcov hn).extractor :=
  (iteration (zDigits := zDigits) (ω := ω) (m₀ := m₀) (m₁ := m₁) init impl hq5 hκ hτ
    K pp φF hd hq2 hb hρ hcov hn).isCWSS

/- The end-piece is no longer a skeleton: it lives in `EndPiece/` as a subprotocol in its own
right, exporting its `GCWSSPackage` the same way as the other subprotocols (`QuadEval/`,
`RingSwitch/`, `ZeroCheck/`, `Sumcheck/`). Only its use in `evaluation` remains here. -/

/-- **The complete Hachi evaluation** (the opening argument of the commitment scheme): a single
`iteration` concatenated with the `endPiece`. The composed reduction takes the
polynomial-evaluation claim `relPolyEval` all the way to the trivial claim: after the end-piece
the verifier has checked the reduced witness against the reduced claim itself, so nothing is left
to reduce. The certificate is `(evaluation …).isCWSS`; it is skeletal exactly where its factors
are (the sorried links of the iteration; the end-piece contributes only its own
`endPiece_coordinateWiseSpecialSoundWith`). -/
noncomputable def evaluation (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ ρBound m₀ m₁ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) (liftShort 𝓜(q, α) γ ρBound))
    [BEq K.TCom] [LawfulBEq K.TCom]
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (hq2 : 2 * b ≤ q + 1) (hb : b - 1 ≤ γ)
    (hρ : b - 1 ≤ ρBound) (hcov : (μ₀ + n₀) * (𝓜(q, α)).φ.natDegree ≤ 2 ^ m₀)
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
    hq5 hκ hτ K pp φF hd hq2 hb hρ hcov hn
  let closing := endPiece 𝓜(q, α) m₀ γ ρBound b init impl K φF
  iter ▷ closing

end Evaluation

/-! ## TODO — growing the composition

* **Discharging the skeleton.** Work through the sorry inventory in the module header in
  dependency order: the two sum identities of the shared encoding layer
  (`ZeroCheck/Constraints.lean`), then Lemma 11's round certificate (`Sumcheck/Rounds.lean`) and
  the final evaluation (`Sumcheck/FinalEval.lean`), and the end-piece certificate
  `endPiece_coordinateWiseSpecialSoundWith` (`EndPiece/Reduction.lean`) — plus the
  `LiftCom` instantiation (the inner-outer commitment without re-decomposition, with its collision
  escape via `outputToModuleSIS_valid_of_verified`).
* **Computability.** `iteration` and `evaluation` are `noncomputable`; making them computable is
  tracked with @ErVinuelas.
* **§3 packing head (external extension-field claims).** The paper's headline
  multilinear-over-`F_{q^k}` interface (§3.1/§3.2) wraps an extension-field evaluation claim in
  front of `relPolyEval`; it is planned as an instance of the generalized `RingSwitching`
  packing phase, not as a Hachi-local head.
* **Recursion at the `relWEvalClaim` seam.** The §4.5 `Recursion/` adapters (`PartialEval`,
  `ZBatchBridge`, `TraceHandoff`) would carry one iteration's evaluation claim to the next ring,
  so that several iterations could precede a single `endPiece`. They are formalized but not
  composed here, and `ZBatchBridge` carries a documented soundness gap needing a repair decision.
  Termination is §4.4's asymptotic base case and §4.5's concrete Greyhound/LaBRADOR cutoff.
* **Knowledge-error accounting** ([FMN24] Lemma 4), `Commitment.extractability`, and Fiat–Shamir
  remain out of scope. -/

end ArkLib.Lattices.Ajtai.InnerOuter
