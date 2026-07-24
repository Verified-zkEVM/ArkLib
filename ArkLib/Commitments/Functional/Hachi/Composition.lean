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
file and exported as an `EscapeCWSSPackage` (pure verifier) or `EscapeGCWSSPackage` (guarded
verifier — may `failure` at runtime), bundling the verifier with its proof of coordinate-wise
special soundness
(CWSS), the knowledge-soundness notion under which a witness is extracted from a suitably
structured tree of accepting transcripts. This file only **imports those packages and chains
them** with the universal append `▷`, which dispatches on the factors' package kinds (pure,
guarded, escape-aware, or both) and lifts to the join automatically. Both the ordinary relation
seam and the parallel escape seam must match. The guarded composition theorem lives in
`OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean`). The composed chain's
`isCWSS` field is the CWSS certificate for the whole reduction. (Hachi as a `Commitment.Scheme` —
the honest committer `keygen`/`commit` and the `hachi` functional commitment — lives in the
sibling `Commitment.lean`.)

## The three layers of this file

1. **`evalChain`** (sorry-free, finished): the polynomial-level bridge ▷ `QuadEval`
   (§4.2 / Figure 3 / Lemma 8).
2. **`openCore`** (skeleton, pure links): the escape-aware `evalChain` extended by the
   §4.3 stages up to the sumcheck bridge — R^lin adapter (F2) ▷ HMZ25 lift (Figure 4 / Lemma 9)
   ▷ batching bridge (Eqs. (22)–(23)) ▷ zero-check (Figure 5 / **corrected** Lemma 10) ▷
   sumcheck bridge.
3. **`openingChain`** (skeleton, guarded tail): the pure `openCore` ▷ the paired sumcheck loop
   (Figure 6 / Lemma 11, `m₀` guarded rounds) ▷ final evaluation (Figure 7 tail) ▷ the
   §4.5 recursion adapters (pure partial evaluations ▷ pure `Z`-packing bridge ▷ guarded trace
   handoff), landing on
   the **next iteration's** `QuadEval` input relation over the next ring `Φ'` — the recursion
   loop's closing seam. The universal `▷` lifts each pure factor into the escape-guarded world
   automatically (`Escape.lean`, package-lattice section); no explicit `.toGuarded` calls.

## The composed verifier chain, seam by seam

Top-to-bottom is one opening iteration of the ArkLib Hachi commitment, whose committed data is an
`Rq`-valued multilinear polynomial. The opening starts with the Figure 3 path, not with §3: the §3
packing head (extension-field claims into `Rq`-claims, via the generalized `RingSwitching` packing
phase — see `HACHI_RING_SWITCHING_PLAN.md`, Phases B–E) is a separate track that wraps *external*
extension-field claims in front of `relPolyEval`; the §4.5 adapters below close the recursion
*internally*. Every row exposes ordinary witness relations. In parallel, the escape budget grows
backwards at the two extraction points that can create failures: Figure 4 adds `K.esc`, and
`QuadEval` adds `Q.localEsc`. `Set.withEscape` appears only inside package certificates.

```text
 # | link (file)                | rounds: wire         | relIn → relOut            | CWSS, k
---+----------------------------+----------------------+---------------------------+---------------
 1 | bridge (QuadEval/Bridge)   | 0                    | relPolyEval → relIn       | any (0 chals)
 2 | QuadEval (QuadEval/*)      | msg v; c ∈ C^{2^r}   | relIn → relOut (Eq. 20)   | ℓ=2^r, k=2 (L8)
 3 | R^lin (RingSwitch/Rlin)    | 0                    | relOut → relRlin          | any
 4 | lift (…/Reduction)         | msg t; α ∈ F         | relRlin → relLift         | ℓ=1, k=2d (L9)
 5 | batch (ZeroCheck/Batch)    | 0                    | relLift → relBatched      | any
 6 | zero-check (…/Reduction)   | (ρ₀,ρ_α) ∈ F²        | relBatched → relZeroCheck | ℓ=2, k=D (L10*)
 7 | sc bridge (Sumcheck/Bridge)| 0                    | relZeroCheck → roundRel 0 | any
 8 | rounds ×m₀ (…/Rounds)      | (g-pair; aᵢ)ᵢ        | roundRel 0 → roundRel m₀ | ℓ=1, k=2b+1
   |  — GUARDED: gᵢ(0)+gᵢ(1)=z |                      |                           |  (L11)/round
 9 | final eval (…/FinalEval)   | msg y′ ∈ F           | roundRel m₀ → relWEvalClaim | any — GUARDED
10 | partials (Recursion/PartialEval)| msg (yᵢ)_{i≠0}  | relWEvalClaim → relPartialEval | any (pure)
11 | Z-pack (…/ZBatchBridge)    | 0                    | relPartialEval → relHatEval | any — ⚠ GAP
12 | handoff (…/TraceHandoff)   | msg p ∈ R′q          | relHatEval → relIn(Φ′) | any — GUARDED
   |                            |                      |  = next iteration's row 2 |
```

- Rows 1–7 have **pure** verifiers: every check constrains either retained statement data or the
  never-sent witness, so it lives in the output relation (the `QuadEval` precedent). Rows 8, 9,
  12 are **guarded** (design D6): their runtime check reads data the next statement type drops
  (the previous sumcheck target; the final targets; the packed claim value) — exactly the paper's
  runtime checks — and compose through the guarded append, whose composition theorem (B4) is the
  one sorried piece of *generic* machinery.
- Row 6 implements the **corrected Lemma 10**: the paper's uniform-vector star extraction is not
  provable (axis-cross counterexample); the challenge is a pair of scalar **Kronecker seeds**
  with the batching points derived on the curves `κ_m(ρ) = (ρ, ρ², ρ⁴, …)`, giving genuine
  `(ℓ, k) = (2, D)` CWSS at `D = max 2^{m₀} 2^{m₁}`. See `HACHI_LEMMA10_GAP.md`. This is the one
  place the formalization deliberately changes the paper's protocol.
- Row 11 isolates the **§4.5/§3.2 partial-evaluation gap** found while auditing this skeleton:
  the packed claim of Eq. (26) pins only one `F`-linear functional of the per-slice values, so
  the paper's step is (apparently) not knowledge-sound as stated; the bridge's pull-back sorry is
  expected to be unprovable until a repair (batching challenge / generic §3.1 packing) is
  adopted. See `HACHI_RECURSION_GAP.md`. All other sorries in the chain are honest skeleton work.
- Row 12 lands on plain `relIn Φ'`, with the ambient escape set carried separately. Iteration
  `i+1` re-enters at `quadEvalPackage Φ'` directly (its bases are `eq`-tensor
  packings, not monomial bases, so the polynomial-level bridge of row 1 is head-only).
  Asymptotic termination (§4.4: reveal the final polynomial once small) and the concrete §4.5
  Greyhound/LaBRADOR cutoff are future zero-round tails at that seam.

## Sorry inventory of the composed chain (provenance of the certificate)

*Generic machinery* (B4): `Verifier.IsGuarded.append`,
`Verifier.append_coordinateWiseSpecialSound_of_guardedLeft` (`Guarded.lean`);
`coordinateWiseSpecialSound_of_mkWitness_scalar` (`ScalarRound.lean`, consumed only by future
proofs). *Escape threading*: `EscapeCWSSPackage`, `EscapeGCWSSPackage`, and
`quadEval_coordinateWiseSpecialSound`.
*Per-link math*: the F2 index bookkeeping (`rlinStmt`/`unstack`/`mem_relOut_of_relRlin`),
Lemma 9 (`lift_coordinateWiseSpecialSound`), the F5 encodings (`Constraints.lean`), the
un-batching (`mem_relLift_of_relBatched`), corrected Lemma 10
(`zeroCheck_coordinateWiseSpecialSound`), the sum-to-point bridge, Lemma 11
(`round_coordinateWiseSpecialSound`), F8 (`finalEval_coordinateWiseSpecialSound` + the
`finalCheck` encoding), G2 (`partialEval_coordinateWiseSpecialSound` + its encoding defs), G3
(`handoff_coordinateWiseSpecialSound` + `traceCheck`/`toNextQuadEvalStatement`/`hatEval`).
Every sorried encoding def carries an in-situ `**Sorried**` docstring naming its milestone.
*Flagged as an open gap (not merely unproven)*: `mem_relPartialEval_of_relHatEval` (row 11).

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
variable {σ E : Type}

/-- The polynomial bridge followed by `QuadEval`, with one ordinary relation seam and a
parallel escape seam. `QuadEval` grows the backwards escape budget by `Q.localEsc`; the bridge
then transports that enlarged budget unchanged to the polynomial-level input. -/
def evalChain (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    (esc : Set E)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (Q : QuadEvalEscapeMap 𝓜(q, α) pp γ E) :
    EscapeCWSSPackage init impl E
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
      (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω)
      (esc ∪ Q.localEsc) ▷
    quadEvalPackage init impl hq5 hκ hτ esc pp Q

/-- **Hachi evaluation reduction — coordinate-wise special soundness (Hachi [NOZ26, §4.2,
Figure 3], `Rq`-level), `sorry`-free.** The public flow of `evalChain` is the ordinary
`relPolyEval → relIn → relOut` flow. Only this certificate widens its endpoints by the
parallel escape sets; `QuadEval` adds its mapped local Module-SIS(B/D) outcomes to the input
budget. The result is pinned to `𝓜(q, α)` with the [LS18] hypotheses of
`quadEval_coordinateWiseSpecialSound`. -/
theorem eval_coordinateWiseSpecialSound (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (hq5 : q % 8 = 5) {b ω γ : ℕ}
    (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits) (esc : Set E)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (Q : QuadEvalEscapeMap 𝓜(q, α) pp γ E) :
    ((bridgeVerifier (oSpec := oSpec) (innerRows := innerRows) (messageDigits := messageDigits)
          (outerRows := outerRows) (innerDigits := innerDigits) (dRows := dRows) (m := m) (r := r)
          𝓜(q, α)).append
        (verifier (oSpec := oSpec) (ω := ω) 𝓜(q, α))).coordinateWiseSpecialSound init impl
      (CWSSStructure.ofIsEmpty.append
        (foldStructure (CarrierCom := CarrierCom 𝓜(q, α) dRows)
          (C := ShortChallenge 𝓜(q, α) ω) (r := r)))
      ((relPolyEval 𝓜(q, α) pp (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ
          (2 * ω)).withEscape (esc ∪ Q.localEsc))
      ((relOut (zDigits := zDigits) 𝓜(q, α) pp (b : ZMod q) ω γ).withEscape esc) :=
  (evalChain init impl hq5 hκ hτ esc pp Q).isCWSS

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
abbrev openCoreSpec (ω : ℕ) (TCom F : Type) :=
  (((!p[] : ProtocolSpec 0) ++ₚ
      pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r)) ++ₚ
    ((!p[] : ProtocolSpec 0) ++ₚ
      (CoordinateWise.ScalarRound.pSpecScalar TCom F ++ₚ
        ((!p[] : ProtocolSpec 0) ++ₚ (pSpecZeroCheck F ++ₚ (!p[] : ProtocolSpec 0)))))

/-- Sampleability of the pure prefix's challenges, assembled **by name** from the per-link
instances (the generic append instance does not fire through the reducible `++ₚ` — its
discrimination keys degenerate — so compound wire formats get their instances built explicitly;
same workaround as `roundsSpecSampleable`). Requires a sampler for the fold challenges
(`ShortChallenge`), which the repo does not yet provide as an instance. -/
@[reducible] def openCoreSpecSampleable (ω : ℕ) (TCom F : Type) [SampleableType F]
    [SampleableType (ShortChallenge 𝓜(q, α) ω)] :
    ∀ i, SampleableType
      ((openCoreSpec (q := q) (α := α) (dRows := dRows) (r := r) ω TCom F).Challenge i) :=
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
            (h₁ := instSampleableTypeChallengePSpecZeroCheck)
            (h₂ := ProtocolSpec.instSampleableTypeChallengeEmpty)))))

/-- **The pure prefix of one Hachi opening iteration** (rows 1–7 of the chain table): the
escape-aware evaluation front (`evalChain` = bridge ▷ `QuadEval`) extended by the §4.3 stages
with pure verifiers — the `R^lin` adapter, the HMZ25
lift, the batching bridge, the (corrected-Lemma-10) zero-check, and the sumcheck bridge. Every
ordinary relation seam and parallel escape seam is definitional (`rfl`). The public result
reduces `relPolyEval` to the round-`0` `roundRel`; backwards extraction grows `esc` first by
`K.esc` and then by `Q.localEsc`. -/
noncomputable def openCore (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ ρBound m₀ m₁ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) E (liftShort 𝓜(q, α) γ ρBound))
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (Q : QuadEvalEscapeMap 𝓜(q, α) pp γ E)
    (esc : Set E)
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (hq2 : 2 * b ≤ q + 1) (hb : b - 1 ≤ γ) :
    EscapeCWSSPackage init impl E
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (RoundStatement 𝓜(q, α) K.TCom F n₀ μ₀ 0)
      (LiftedWitness 𝓜(q, α) μ₀ n₀)
      (openCoreSpec (q := q) (α := α) (dRows := dRows) (r := r) ω K.TCom F) :=
  haveI : ∀ i, SampleableType
      ((((!p[] : ProtocolSpec 0) ++ₚ
        pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r)).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
      (h₂ := CoordinateWise.SingleRound.instSampleableTypeChallengePSpec)
  evalChain (b := b) (γ := γ) init impl hq5 hκ hτ (esc ∪ K.esc) pp Q ▷
    rlinPackage (zDigits := zDigits) 𝓜(q, α) init impl pp (b : ZMod q) ω γ
      (esc ∪ K.esc) ▷
    liftPackage 𝓜(q, α) γ ρBound K φF init impl hd esc ▷
    batchPackage 𝓜(q, α) m₀ m₁ γ ρBound init impl K φF b hq2 hb esc ▷
    zeroCheckPackage 𝓜(q, α) m₀ m₁ γ ρBound init impl K φF b esc ▷
    sumcheckBridgePackage 𝓜(q, α) m₀ m₁ γ ρBound init impl K φF b esc

/-- **One full Hachi opening iteration** (rows 1–12 of the chain table): the pure prefix
`openCore` composed with the guarded tail: the `m₀` paired sumcheck rounds (Lemma 11, guarded on
the round checks), the final-evaluation step (guarded on the target checks), and the §4.5
recursion adapters (the pure partial-evaluation head, the ⚠ `Z`-packing bridge of
`HACHI_RECURSION_GAP.md`, and the guarded trace handoff). Pure factors (`openCore`,
`partialEvalPackage`, `zBatchPackage`) stay pure escape packages and are lifted into the
escape-guarded world by the mixed appends behind the universal `▷` (the head seam, whose
relation and escape identifications are the named `roundsChain_*` lemmas rather than `rfl`, uses
`EscapeCWSSPackage.appendEscapeGuarded` explicitly). The chain lands on the plain `relIn Φ'`
relation, with the ambient escape set carried separately — closing the recursion loop:
iteration `i+1` is this chain re-instantiated at `Φ'` (entering at `quadEvalPackage`, without
row 1).

The certificate `openingChain.isCWSS` is the one-iteration CWSS statement; its provenance (which
links are finished, skeleton-sorried, or gap-flagged) is inventoried in the module header. The
sumcheck arity is pinned to `m₀ := mLow + κ` so the recursion adapters can peel the top `κ`
variables. -/
noncomputable def openingChain (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ ρBound m₁ mLow κ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) E (liftShort 𝓜(q, α) γ ρBound))
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (Q : QuadEvalEscapeMap 𝓜(q, α) pp γ E)
    (esc : Set E)
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (hq2 : 2 * b ≤ q + 1) (hb : b - 1 ≤ γ)
    (zpow : Fin (2 ^ κ) → F)
    (Φ' : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ']
    {innerRows' messageDigits' outerRows' innerDigits' dRows' m' r' : ℕ}
    (pp' : Hachi.PublicParamsD Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r')
      innerDigits' dRows')
    (reinterpretCom : K.TCom → Commitment Φ' outerRows')
    (base' : ZMod q) (βSq' γ' κ' : ℕ) :
    EscapeGCWSSPackage init impl E
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (QuadEvalStatement Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r') innerDigits'
        dRows')
      (QuadEvalWitness Φ' innerRows' (2 ^ m') messageDigits' (2 ^ r') innerDigits')
      ((openCoreSpec (q := q) (α := α) (dRows := dRows) (r := r) ω K.TCom F ++ₚ
          roundsSpec F b (mLow + κ) ++ₚ pSpecFinalEval F) ++ₚ
        (pSpecPartialEval F κ ++ₚ ((!p[] : ProtocolSpec 0) ++ₚ pSpecHandoff Φ'))) :=
  haveI i₀ := openCoreSpecSampleable (q := q) (α := α) (dRows := dRows) (r := r) ω K.TCom F
  haveI i₁ : ∀ i, SampleableType
      (((openCoreSpec (q := q) (α := α) (dRows := dRows) (r := r) ω K.TCom F) ++ₚ
        roundsSpec F b (mLow + κ)).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend (h₁ := i₀)
      (h₂ := roundsSpecSampleable F b (mLow + κ))
  haveI i₂ : ∀ i, SampleableType
      ((((openCoreSpec (q := q) (α := α) (dRows := dRows) (r := r) ω K.TCom F) ++ₚ
          roundsSpec F b (mLow + κ)) ++ₚ pSpecFinalEval F).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend (h₁ := i₁)
      (h₂ := instSampleableTypeChallengePSpecFinalEval)
  (((openCore (m₀ := mLow + κ) (m₁ := m₁) init impl hq5 hκ hτ K pp Q esc φF hd hq2
      hb).appendEscapeGuarded
      (roundsChain 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF esc (mLow + κ))
      (roundsChain_relIn 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF esc
        (mLow + κ)).symm
      (roundsChain_escIn 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF esc
        (mLow + κ)).symm).append
    (finalEvalPackage 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF esc)
    (roundsChain_relOut 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF esc
      (mLow + κ))
    (roundsChain_escOut 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF esc
      (mLow + κ))) ▷
  partialEvalPackage 𝓜(q, α) mLow κ γ ρBound b init impl K φF esc ▷
  zBatchPackage 𝓜(q, α) mLow κ γ ρBound init impl zpow K φF esc ▷
  handoffPackage 𝓜(q, α) Φ' mLow κ γ ρBound init impl zpow K esc φF pp' reinterpretCom base' βSq'
    γ' κ'

/-- **Hachi one-iteration opening — coordinate-wise special soundness (skeleton certificate).**
The composed verifier of rows 1–12 is CWSS over the ordinary endpoint relations `relPolyEval`
(over the current ring `𝓜(q, α)`) and `relIn` (over `Φ'`), widened only in this certificate
by their corresponding parallel escape sets. The proof term is
just `openingChain.isCWSS`; its assumptions are exactly the sorried links inventoried in the
module header (in particular the ⚠ row-11 gap and the B4 guarded-append machinery). -/
theorem hachi_iteration_coordinateWiseSpecialSound (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ ρBound m₁ mLow κ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) E (liftShort 𝓜(q, α) γ ρBound))
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r)
      innerDigits dRows)
    (Q : QuadEvalEscapeMap 𝓜(q, α) pp γ E)
    (esc : Set E)
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (hq2 : 2 * b ≤ q + 1) (hb : b - 1 ≤ γ)
    (zpow : Fin (2 ^ κ) → F)
    (Φ' : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ']
    {innerRows' messageDigits' outerRows' innerDigits' dRows' m' r' : ℕ}
    (pp' : Hachi.PublicParamsD Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r')
      innerDigits' dRows')
    (reinterpretCom : K.TCom → Commitment Φ' outerRows')
    (base' : ZMod q) (βSq' γ' κ' : ℕ) :
    ((openingChain (zDigits := zDigits) (ω := ω) (mLow := mLow) (m₁ := m₁) init impl hq5 hκ
        hτ K pp Q esc φF hd hq2 hb zpow Φ' pp' reinterpretCom base' βSq'
        γ' κ')).verifier.coordinateWiseSpecialSound init impl
      (openingChain (zDigits := zDigits) (ω := ω) (mLow := mLow) (m₁ := m₁) init impl hq5 hκ hτ
        K pp Q esc φF hd hq2 hb zpow Φ' pp' reinterpretCom base' βSq' γ' κ').struct
      ((relPolyEval 𝓜(q, α) pp (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ
          (2 * ω)).withEscape ((esc ∪ K.esc) ∪ Q.localEsc))
      ((relIn Φ' pp' base' βSq' γ' κ').withEscape esc) :=
  (openingChain (zDigits := zDigits) (ω := ω) (mLow := mLow) (m₁ := m₁) init impl hq5 hκ hτ
    K pp Q esc φF hd hq2 hb zpow Φ' pp' reinterpretCom base' βSq' γ' κ').isCWSS

end OpeningChain

/-! ## TODO — growing the composition

* **§3 packing head (external extension-field claims).** The paper's headline
  multilinear-over-`F_{q^k}` interface (§3.1/§3.2) wraps an extension-field evaluation claim in
  front of `relPolyEval`; it is planned as an instance of the generalized `RingSwitching`
  packing phase (`HACHI_RING_SWITCHING_PLAN.md`, Phases B–E), not as a Hachi-local head.
* **Recursion termination.** At the row-12 seam: the §4.4 asymptotic base case (reveal the final
  small polynomial — a `SendWitness`-style tail) and the §4.5 concrete cutoff (switch to
  Greyhound/LaBRADOR, i.e. the JL projection route) are future zero-round/one-message tails.
* **Discharging the skeleton.** The sorry inventory in the module header, in dependency order:
  B4 (`Guarded.lean`) → F2.0/F2 → F3/F4 → F5 → F6 → F7 → F8 → G2/G3 — plus a repair decision for
  the row-11 gap (`HACHI_RECURSION_GAP.md`) and the Phase-G `LiftCom` instantiation (the
  inner-outer commitment without re-decomposition, its collision escape via
  `outputToModuleSIS_valid_of_verified`, and the ring-dimension reinterpretation used by row 12).
* **Knowledge-error accounting** (FMN24 Lemma 4), `Commitment.extractability`, and Fiat–Shamir
  remain out of scope (design D12/R6). -/

end ArkLib.Lattices.Ajtai.InnerOuter
