/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval
import ArkLib.Commitments.Functional.Hachi.LinSumcheck.FinalEval
import ArkLib.Commitments.Functional.Hachi.Recursion.TraceHandoff
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Package
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

/-!
# Hachi — the CWSS composition home

This is the designated home of the growing n-ary composition of the subprotocols of Hachi [NOZ26],
a lattice-based multilinear polynomial commitment scheme. Each subprotocol is formalized in its own
file and exported as a `CWSSPackage` (pure verifier) or `GCWSSPackage` (guarded verifier — may
`failure` at runtime), bundling the verifier with its proof of coordinate-wise special soundness
(CWSS), the knowledge-soundness notion under which a witness is extracted from a suitably
structured tree of accepting transcripts. This file only **imports those packages and chains
them**: pure links with `▷` (`CWSSPackage.append`, seams discharged by `rfl`), guarded links with
`▷ᵍ` (`GCWSSPackage.append`, the B4 skeleton in
`OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean`). The composed chain's
`isCWSS` field is the CWSS certificate for the whole reduction. (Hachi as a `Commitment.Scheme` —
the honest committer `keygen`/`commit` and the `hachi` functional commitment — lives in the
sibling `Commitment.lean`.)

## The three layers of this file

1. **`evalChain`** (sorry-free, finished): the polynomial-level bridge ▷ `QuadEval`
   (§4.2 / Figure 3 / Lemma 8).
2. **`openCore`** (skeleton, pure links): the escape-threaded front `evalChainE` extended by the
   §4.3 stages up to the sumcheck bridge — R^lin adapter (F2) ▷ HMZ25 lift (Figure 4 / Lemma 9)
   ▷ batching bridge (Eqs. (22)–(23)) ▷ zero-check (Figure 5 / **corrected** Lemma 10) ▷
   sumcheck bridge.
3. **`openingChain`** (skeleton, guarded tail): `openCore` ▷ᵍ the paired sumcheck loop
   (Figure 6 / Lemma 11, `m₀` guarded rounds) ▷ᵍ final evaluation (Figure 7 tail) ▷ᵍ the §4.5
   recursion adapters (partial evaluations ▷ᵍ `Z`-packing bridge ▷ᵍ trace handoff), landing on
   the **next iteration's** `QuadEval` input relation over the next ring `Φ'` — the recursion
   loop's closing seam.

## The composed verifier chain, seam by seam

Top-to-bottom is one opening iteration of the ArkLib Hachi commitment, whose committed data is an
`Rq`-valued multilinear polynomial. The opening starts with the Figure 3 path, not with §3: the §3
packing head (extension-field claims into `Rq`-claims, via the generalized `RingSwitching` packing
phase — see `HACHI_RING_SWITCHING_PLAN.md`, Phases B–E) is a separate track that wraps *external*
extension-field claims in front of `relPolyEval(E)`; the §4.5 adapters below close the recursion
*internally*. Witnesses in rows 3–11 are `· ⊕ E`: escape threading (`Set.withEscape`) gives every
seam a home for the `w̃`-commitment's weak-binding break (design G1; `E` abstract, escape set
`K.esc`).

```text
 # | link (file)                | rounds: wire         | relIn → relOut            | CWSS, k
---+----------------------------+----------------------+---------------------------+---------------
 1 | bridge (QuadEval/Bridge)   | 0                    | relPolyEvalE → relInE     | any (0 chals)
 2 | QuadEval (QuadEval/*)      | msg v; c ∈ C^{2^r}   | relInE → relOutE (Eq. 20) | ℓ=2^r, k=2 (L8)
 3 | R^lin (LinSumcheck/Rlin)   | 0                    | relOutE → relRlinE        | any
 4 | lift (LinSumcheck/Lift)    | msg t; α ∈ F         | relRlinE → relLiftE       | ℓ=1, k=2d (L9)
 5 | batch (…/BatchBridge)      | 0                    | relLiftE → relBatchedE    | any
 6 | zero-check (…/ZeroCheck)   | (ρ₀,ρ_α) ∈ F²        | relBatchedE → relZeroChkE | ℓ=2, k=D (L10*)
 7 | sc bridge (…/SumcheckBridge)| 0                   | relZeroChkE → roundRelE 0 | any
 8 | rounds ×m₀ (…/Rounds)      | (g-pair; aᵢ)ᵢ        | roundRelE 0 → roundRelE m₀| ℓ=1, k=2b+1
   |  — GUARDED: gᵢ(0)+gᵢ(1)=z |                      |                           |  (L11)/round
 9 | final eval (…/FinalEval)   | msg y′ ∈ F           | roundRelE m₀ → relWEvalE  | any — GUARDED
10 | partials (Recursion/PartialEval)| msg (yᵢ)_{i≠0}  | relWEvalE → relPartialE   | any (pure)
11 | Z-pack (…/ZBatchBridge)    | 0                    | relPartialE → relHatEvalE | any — ⚠ GAP
12 | handoff (…/TraceHandoff)   | msg p ∈ R′q          | relHatEvalE → relInE(Φ′)  | any — GUARDED
   |                            |                      |  = next iteration's row 2 |
```

- Rows 1–7 have **pure** verifiers: every check constrains either retained statement data or the
  never-sent witness, so it lives in the output relation (the `QuadEval` precedent). Rows 8, 9,
  12 are **guarded** (design D6): their runtime check reads data the next statement type drops
  (the previous sumcheck target; the final targets; the packed claim value) — exactly the paper's
  runtime checks — and compose via `▷ᵍ`, whose composition theorem (B4) is the one sorried piece
  of *generic* machinery.
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
- Row 12 lands on `relInE Φ'` — the escape-threaded `QuadEval` input relation at the **next**
  ring: iteration `i+1` re-enters at `quadEvalPackageE Φ'` directly (its bases are `eq`-tensor
  packings, not monomial bases, so the polynomial-level bridge of row 1 is head-only).
  Asymptotic termination (§4.4: reveal the final polynomial once small) and the concrete §4.5
  Greyhound/LaBRADOR cutoff are future zero-round tails at that seam.

## Sorry inventory of the composed chain (provenance of the certificate)

*Generic machinery* (B4): `Verifier.IsGuarded.append`,
`Verifier.append_coordinateWiseSpecialSound_of_guardedLeft` (`Guarded.lean`);
`coordinateWiseSpecialSound_of_mkWitness_scalar` (`ScalarRound.lean`, consumed only by future
proofs). *Escape threading* (F2.0): `quadEval_coordinateWiseSpecialSound_withEscape`.
*Per-link math*: the F2 index bookkeeping (`rlinStmt`/`unstack`/`mem_relOutE_of_relRlinE`),
Lemma 9 (`lift_coordinateWiseSpecialSound`), the F5 encodings (`Constraints.lean`), the
un-batching (`mem_relLiftE_of_relBatchedE`), corrected Lemma 10
(`zeroCheck_coordinateWiseSpecialSound`), the sum-to-point bridge, Lemma 11
(`round_coordinateWiseSpecialSound`), F8 (`finalEval_coordinateWiseSpecialSound` + the
`finalCheck` encoding), G2 (`partialEval_coordinateWiseSpecialSound` + its encoding defs), G3
(`handoff_coordinateWiseSpecialSound` + `traceCheck`/`toNextQuadEvalStatement`/`hatEval`).
Every sorried encoding def carries an in-situ `**Sorried**` docstring naming its milestone.
*Flagged as an open gap (not merely unproven)*: `mem_relPartialEvalE_of_relHatEvalE` (row 11).

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

/-- **The composed evaluation reduction** (Hachi [NOZ26, §4.2, Figure 3], `Rq`-level): the bridge
package chained with the `QuadEval` package via the `CWSSPackage` operator `▷`.
Both packages are defined next to their CWSS theorems in the component files (`bridgePackage` in
`QuadEval/Bridge`, `quadEvalPackage` in `QuadEval/Soundness`); here they are only imported and
composed. The seam is definitional — the bridge's `relOut` *is* `QuadEval`'s `relIn` — so `▷`
discharges it by `rfl`. The chain's `isCWSS` field is `eval_coordinateWiseSpecialSound`. This is
the finished, sorry-free core; the escape-threaded variant `evalChainE`
(`LinSumcheck/Escape.lean`) is its drop-in for the extended opening chain below. -/
def evalChain (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits) :
    CWSSPackage init impl
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        CarrierCom 𝓜(q, α) dRows × (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
      (QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
      ((!p[] : ProtocolSpec 0) ++ₚ
        pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r) :=
  bridgePackage 𝓜(q, α) init impl (b : ZMod q)
      (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) ▷
    quadEvalPackage init impl hq5 hκ hτ

/-- **Hachi evaluation reduction — coordinate-wise special soundness (Hachi [NOZ26, §4.2,
Figure 3], `Rq`-level), `sorry`-free.** This is the certificate carried by `evalChain`: the composed
verifier (bridge ⧺ `QuadEval`) is CWSS for `ofIsEmpty.append foldStructure`, reducing the
polynomial-level `relPolyEval` (a weak eval-consistent opening, or MSIS(B), or MSIS(D)) to Hachi
Eq. (20) (`relOut`), pinned to `𝓜(q, α)` with the [LS18] hypotheses of
`quadEval_coordinateWiseSpecialSound`. -/
theorem eval_coordinateWiseSpecialSound (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) (hq5 : q % 8 = 5) {b ω γ : ℕ}
    (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits) :
    ((bridgeVerifier (oSpec := oSpec) (innerRows := innerRows) (messageDigits := messageDigits)
          (outerRows := outerRows) (innerDigits := innerDigits) (dRows := dRows) (m := m) (r := r)
          𝓜(q, α)).append
        (verifier (oSpec := oSpec) (ω := ω) 𝓜(q, α))).coordinateWiseSpecialSound init impl
      (CWSSStructure.ofIsEmpty.append
        (foldStructure (CarrierCom := CarrierCom 𝓜(q, α) dRows)
          (C := ShortChallenge 𝓜(q, α) ω) (r := r)))
      (relPolyEval 𝓜(q, α) (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω))
      (relOut (zDigits := zDigits) 𝓜(q, α) (b : ZMod q) ω γ) :=
  (evalChain init impl hq5 hκ hτ).isCWSS

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
escape-threaded evaluation front (`evalChainE` = bridge ▷ `QuadEval`, both widened by the escape
budget `E`) extended by the §4.3 stages with pure verifiers — the `R^lin` adapter, the HMZ25
lift, the batching bridge, the (corrected-Lemma-10) zero-check, and the sumcheck bridge. Every
seam is definitional (`rfl`). The result reduces the polynomial-level `relPolyEvalE` to the
round-`0` sumcheck seam `roundRelE 0`. -/
noncomputable def openCore (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ ρBound m₀ m₁ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) E (liftShort 𝓜(q, α) γ ρBound))
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (hq2 : 2 * b ≤ q + 1) (hb : b - 1 ≤ γ) :
    CWSSPackage init impl
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits ⊕ E)
      (RoundStatement 𝓜(q, α) K.TCom F n₀ μ₀ 0)
      (LiftedWitness 𝓜(q, α) μ₀ n₀ ⊕ E)
      (openCoreSpec (q := q) (α := α) (dRows := dRows) (r := r) ω K.TCom F) :=
  haveI : ∀ i, SampleableType
      ((((!p[] : ProtocolSpec 0) ++ₚ
        pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r)).Challenge i) :=
    ProtocolSpec.instSampleableTypeChallengeAppend
      (h₁ := ProtocolSpec.instSampleableTypeChallengeEmpty)
      (h₂ := CoordinateWise.SingleRound.instSampleableTypeChallengePSpec)
  evalChainE (b := b) (γ := γ) init impl hq5 hκ hτ K.esc ▷
    rlinPackage (zDigits := zDigits) 𝓜(q, α) init impl (b : ZMod q) ω γ K.esc ▷
    liftPackage 𝓜(q, α) γ ρBound K φF init impl hd ▷
    batchPackage 𝓜(q, α) m₀ m₁ γ ρBound init impl K φF b hq2 hb ▷
    zeroCheckPackage 𝓜(q, α) m₀ m₁ γ ρBound init impl K φF b ▷
    sumcheckBridgePackage 𝓜(q, α) m₀ m₁ γ ρBound init impl K φF b

/-- **One full Hachi opening iteration** (rows 1–12 of the chain table): the pure prefix
`openCore` composed — through the guarded append `▷ᵍ` — with the guarded tail: the `m₀` paired
sumcheck rounds (Lemma 11, guarded on the round checks), the final-evaluation step (guarded on
the target checks), and the §4.5 recursion adapters (the pure partial-evaluation head, the ⚠
`Z`-packing bridge of `HACHI_RECURSION_GAP.md`, and the guarded trace handoff). The chain lands
on `relInE Φ'` — the escape-threaded `QuadEval` input relation at the next ring `Φ'` — closing
the recursion loop: iteration `i+1` is this chain re-instantiated at `Φ'` (entering at
`quadEvalPackageE`, without row 1).

The certificate `openingChain.isCWSS` is the one-iteration CWSS statement; its provenance (which
links are finished, skeleton-sorried, or gap-flagged) is inventoried in the module header. The
sumcheck arity is pinned to `m₀ := mLow + κ` so the recursion adapters can peel the top `κ`
variables. -/
noncomputable def openingChain (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ ρBound m₁ mLow κ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) E (liftShort 𝓜(q, α) γ ρBound))
    (φF : ZMod q →+* F)
    (hd : 0 < (𝓜(q, α)).φ.natDegree) (hq2 : 2 * b ≤ q + 1) (hb : b - 1 ≤ γ)
    (zpow : Fin (2 ^ κ) → F)
    (Φ' : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ']
    {innerRows' messageDigits' outerRows' innerDigits' dRows' m' r' : ℕ}
    (pp' : Hachi.PublicParamsD Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r')
      innerDigits' dRows')
    (reinterpretCom : K.TCom → Commitment Φ' outerRows')
    (base' : ZMod q) (βSq' γ' κ' : ℕ) :
    GCWSSPackage init impl
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalWitness 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits ⊕ E)
      (QuadEvalStatement Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r') innerDigits'
        dRows')
      (QuadEvalWitness Φ' innerRows' (2 ^ m') messageDigits' (2 ^ r') innerDigits' ⊕ E)
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
  (((openCore (m₀ := mLow + κ) (m₁ := m₁) init impl hq5 hκ hτ K φF hd hq2 hb).toGuarded.append
      (roundsChain 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF (mLow + κ))
      (roundsChain_relIn 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF
        (mLow + κ)).symm).append
    (finalEvalPackage 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF)
    (roundsChain_relOut 𝓜(q, α) (mLow + κ) m₁ γ ρBound b init impl K φF (mLow + κ))) ▷ᵍ
  (partialEvalPackage 𝓜(q, α) mLow κ γ ρBound b init impl K φF).toGuarded ▷ᵍ
  (zBatchPackage 𝓜(q, α) mLow κ γ ρBound init impl zpow K φF).toGuarded ▷ᵍ
  handoffPackage 𝓜(q, α) Φ' mLow κ γ ρBound init impl zpow K φF pp' reinterpretCom base' βSq'
    γ' κ'

/-- **Hachi one-iteration opening — coordinate-wise special soundness (skeleton certificate).**
The composed verifier of rows 1–12 is CWSS, reducing the polynomial-level `relPolyEvalE` (over
the current ring `𝓜(q, α)`) to the next iteration's `relInE` (over `Φ'`). The proof term is
just `openingChain.isCWSS`; its assumptions are exactly the sorried links inventoried in the
module header (in particular the ⚠ row-11 gap and the B4 guarded-append machinery). -/
theorem hachi_iteration_coordinateWiseSpecialSound (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ ρBound m₁ mLow κ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits)
    [SampleableType (ShortChallenge 𝓜(q, α) ω)]
    (K : LiftCom (LiftedWitness 𝓜(q, α) μ₀ n₀) E (liftShort 𝓜(q, α) γ ρBound))
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
        hτ K φF hd hq2 hb zpow Φ' pp' reinterpretCom base' βSq'
        γ' κ')).verifier.coordinateWiseSpecialSound init impl
      (openingChain (zDigits := zDigits) (ω := ω) (mLow := mLow) (m₁ := m₁) init impl hq5 hκ hτ
        K φF hd hq2 hb zpow Φ' pp' reinterpretCom base' βSq' γ' κ').struct
      (relPolyEvalE 𝓜(q, α) (b : ZMod q)
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) K.esc)
      (relInE Φ' base' βSq' γ' κ' K.esc) :=
  (openingChain (zDigits := zDigits) (ω := ω) (mLow := mLow) (m₁ := m₁) init impl hq5 hκ hτ
    K φF hd hq2 hb zpow Φ' pp' reinterpretCom base' βSq' γ' κ').isCWSS

end OpeningChain

/-! ## TODO — growing the composition

* **§3 packing head (external extension-field claims).** The paper's headline
  multilinear-over-`F_{q^k}` interface (§3.1/§3.2) wraps an extension-field evaluation claim in
  front of `relPolyEvalE`; it is planned as an instance of the generalized `RingSwitching`
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
