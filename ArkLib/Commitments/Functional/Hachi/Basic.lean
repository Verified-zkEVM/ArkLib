/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.PolynomialQuadraticEq.PolyEvalReduction
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Scheme
import ArkLib.Commitments.Functional.Basic
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge

/-!
# Hachi as a Functional Commitment — the composition home

This is the designated home of Hachi [NOZ26] as a **functional commitment** and of the growing
n-ary composition of its subprotocols. Right now the composed verifier chains exactly two factors:

* the zero-round **bridge** (`PolyEvalReduction.bridgeVerifier`), which reinterprets a
  `CMlPolynomial`-level statement as a `QuadEvalStatement` (monomial-basis instantiation of the
  Eq. (12) bases), and
* Hachi's two-round **`QuadEval`** reduction (Lemma 8).

`evalVerifier` is their `Verifier.append`; `hachi_eval_coordinateWiseSpecialSound` is the
composed coordinate-wise special soundness — sorry-free — obtained from
`Verifier.append_coordinateWiseSpecialSound` (the left factor is `IsPure`, so `hV₁` is `rfl`;
statement chaining is definitional). The composed structure is
`CWSSStructure.ofIsEmpty.append foldStructure`; the input relation is the polynomial-level
`relPolyEval` and the output relation is Hachi Eq. (20) (`relOut`).

## Growing the composition

Each further §4.3+ subprotocol is appended with its own CWSS proof; any shape mismatch between
`relOut_i` and `relIn_{i+1}` gets its own zero-round `ReduceClaim` adapter (same recipe as the
bridge). Once ≥3 factors exist, upgrade the binary `Verifier.append` to `Verifier.seqCompose` +
`seqCompose_coordinateWiseSpecialSound`: every factor is `IsPure` and `seqCompose_succ_eq_append`
is `rfl`, so no rework of the existing proof is needed. The `𝔽_{q^k}` ring-switch entry point
(§4.1) is a future zero-round head adapter placed in front of `relPolyEval`, built by the same
recipe as the bridge.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.SingleRound

section Composition

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α : ℕ}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}
variable {ι : Type} {oSpec : OracleSpec ι} {ω : ℕ}

/-- The **composed evaluation verifier**: the zero-round polynomial-level bridge
(`bridgeVerifier`) followed by Hachi's two-round `QuadEval` reduction (`verifier`). Stated over the
appended protocol spec `!p[] ++ₚ pSpec …` (its length index `0 + 2` is defeq to `2`, but the
vappend contents are not syntactically the bare two-round spec, so we keep the appended form). -/
def evalVerifier :
    Verifier oSpec
      (PolyEvalStatement 𝓜(q, α) innerRows messageDigits outerRows innerDigits dRows m r)
      (QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows
        × CarrierCom 𝓜(q, α) dRows × (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
      ((!p[] : ProtocolSpec 0) ++ₚ
        pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r) :=
  (bridgeVerifier (oSpec := oSpec) 𝓜(q, α)).append (verifier (oSpec := oSpec) (ω := ω) 𝓜(q, α))

/-- **Hachi evaluation reduction — coordinate-wise special soundness of the composed protocol
(Hachi §4.2/Figure 3, `Rq`-level), sorry-free.** The composed `evalVerifier` (bridge ⧺ QuadEval) is
coordinate-wise special sound for the appended structure `ofIsEmpty.append foldStructure`, reducing
the polynomial-level input relation `relPolyEval` (a weak eval-consistent opening, or MSIS(B), or
MSIS(D)) to Hachi Eq. (20) (`relOut`). Pinned to `𝓜(q, α)` with the [LS18] hypotheses exactly as
`quadEval_coordinateWiseSpecialSound`. Assembled by `Verifier.append_coordinateWiseSpecialSound`:
the bridge's CWSS (`bridge_coordinateWiseSpecialSound`, any `D`) composes with QuadEval's Lemma 8
(`quadEval_coordinateWiseSpecialSound'`); the left factor is pure so `hV₁` is `rfl` and the middle
relation is QuadEval's `relIn`. -/
theorem hachi_eval_coordinateWiseSpecialSound {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits) :
    (evalVerifier (oSpec := oSpec) (ω := ω) (q := q) (α := α) (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows) (innerDigits := innerDigits)
        (dRows := dRows) (m := m) (r := r)).coordinateWiseSpecialSound init impl
      (CWSSStructure.ofIsEmpty.append
        (foldStructure (CarrierCom := CarrierCom 𝓜(q, α) dRows)
          (C := ShortChallenge 𝓜(q, α) ω) (r := r)))
      (relPolyEval 𝓜(q, α) ((b : ZMod q))
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω))
      (relOut (zDigits := zDigits) 𝓜(q, α) ((b : ZMod q)) ω γ) := by
  unfold evalVerifier
  exact Verifier.append_coordinateWiseSpecialSound init impl _ _ _ _
    (fun s _ => toQuadEvalStatement 𝓜(q, α) s) (fun _ _ => rfl)
    (bridge_coordinateWiseSpecialSound 𝓜(q, α) init impl CWSSStructure.ofIsEmpty ((b : ZMod q))
      (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω))
    (quadEval_coordinateWiseSpecialSound' init impl hq5 hκ hτ)

end Composition

/-! ## Functional-commitment scaffolding

Hachi as a `Commitment.Scheme` (`ArkLib.Commitments.Functional.Basic`) over the multilinear data
`CMlPolynomial (Rq 𝓜(q,α)) (r + m)`. The eval-oracle interface and the honest committer operations
(`hachiKeygen` / `hachiCommit`) are real; the opening `Proof` is deferred (see the `TODO` block). -/

section FunctionalCommitment

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α : ℕ}
variable {innerRows messageDigits outerRows innerDigits dRows m r : Nat} {ω : ℕ}

/-- The **evaluation oracle** on a committed multilinear polynomial: a query is a split evaluation
point `(xl, xh)` (the split matches `PolyEvalStatement`; the unsplit view `xl ++ xh` is a later
cosmetic lens), and the answer is `f(xl ++ xh)`. This is the `OracleInterface` that makes
`CMlPolynomial (Rq 𝓜(q,α)) (r + m)` the `Data` of a functional commitment (`Commitment.Scheme`);
`toOC` follows `OracleContext.ofFunction`. -/
instance evalOracleInterface :
    OracleInterface (CMlPolynomial (Rq 𝓜(q, α)) (r + m)) where
  Query := Vector (Rq 𝓜(q, α)) r × Vector (Rq 𝓜(q, α)) m
  toOC :=
    { spec := (Vector (Rq 𝓜(q, α)) r × Vector (Rq 𝓜(q, α)) m) →ₒ Rq 𝓜(q, α)
      impl := fun p => do return CMlPolynomial.eval (← read) (p.1 ++ p.2) }

variable
  [SampleableType (Simple.PublicParams 𝓜(q, α) innerRows ((2 ^ m) * messageDigits))]
  [SampleableType (Simple.PublicParams 𝓜(q, α) outerRows ((2 ^ r) * (innerRows * innerDigits)))]
  [SampleableType (Simple.PublicParams 𝓜(q, α) dRows ((2 ^ r) * messageDigits))]

/-- Honest **key generation**: sample the inner/outer/short Ajtai matrices `(A, B, D)` uniformly
(matching `InnerOuter.commitmentScheme.setup`, extended with the Hachi short-commitment matrix `D`,
Eq. (16)) and return the resulting `PublicParamsD` as both the committer and the verifier key. -/
def hachiKeygen :
    ProbComp
      (Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows ×
        Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
          dRows) := do
  let A ← $ᵗ (Simple.PublicParams 𝓜(q, α) innerRows ((2 ^ m) * messageDigits))
  let B ← $ᵗ (Simple.PublicParams 𝓜(q, α) outerRows ((2 ^ r) * (innerRows * innerDigits)))
  let D ← $ᵗ (Simple.PublicParams 𝓜(q, α) dRows ((2 ^ r) * messageDigits))
  let pp :
      Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
        dRows :=
    { innerMatrix := A, outerMatrix := B, dMatrix := D }
  pure (pp, pp)

/-- Honest **commitment**: reshape the polynomial into its `2^r × 2^m` coefficient matrix
(`Hachi.toMatrix`, which is definitionally a `Message 𝓜(q,α) (2^m) (2^r)`), gadget-decompose it into
the per-block messages/inner decompositions (`generateDecomps` with `Decomposition.ofDigits`), and
outer-commit (`commitWithDecomps`). Deterministic; the decommitment is the `Decomp` data. -/
def hachiCommit [DecidableEq (ZMod q)] {base : ZMod q}
    (ddMsg : DigitDecomposition base messageDigits)
    (ddInner : DigitDecomposition base innerDigits)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (p : CMlPolynomial (Rq 𝓜(q, α)) (r + m)) :
    Commitment 𝓜(q, α) outerRows ×
      Decomp 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits :=
  let decomps := generateDecomps 𝓜(q, α) (Decomposition.ofDigits 𝓜(q, α) ddMsg ddInner)
    pp.toPublicParams (Hachi.toMatrix p)
  (commitWithDecomps 𝓜(q, α) pp.toPublicParams decomps, decomps)

/-- **Hachi as a functional commitment** (`Commitment.Scheme`) over the multilinear data
`CMlPolynomial (Rq 𝓜(q,α)) (r + m)`, with the eval oracle `evalOracleInterface`, honest
`hachiKeygen` / `hachiCommit`, committer and verifier key `PublicParamsD`, and decommitment
`Decomp`.

The `opening` field — the complete opening `Proof` (a `Reduction … Bool Unit`) — is **provisional**
(`sorry`): its boolean verdict is Hachi Eq. (20) membership (`relOut`), which depends on the never-
sent triple `(ŵ, t̂, ẑ)`; it becomes verifier-computable only after the remaining §4.3+ subprotocols
(and their honest-prover layer, `QuadEval.computeV`/`computeResp`, §9.3) are formalized. Everything
else here is real. The stated `pSpec` is the composed evaluation protocol spec (`!p[] ++ₚ pSpec …`),
i.e. the shape the finished opening will run over — see the `TODO` block. -/
noncomputable def hachiFC [DecidableEq (ZMod q)] {base : ZMod q}
    (ddMsg : DigitDecomposition base messageDigits)
    (ddInner : DigitDecomposition base innerDigits) :
    _root_.Commitment.Scheme unifSpec
      (CMlPolynomial (Rq 𝓜(q, α)) (r + m))
      (Commitment 𝓜(q, α) outerRows)
      (Decomp 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
        dRows)
      (Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
        dRows)
      ((!p[] : ProtocolSpec 0) ++ₚ
        pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r) where
  keygen := hachiKeygen
  commit := fun pp p => pure (hachiCommit ddMsg ddInner pp p)
  opening := sorry

end FunctionalCommitment

/-! ## TODO — remaining work toward the full Hachi functional commitment

The composition (`evalVerifier` / `hachi_eval_coordinateWiseSpecialSound`) is the `Rq`-level
CWSS core; the FC scaffolding (`evalOracleInterface`, `hachiKeygen`, `hachiCommit`, `hachiFC`) is
the honest committer side. Still open, in rough dependency order:

* **Remaining §4.3+ subprotocols.** Each is appended to `evalVerifier` with its own CWSS proof,
  bridged by a zero-round `ReduceClaim` adapter when `relOut_i`/`relIn_{i+1}` disagree in shape.
  Once ≥3 factors accumulate, migrate the binary `Verifier.append` to `Verifier.seqCompose` +
  `seqCompose_coordinateWiseSpecialSound` (every factor is `IsPure`, `seqCompose_succ_eq_append`
  is `rfl`).
* **Completeness / honest-prover layer** (§9.3): instantiate `QuadEval.prover`'s `computeV` /
  `computeResp` from the `QuadEvalGadgets` carrier/decomposition definitions, discharging
  `Commitment.perfectCorrectness` for `hachiFC` — this is what materializes `hachiFC.opening`
  (currently `sorry`).
* **CWSS → knowledge-extraction bridge** and the cross-run step
  (`outputToModuleSIS_valid_of_verified`): turn the coordinate-wise special soundness into the
  `Commitment.extractability` / `functionBinding` statements.
* **`𝔽_{q^k}` ring-switch head** (§4.1): a zero-round head adapter in front of `relPolyEval`
  lifting the `Rq`-level statement to the paper's headline multilinear-over-`𝔽_{q^k}` claim.
* **`ShortChallenge` instances.** Stating `Commitment.perfectCorrectness` / `extractability` needs
  `[[pSpec.Challenge]ₒ.Fintype]` / `VCVCompatible` / `SampleableType` for `ShortChallenge 𝓜(q,α) ω`
  (a subtype of `Rq`); the requisite `Fintype`/`DecidablePred` work does not yet exist.
-/

end ArkLib.Lattices.Ajtai.InnerOuter
