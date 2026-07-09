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
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Package

/-!
# Hachi as a Functional Commitment — the composition home

This is the designated home of Hachi [NOZ26] as a **functional commitment** and of the growing
n-ary composition of its subprotocols. Each subprotocol is formalized in its own file and exported
as a coordinate-wise-special-sound (CWSS) `CWSSPackage`; this file only **imports those packages
and chains them** with the `▷` operator (`CWSSPackage.append`). The composed chain's `isCWSS` field
is the CWSS certificate for the whole reduction, so growing the protocol is a one-line `▷`.

Right now the finished core chains exactly two links — the polynomial-level bridge and `QuadEval`
(`evalChain = bridgePackage ▷ quadEvalPackage`, certificate `eval_coordinateWiseSpecialSound`). The
remaining §3/§4.3+/§4.5 subprotocols are placeholders (see the `TODO` block); each will land as one
more `CWSSPackage` `▷`-appended into the chain.

## Components — where each piece lives and which part of the paper it is

Finished pieces, each in its own file (paths under `Commitments/Functional/Hachi/` unless marked
*generic*); paper references are to Hachi [NOZ26]:

* **Ajtai gadget matrices** (§2.1/§4.1) — `Gadget`, `GadgetNorms`.
* **Inner-outer Ajtai commitment** + weak binding (§4.1) —
  `InnerOuter/{Scheme, Correctness, Security, Arithmetic}`.
* **Multilinear evaluation as a matrix–vector product** (§4) — `PolynomialEvalSplit`.
* **`QuadEval` gadget algebra** (§4.2, Figure 3) — `PolynomialQuadraticEq/QuadEvalGadgets`.
* **`QuadEval` reduction** (§4.2, Lemma 8) — `PolynomialQuadraticEq/QuadEval`, exported as
  `quadEvalPackage`.
* **Polynomial-level bridge** (§4.2) — `PolynomialQuadraticEq/PolyEvalReduction`, exported as
  `bridgePackage`.
* **Single-round CWSS tree navigation** *(generic)* —
  `OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound`.
* **`CWSSPackage` + the `▷` chain operator** *(generic)* —
  `OracleReduction/Security/CoordinateWiseSpecialSoundness/Package`.

## The composed verifier chain

Top-to-bottom is the composition order (each `▷` is one `CWSSPackage`). The `═══` band is the
finished core (`evalChain`); everything else is a placeholder for a future package:

```text
  §3.2/§4.5  partial-evaluations head           ── planned (pure, 1 msg)
      │ ▷
      ▼
  §3.1  ring-switch packing head                ── planned (guarded, 1 msg)
      │ ▷
      ▼
  σ₋₁ statement adapter                         ── planned (0-round ReduceClaim)
      │ ▷
  ═══════════════════════ evalChain (finished core) ═══════════════════════
      ▼
  bridge     PolyEvalStatement ⇒ QuadEval.relIn   bridgePackage   (§4.2, 0-round)
      │ ▷
      ▼
  QuadEval   QuadEval.relIn ⇒ Eq.(20) relOut      quadEvalPackage (§4.2, Lemma 8)
  ══════════════════════════════════════════════════════════════════════════
      │ ▷
      ▼
  §4.3  Eq.(20) ⇒ R^lin ⇒ HMZ25 lift ⇒
        zero-check rounds ⇒ sumcheck ⇒ final eval ── planned (Lemmas 9–11)
      │ ▷
      ▼
  §4.5  recursion handoff ⇒ next iteration       ── planned (guarded)
```

## Growing the composition

Each further subprotocol is exported from its file as a `CWSSPackage` and `▷`-appended here; a shape
mismatch between one package's `relOut` and the next's `relIn` gets its own zero-round `ReduceClaim`
package (the same recipe as `bridgePackage`). Guarded subprotocols (the §3.1 head, the sumcheck
rounds, the final-eval and §4.5 handoff — those whose runtime check reads data the next statement
type drops) need a guarded variant of `▷`; the pure links compose as above. Once the chain is long,
the binary `▷` can be replaced by the n-ary `Verifier.seqCompose` (every finished factor is
`IsPure` and `seqCompose_succ_eq_append` is `rfl`, so no existing proof is reworked).

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
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
package (link 3) chained with the `QuadEval` package (link 4) via the `CWSSPackage` operator `▷`.
Both packages are defined next to their CWSS theorems in the component files (`bridgePackage` in
`PolyEvalReduction`, `quadEvalPackage` in `QuadEval`); here they are only imported and composed. The
seam is definitional — the bridge's `relOut` *is* `QuadEval`'s `relIn` — so `▷` discharges it by
`rfl`. The chain's `isCWSS` field is `eval_coordinateWiseSpecialSound`; each further §3/§4.3+
subprotocol is one more package `▷`-appended here (see the module header). -/
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

/-! ## Functional-commitment scaffolding

Hachi as a `Commitment.Scheme` (`ArkLib.Commitments.Functional.Basic`) over the multilinear data
`CMlPolynomial (Rq 𝓜(q,α)) (r + m)`. The eval-oracle interface and the honest committer operations
(`keygen` / `commit`) are real; the opening `Proof` is deferred (see the `TODO` block). -/

section FunctionalCommitment

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α : ℕ}
variable {innerRows outerRows dRows m r : Nat} {ω : ℕ}

/-- The **multilinear evaluation oracle** on a committed `n`-variable multilinear polynomial: a
query is an evaluation point `x : Vector (Rq 𝓜(q,α)) n` and the answer is `f x`. This is the
`OracleInterface` that makes `CMlPolynomial (Rq 𝓜(q,α)) n` the `Data` of a functional commitment
(`Commitment.Scheme`); `toOC` follows `OracleContext.ofFunction`. -/
instance multilinearEvalOracleInterface {n : ℕ} :
    OracleInterface (CMlPolynomial (Rq 𝓜(q, α)) n) where
  Query := Vector (Rq 𝓜(q, α)) n
  toOC :=
    { spec := Vector (Rq 𝓜(q, α)) n →ₒ Rq 𝓜(q, α)
      impl := fun p => do return CMlPolynomial.eval (← read) p }

-- `b > 1` is the gadget base used for **all** decompositions. Faithful to Hachi [NOZ26] §2.1/§4.1,
-- every coefficient is written in `δ := ⌈log_b q⌉ = Nat.clog b q` base-`b` digits — a single `δ`
-- shared by the message gadget `G⁻¹_{2ᵐ}` and the inner gadget `G⁻¹_{n_A}` — so both digit counts
-- are `Nat.clog b q` (and `q ≤ bᵟ` holds by `Nat.le_pow_clog`).
variable (b : ℕ)

variable
  [SampleableType (Simple.PublicParams 𝓜(q, α) innerRows ((2 ^ m) * Nat.clog b q))]
  [SampleableType (Simple.PublicParams 𝓜(q, α) outerRows ((2 ^ r) * (innerRows * Nat.clog b q)))]
  [SampleableType (Simple.PublicParams 𝓜(q, α) dRows ((2 ^ r) * Nat.clog b q))]

/-- Honest **key generation**: sample the inner/outer/short Ajtai matrices `(A, B, D)` uniformly
(matching `InnerOuter.commitmentScheme.setup`, extended with the Hachi short-commitment matrix `D`,
Eq. (16)) and return the resulting `PublicParamsD` as both the committer and the verifier key. -/
def keygen :
    ProbComp
      (Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r) (Nat.clog b q)
          dRows ×
        Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r)
          (Nat.clog b q) dRows) := do
  let A ← $ᵗ (Simple.PublicParams 𝓜(q, α) innerRows ((2 ^ m) * Nat.clog b q))
  let B ← $ᵗ (Simple.PublicParams 𝓜(q, α) outerRows ((2 ^ r) * (innerRows * Nat.clog b q)))
  let D ← $ᵗ (Simple.PublicParams 𝓜(q, α) dRows ((2 ^ r) * Nat.clog b q))
  let pp :
      Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r) (Nat.clog b q)
        dRows :=
    { innerMatrix := A, outerMatrix := B, dMatrix := D }
  pure (pp, pp)

/-- Honest **commitment** to a multilinear polynomial `p`: reshape it into its `2^r × 2^m`
coefficient matrix (`Hachi.toMatrix`, definitionally a `Message 𝓜(q,α) (2^m) (2^r)`),
gadget-decompose it into the per-block messages/inner decompositions with the **canonical base-`b`
digit decomposition** `zmodDigitDecomposition` at the paper's width `δ = ⌈log_b q⌉ = Nat.clog b q`
(the `q ≤ bᵟ` obligation is `Nat.le_pow_clog`), and outer-commit (`commitWithDecomps`).
Deterministic; the decommitment is the `Decomp` data. -/
def commit [DecidableEq (ZMod q)] (hb : 1 < b)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r)
      (Nat.clog b q) dRows)
    (p : CMlPolynomial (Rq 𝓜(q, α)) (r + m)) :
    Commitment 𝓜(q, α) outerRows ×
      Decomp 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) (2 ^ r) (Nat.clog b q) :=
  let decomps := generateDecomps 𝓜(q, α)
    (Decomposition.ofDigits 𝓜(q, α)
      (zmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q))
      (zmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q)))
    pp.toPublicParams (Hachi.toMatrix p)
  (commitWithDecomps 𝓜(q, α) pp.toPublicParams decomps, decomps)

/-- **Hachi as a functional commitment** (`Commitment.Scheme`) over the multilinear data
`CMlPolynomial (Rq 𝓜(q,α)) (r + m)` — an `(r + m)`-variable polynomial, with the `r`/`m` split
feeding the outer/inner gadgets. It commits a polynomial directly (no caller-supplied
decompositions): the honest `commit` uses the canonical base-`b` gadget decomposition at the
paper's width `δ = ⌈log_b q⌉ = Nat.clog b q` (Hachi [NOZ26] §2.1/§4.1), shared by the message and
inner gadgets — so `messageDigits`/`innerDigits` are not free parameters. The only parameters are
the gadget base `b` and `1 < b`; the scheme carries the eval oracle
`multilinearEvalOracleInterface`, honest `keygen` / `commit`, committer and verifier key
`PublicParamsD`, and decommitment `Decomp`.

The `opening` field — the complete opening `Proof` (a `Reduction … Bool Unit`) — is **provisional**
(`sorry`): its boolean verdict is Hachi Eq. (20) membership (`relOut`), which depends on the never-
sent triple `(ŵ, t̂, ẑ)`; it becomes verifier-computable only after the remaining §4.3+ subprotocols
and their honest-prover layer (`QuadEval.prover`'s `computeV`/`computeResp`) are formalized.
Everything else here is real. The stated `pSpec` is the composed evaluation protocol spec
(`!p[] ++ₚ pSpec …`), i.e. the shape the finished opening will run over — see the `TODO` block. -/
def hachi [DecidableEq (ZMod q)] (hb : 1 < b) :
    Commitment.Scheme unifSpec
      (CMlPolynomial (Rq 𝓜(q, α)) (r + m))
      (Commitment 𝓜(q, α) outerRows)
      (Decomp 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) (2 ^ r) (Nat.clog b q))
      (Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r) (Nat.clog b q)
        dRows)
      (Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r) (Nat.clog b q)
        dRows)
      ((!p[] : ProtocolSpec 0) ++ₚ
        pSpec (CarrierCom 𝓜(q, α) dRows) (ShortChallenge 𝓜(q, α) ω) r) where
  keygen := keygen b
  commit := fun pp p => pure (commit b hb pp p)
  opening := sorry

end FunctionalCommitment

/-! ## TODO — remaining work toward the full Hachi functional commitment

The composition (`evalChain` / `eval_coordinateWiseSpecialSound`) is the `Rq`-level CWSS core; the
FC scaffolding (`multilinearEvalOracleInterface`, `keygen`, `commit`, `fc`) is the honest committer
side. Still open, in rough dependency order:

* **Remaining §3/§4.3+/§4.5 subprotocols.** Each is exported from its file as a `CWSSPackage` and
  `▷`-appended into `evalChain`, bridged by a zero-round `ReduceClaim` package when one `relOut`
  and the next `relIn` disagree in shape. Guarded subprotocols need a guarded variant of `▷`. Once
  the chain is long, migrate the binary `▷` to the n-ary `Verifier.seqCompose` +
  `seqCompose_coordinateWiseSpecialSound` (every factor is `IsPure`, `seqCompose_succ_eq_append`
  is `rfl`).
* **Completeness / honest-prover layer**: instantiate `QuadEval.prover`'s `computeV` /
  `computeResp` from the `QuadEvalGadgets` carrier/decomposition definitions
  (`carrierCommit`, `zDecomp`), discharging `Commitment.perfectCorrectness` for `fc` —
  this is what materializes `fc.opening` (currently `sorry`).
-/

end ArkLib.Lattices.Ajtai.InnerOuter
