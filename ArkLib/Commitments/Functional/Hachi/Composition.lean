/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.NoChallenge
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Package

/-!
# Hachi — the CWSS composition home

This is the designated home of the growing n-ary composition of the subprotocols of Hachi [NOZ26],
a lattice-based multilinear polynomial commitment scheme. Each subprotocol is formalized in its own
file and exported as a `CWSSPackage` — a verifier bundled with its proof of coordinate-wise special
soundness (CWSS), the knowledge-soundness notion under which a witness can be extracted from a
suitably structured tree of accepting transcripts. This file only **imports those packages and
chains them** with the `▷` operator (`CWSSPackage.append`). The composed chain's `isCWSS` field is
the CWSS certificate for the whole reduction, so growing the protocol is a one-line `▷`. (Hachi as
a `Commitment.Scheme` — the honest committer `keygen`/`commit` and the `hachi` functional
commitment — lives in the sibling `Commitment.lean`.)

Right now the finished core chains exactly two links — the polynomial-level bridge and `QuadEval`
(`evalChain = bridgePackage ▷ quadEvalPackage`, certificate `eval_coordinateWiseSpecialSound`). The
remaining §3/§4.3+/§4.5 subprotocols are placeholders (see the `TODO` block); each will land as one
more `CWSSPackage` `▷`-appended into the chain.

## Components — where each piece lives and which part of the paper it is

Finished pieces, each in its own file (paths under `Commitments/Functional/Hachi/` unless marked
*generic*); paper references are to Hachi [NOZ26]:

* **Ajtai gadget matrices** (§2.1) — `Gadget/{Basic, Norms}`.
* **Inner-outer Ajtai commitment** + weak binding (§4.1) —
  `InnerOuter/{Scheme, Correctness, Security, Arithmetic}`.
* **Multilinear evaluation as a matrix–vector product** (§4, Eq. (12)) — `EvalSplit`.
* **`QuadEval` gadget algebra** (§4.2, Figure 3) — `QuadEval/Gadgets`.
* **`QuadEval` reduction** (§4.2) — `QuadEval/Reduction` (types, relations, protocol); its
  Lemma 8 CWSS soundness and `quadEvalPackage` live in `QuadEval/Soundness`.
* **Polynomial-level bridge** (§4.2) — `QuadEval/Bridge`, exported as `bridgePackage`.
* **Functional-commitment interface** (`Commitment.Scheme`) — `Commitment` (honest committer).
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
`QuadEval/Bridge`, `quadEvalPackage` in `QuadEval/Soundness`); here they are only imported and
composed. The seam is definitional — the bridge's `relOut` *is* `QuadEval`'s `relIn` — so `▷`
discharges it by `rfl`. The chain's `isCWSS` field is `eval_coordinateWiseSpecialSound`; each
further §3/§4.3+ subprotocol is one more package `▷`-appended here (see the module header). -/
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

/-! ## TODO — growing the composition

`evalChain` / `eval_coordinateWiseSpecialSound` is the finished `Rq`-level CWSS core (bridge ▷
`QuadEval`). Still open:

* **Remaining §3/§4.3+/§4.5 subprotocols.** Each is exported from its file as a `CWSSPackage` and
  `▷`-appended into `evalChain`, bridged by a zero-round `ReduceClaim` package when one `relOut`
  and the next `relIn` disagree in shape. Guarded subprotocols need a guarded variant of `▷`. Once
  the chain is long, migrate the binary `▷` to the n-ary `Verifier.seqCompose` +
  `seqCompose_coordinateWiseSpecialSound` (every factor is `IsPure`, `seqCompose_succ_eq_append`
  is `rfl`). -/

end ArkLib.Lattices.Ajtai.InnerOuter
