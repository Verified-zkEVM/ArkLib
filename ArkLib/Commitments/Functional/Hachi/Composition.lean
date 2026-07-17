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
remaining §4.3+ opening stages and the §3/§4.5 recursion adapters are placeholders (see the `TODO`
block).

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

Top-to-bottom is one opening iteration of the ArkLib Hachi commitment, whose committed data is an
`Rq`-valued multilinear polynomial. Consequently the opening starts with the Figure 3 path, not
with §3. Section 3 only converts the smaller extension-field evaluation produced at the end back
into an `Rq` evaluation for the **next** iteration (and may separately wrap an external
extension-field claim). It is not the HMZ25 ring-switching subprotocol: that is Figure 4 in §4.3,
after `QuadEval`. The `═══` band is the finished core (`evalChain`); all other links are planned
packages (plus zero-round relation adapters where statement shapes differ):

```text
  committed f : CMlPolynomial Rq (r + m), with an Rq evaluation query (x, y)
      │
  ═══════════════════════ evalChain (finished core) ═══════════════════════
      ▼
  bridge     PolyEvalStatement ⇒ QuadEval.relIn   bridgePackage   (§4.2, 0-round)
      │ ▷
      ▼
  QuadEval   QuadEval.relIn ⇒ Eq. (20) relOut     quadEvalPackage (§4.2, Figure 3,
                                                                  Lemma 8)
  ══════════════════════════════════════════════════════════════════════════
      │ ▷  read (t̂, ŵ, ẑ) and the block equation as an Rq-linear relation R^lin
      ├─ optional concrete cutoff: use §4.5 JL / LaBRADOR instead of §4.3
      │
      ▼
  §4.3, Figure 4   HMZ25 ring switching: commit to (z, r), sample α,
                   reduce R^lin over Rq to constraints over F_{q^k}  planned (Lemma 9)
      │ ▷
      ▼
  §4.3, Figure 5   batch the linear and range constraints into
                   H_α and H_0; sample evaluation points τ₁ and τ₀  planned (Lemma 10)
      │ ▷
      ▼
  §4.3, Figures 6–7  sumcheck rounds g_i(X_i), challenges a_i,
                     then open w̃(a₁, …, a_ℓ)                        planned (Lemma 11)
      │
      ▼
  smaller evaluation claim over F_{q^k}
      ├─ recurse (§4.4):
      │     §3.2  partial evaluations (the recursive polynomial has F_q coefficients)
      │       │ ▷
      │       ▼
      │     §3.1  packing / trace encoding ⇒ Rq polynomial evaluation
      │       └────────────────────────────── loop to bridge for the next iteration
      ├─ asymptotic termination: reveal the final polynomial once it is small (§4.4)
      └─ concrete cutoff: §4.5 repacking without re-decomposition, then Greyhound
```

## Growing the composition

Each §4.3 opening subprotocol is exported from its file as a `CWSSPackage` and appended after
`evalChain`. Recursive composition then routes its final extension-field claim through the §3
adapters before invoking `evalChain` again. A shape mismatch between one package's `relOut` and the
next's `relIn` gets its own zero-round `ReduceClaim` package (the same recipe as `bridgePackage`).
Links whose runtime check reads data the next statement type drops need a guarded variant of `▷`;
the pure links compose as above. Once the chain is long, the binary `▷` can be replaced by the
n-ary `Verifier.seqCompose` (`seqCompose_succ_eq_append` is `rfl` for the finished pure factors, so
their existing proofs are not reworked).

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
package chained with the `QuadEval` package via the `CWSSPackage` operator `▷`.
Both packages are defined next to their CWSS theorems in the component files (`bridgePackage` in
`QuadEval/Bridge`, `quadEvalPackage` in `QuadEval/Soundness`); here they are only imported and
composed. The seam is definitional — the bridge's `relOut` *is* `QuadEval`'s `relIn` — so `▷`
discharges it by `rfl`. The chain's `isCWSS` field is `eval_coordinateWiseSpecialSound`; each
further §4.3 opening subprotocol is appended after this core, while §3 closes the recursion back
to the next invocation (see the module header). -/
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

* **Remaining §3/§4.3+/§4.5 subprotocols.** Append the §4.3 packages after `evalChain`, then route
  the final extension-field evaluation through §3 before the next iteration (or take a §4.5
  cutoff), as shown in the module header. Insert a zero-round `ReduceClaim` package when one
  `relOut` and the next `relIn` disagree in shape. Guarded subprotocols need a guarded variant of
  `▷`. Once the chain is long, migrate the binary `▷` to the n-ary
  `Verifier.seqCompose` + `seqCompose_coordinateWiseSpecialSound` (every factor is `IsPure`,
  `seqCompose_succ_eq_append` is `rfl`). -/

end ArkLib.Lattices.Ajtai.InnerOuter
