/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval.Basic
import ArkLib.Commitments.Functional.Basic

/-!
# Hachi as a Functional Commitment

Hachi [NOZ26] as a `Commitment.Scheme` (`ArkLib.Commitments.Functional.Basic`) over the multilinear
data `CMlPolynomial (Rq 𝓜(q,α)) (r + m)` — an `(r + m)`-variable multilinear polynomial with
coefficients in the power-of-two cyclotomic ring `Rq 𝓜(q,α) = (ZMod q)[X] / (X^{2^α} + 1)`. This
file supplies what the generic interface asks of a functional commitment: the multilinear
eval-oracle interface (`multilinearEvalOracleInterface`), honest key generation and commitment
(`keygen` / `commit`, using the canonical base-`b` gadget decomposition `zmodDigitDecomposition` at
the paper's width `δ = ⌈log_b q⌉ = Nat.clog b q`, Hachi §2.1/§4.1), and the `hachi` scheme itself.

The eval-oracle interface and the honest committer operations are real; the opening `Proof` is
deferred (`sorry`, see the `TODO`). The coordinate-wise-special-sound (CWSS) composition the
finished opening will run over lives in the sibling `Composition.lean`
(`evalChain` / `eval_coordinateWiseSpecialSoundWithEscape`).

## Main definitions

* `multilinearEvalOracleInterface`: the `OracleInterface` letting a committed polynomial be
  queried at an evaluation point, returning its value there — the `Data` of the commitment.
* `keygen`: honest key generation — sample the inner/outer/short Ajtai matrices `(A, B, D)`
  uniformly; the resulting `PublicParamsD` serves as both committer and verifier key.
* `commit`: honest commitment — reshape the polynomial into its `2^r × 2^m` coefficient matrix,
  gadget-decompose it, and outer-commit; the decommitment is the `Decomp` data. Deterministic.
* `hachi`: the `Commitment.Scheme` value packaging the above; its `opening` field is a documented
  `sorry` pending the honest-prover / completeness layer (see the `TODO` block).

Same namespace/opens discipline as the rest of the Hachi tree
(`namespace ArkLib.Lattices.Ajtai.InnerOuter`, `open WeakBinding`).

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.SingleRound

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

/-- **Hachi as a functional commitment** (`Commitment.Scheme`) — ⚠ **WIP scaffold.** The eval
oracle and the honest `keygen` / `commit` are real, but the `opening` field is a placeholder
(`sorry`, see below and the `TODO` block), so this value does **not** yet certify end-to-end
opening correctness. It is committed now only as the target packaging the finished opening will
slot into once the honest-prover layer lands (the follow-up tracked by the `TODO` here and in
`Composition.lean`; the §4.3 soundness chain it will run over is finished — rows 1–9 of that file's
seam table).

Over the multilinear data `CMlPolynomial (Rq 𝓜(q,α)) (r + m)` — an `(r + m)`-variable polynomial,
with the `r`/`m` split feeding the outer/inner gadgets. It commits a polynomial directly (no
caller-supplied decompositions): the honest `commit` uses the canonical base-`b` gadget
decomposition at the paper's width `δ = ⌈log_b q⌉ = Nat.clog b q` (Hachi [NOZ26] §2.1/§4.1), shared
by the message and inner gadgets — so `messageDigits`/`innerDigits` are not free parameters. The
only parameters are the gadget base `b` and `1 < b`; the scheme carries the eval oracle
`multilinearEvalOracleInterface`, honest `keygen` / `commit`, committer and verifier key
`PublicParamsD`, and decommitment `Decomp`.

The `opening` field — the complete opening `Proof` (a `Reduction … Bool Unit`) — is **provisional**
(`sorry`): its boolean verdict is Hachi Eq. (20) membership (`relOut`), which depends on the never-
sent triple `(ŵ, t̂, ẑ)`; it becomes verifier-computable only once the honest-prover layer is
formalized (`QuadEval.prover`'s `computeV`/`computeResp`, the sumcheck loop's `computeG`, the
tail's `computeY`). Everything else here is real. The stated `pSpec` is the composed evaluation
protocol spec (`!p[] ++ₚ pSpec …`), i.e. the shape the finished opening will run over — see the
`TODO` block. -/
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

/-! ## TODO — completeness / honest-prover layer

The `opening` field of `hachi` is provisional (`sorry`). Materializing it needs the honest-prover
layer, which is open for every link of the chain:

* `QuadEval.prover`'s `computeV` / `computeResp`, from the `QuadEval.Gadgets`
  carrier/decomposition definitions (`carrierCommit`, `zDecomp`);
* the sumcheck loop's `computeG` (`Sumcheck/Rounds.lean`) — the honest round-polynomial pair. This
  one needs new infrastructure first: a *computable* `CPolynomial`-valued partial sum in the free
  coordinate, plus its agreement lemma against the proof-side `roundPoly`
  (`Sumcheck/RoundPoly.lean`, Computability section);
* the final-evaluation and partial-evaluation tails' `computeY`;

and then a completeness/forward direction at each seam, discharging
`Commitment.perfectCorrectness` for `hachi`. -/

end ArkLib.Lattices.Ajtai.InnerOuter
