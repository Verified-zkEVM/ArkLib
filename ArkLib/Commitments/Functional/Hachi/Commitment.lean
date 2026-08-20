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
gadget-decompose it into the per-block messages/inner decompositions with the **canonical
*unsigned* base-`b` digit decomposition** `zmodDigitDecomposition` at the paper's width
`δ = ⌈log_b q⌉ = Nat.clog b q` (the `q ≤ bᵟ` obligation is `Nat.le_pow_clog`), and outer-commit
(`commitWithDecomps`). Deterministic; the decommitment is the `Decomp` data.

Its digits lie in `[0, b − 1]`, **not** in Eq. (20)'s balanced box `S_b`, so this committer supports
the ball-relaxed reading of `QuadEval` completeness only; the paper-exact reading needs
`commitBalanced`. -/
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

/-- **Honest commitment with *balanced* base-`b` digits** — the variant paper-exact `QuadEval`
completeness applies to.

Identical to `commit` except that both gadget steps use `balancedZmodDigitDecomposition` instead of
the unsigned `zmodDigitDecomposition`. The difference is not cosmetic: Eq. (20)'s range check is
the balanced-digit box `S_b`, which unsigned digits generally violate (a digit `b − 1` exceeds the
box's upper end `⌈b/2⌉ − 1` once `b ≥ 3`). So `commit` supports only the ball-relaxed reading of
`QuadEval` completeness, while `commitBalanced` supports the paper-exact one
(`mem_relInBox_of_commitBalanced`).

Both are honest and both reconstruct (`gadgetDecompose_lawful`), so `commit` is not wrong — it is
simply the decomposition whose digits live in `[0, b − 1]` rather than in `S_b`. The scheme value
`hachi` still uses `commit`; packaging the balanced committer into a `Commitment.Scheme` waits on
the `opening` field (see the `TODO` block). -/
def commitBalanced [DecidableEq (ZMod q)] (hb : 1 < b)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r)
      (Nat.clog b q) dRows)
    (p : CMlPolynomial (Rq 𝓜(q, α)) (r + m)) :
    Commitment 𝓜(q, α) outerRows ×
      Decomp 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) (2 ^ r) (Nat.clog b q) :=
  let decomps := generateDecomps 𝓜(q, α)
    (Decomposition.ofDigits 𝓜(q, α)
      (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q))
      (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q)))
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
tail's `computeY`). Everything else here is real.

⚠ The declared `pSpec` is **not** the full opening protocol's spec: `!p[] ++ₚ pSpec …` is the
*bridge ▷ QuadEval prefix* only (zero rounds, then Figure 3's commit/challenge round). The finished
opening additionally runs the §4.3 links — the `R^lin` adapter, the HMZ25 lift's `pSpecScalar`, the
`m₀ + m₁` zero-check rounds, the sumcheck rounds and the final evaluation — so this field's *type*
will change when the opening lands, not just its value. It is recorded here as the shape of the
prefix that exists today; see the `TODO` block. -/
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

/-! ## The honest commitment and the paper-exact input relation `relInBox`

Three separate notions, deliberately not merged:

* **weak-opening validity** — the committer's output is a `WeakBinding.VerifiedOpening`
  (`verifiedOpening_honestOpening`);
* **balanced-box membership** — its inner decomposition lies in Eq. (20)'s box `S_b`, a fact
  about *which* digit decomposition the committer was instantiated with
  (`vecInSb_honestInnerDecomp_balanced`, true for `commitBalanced`, false in general for `commit`);
* **evaluation consistency** — Eq. (15), a property of the polynomial layer, supplied by the caller.

`mem_relInBox_of_honestBalanced` combines them into `QuadEval`'s box-carrying input relation
`relInBox`, the input of paper-exact `QuadEval` completeness, and
`mem_relInBox_of_commitBalanced` restates it at the actual output of `commitBalanced` — so the
paper-exact link has a real committer to apply to. It does **not** apply to `hachi.commit`, which
uses the unsigned decomposition (only the ball-relaxed reading does).

This establishes that *input relation* only: the `opening` field of `hachi` is still `sorry`, so
nothing here claims end-to-end commitment correctness (`Commitment.perfectCorrectness`). -/

section HonestBalanced

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}

omit [NeZero q] in
/-- **The honest opening is a weak opening.** Every `WeakBinding.VerifiedOpening` field of
`InnerOuter.honestOpening` is discharged: the outer equation holds by construction
(`commitWithDecomps` *is* that commitment), the inner gadget relation is `generateDecomps_inner_eq`,
and the challenge fields are the trivial challenge's (`isUnit_one`, `‖1‖₁ ≤ κ`). The two remaining
fields are the weak verifier's norm side conditions, kept as the hypotheses `hβ` (per-block `ℓ₂²`
shortness of the message decomposition) and `hγ` (`ℓ∞` shortness of the flattened inner
decomposition) — exactly as in `perfectlyCorrect_of_lawful`, and discharged for balanced digits in
`mem_relInBox_of_honestBalanced`.

(It lives here rather than in `InnerOuter/Correctness.lean` because `VerifiedOpening` is defined in
`InnerOuter/Security.lean`, which imports that file.) -/
theorem verifiedOpening_honestOpening (base : ZMod q) (βSq γ κ : ℕ)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (hInnerDecomp : IsLawfulGadgetDecomposition Φ base decomp.inner)
    (hκle : ‖(1 : Rq Φ)‖₁ ≤ κ)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (msg : Message Φ messageRows blocks)
    (hβ : ∀ i, ‖(generateDecomps Φ decomp pp msg).message i‖₂² ≤ βSq)
    (hγ : vecLInftyNorm Φ
      (PolyVec.flattenBlocks (generateDecomps Φ decomp pp msg).innerDecomp) ≤ γ) :
    VerifiedOpening Φ base βSq γ κ pp
      (commitWithDecomps Φ pp (generateDecomps Φ decomp pp msg))
      (honestOpening Φ decomp pp msg) where
  outer_eq := rfl
  outer_short := hγ
  block i :=
    { unit := isUnit_one
      challenge_short := hκle
      scaled_short := by
        have hone : (honestOpening Φ decomp pp msg).challenge i •ᵥ
              (honestOpening Φ decomp pp msg).message i
            = (generateDecomps Φ decomp pp msg).message i := by
          funext j; simp [honestOpening]
        rw [hone]
        exact hβ i
      inner_eq := generateDecomps_inner_eq Φ base decomp hInnerDecomp pp msg i }

set_option linter.unusedSectionVars false in
/-- **The honest inner decomposition lies in Eq. (20)'s box `S_b`** when the committer is
instantiated with the *balanced* digits. Each block is `gadgetDecompose … (balanced …)` applied to
that block's inner commitment, so each of its coefficients is a balanced digit
(`gadgetDecompose_coeff_valMinAbs_mem_of_digit_mem` at `balancedZmodDigit_valMinAbs_mem`), and
`vecInSb_flattenBlocks` transports the box through the flattening. -/
theorem vecInSb_honestInnerDecomp_balanced {b : ℕ} (hb : 1 < b)
    (hqi : q ≤ b ^ innerDigits) (hbq : b ≤ q / 2)
    (ddMsg : DigitDecomposition (b : ZMod q) messageDigits)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (msg : Message Φ messageRows blocks) :
    vecInSb Φ b (PolyVec.flattenBlocks (generateDecomps Φ
      (Decomposition.ofDigits Φ ddMsg (balancedZmodDigitDecomposition b innerDigits hb hqi))
      pp msg).innerDecomp) :=
  vecInSb_flattenBlocks Φ _ fun _ j _ hk =>
    gadgetDecompose_coeff_valMinAbs_mem_of_digit_mem Φ _
      (fun c e => balancedZmodDigit_valMinAbs_mem hb hqi hbq c e) _ j hk

section RelInBox

variable {innerRows messageDigits outerRows innerDigits dRows m r : Nat}

set_option linter.unusedSectionVars false in
/-- **The honest balanced commitment establishes `relInBox`** — paper-exact `QuadEval`
completeness's input relation.

The three conjuncts come from the three separate places they belong:

* `VerifiedOpening` — `verifiedOpening_honestOpening`, with its two norm side conditions discharged
  here for the balanced digits: `ℓ₂²` shortness at `βSq = (2ᵐ·δ)·(deg φ)·⌊b/2⌋²`
  (`gadgetDecompose_vecL2NormSq_le_of_digit_le`) and `ℓ∞` shortness at `γ = ⌊b/2⌋`
  (`gadgetDecompose_vecLInftyNorm_le_of_digit_le`), both via `balancedZmodDigit_natAbs_le`. Note the
  balanced digits are short at *half* the unsigned radius, which is why `γ = ⌊b/2⌋` here where
  `perfectlyCorrect` has `b − 1`.
* Eq. (15) evaluation consistency — the hypothesis `heval`, supplied by the polynomial layer (it is
  `Hachi.splitForm_monomialBasis_eq_eval` at the statement's monomial bases; see
  `QuadEval/Bridge.lean`).
* Box membership — `vecInSb_honestInnerDecomp_balanced`, true because the committer was instantiated
  with `balancedZmodDigitDecomposition`.

Hypotheses: `hu` pins the statement's commitment to the honest one, `1 < b`, the two digit-count
conditions `q ≤ b^…`, the anti-wraparound `b ≤ q/2` (needed for balanced digits to be centered — see
`balancedZmodDigit_valMinAbs_mem`), `1 ≤ deg φ`, positive digit counts, and `1 ≤ κ`.

**Scope.** This establishes the input relation only. The `opening` field of `hachi` is still
`sorry`, so no claim is made about `Commitment.perfectCorrectness`. -/
theorem mem_relInBox_of_honestBalanced {b κ : ℕ} (hb : 1 < b)
    (hqm : q ≤ b ^ messageDigits) (hqi : q ≤ b ^ innerDigits) (hbq : b ≤ q / 2)
    (hdeg : 1 ≤ Φ.φ.natDegree) (hinner : 0 < innerDigits) (hκ : 1 ≤ κ)
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (msg : Message Φ (2 ^ m) (2 ^ r))
    (stmt : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (hu : stmt.u = commitWithDecomps Φ pp.toPublicParams (generateDecomps Φ
      (Decomposition.ofDigits Φ (balancedZmodDigitDecomposition b messageDigits hb hqm)
        (balancedZmodDigitDecomposition b innerDigits hb hqi)) pp.toPublicParams msg))
    (heval : evalConsistency Φ (b : ZMod q) stmt.avec stmt.bvec stmt.y
      (honestOpening Φ (Decomposition.ofDigits Φ
        (balancedZmodDigitDecomposition b messageDigits hb hqm)
        (balancedZmodDigitDecomposition b innerDigits hb hqi)) pp.toPublicParams msg)) :
    (stmt, honestOpening Φ (Decomposition.ofDigits Φ
        (balancedZmodDigitDecomposition b messageDigits hb hqm)
        (balancedZmodDigitDecomposition b innerDigits hb hqi)) pp.toPublicParams msg)
      ∈ relInBox Φ pp (b : ZMod q)
        ((2 ^ m) * messageDigits * (Φ.φ.natDegree * (b / 2) ^ 2)) (b / 2) κ b := by
  -- The honest committer's decomposition pair, named so the goals below stay readable.
  set ddM := balancedZmodDigitDecomposition b messageDigits hb hqm with hddM
  set ddI := balancedZmodDigitDecomposition b innerDigits hb hqi with hddI
  -- `ℓ₂²` shortness of each message block: it *is* a `gadgetDecompose` at `ddM`.
  have hβ : ∀ i, ‖(generateDecomps Φ (Decomposition.ofDigits Φ ddM ddI)
      pp.toPublicParams msg).message i‖₂²
      ≤ (2 ^ m) * messageDigits * (Φ.φ.natDegree * (b / 2) ^ 2) := by
    intro i
    change ‖gadgetDecompose Φ ddM (msg i)‖₂² ≤ _
    exact gadgetDecompose_vecL2NormSq_le_of_digit_le Φ ddM
      (fun c e => balancedZmodDigit_natAbs_le hb hqm hbq c e) (msg i)
  -- `ℓ∞` shortness of the flattened inner decomposition, block by block.
  have hγ : vecLInftyNorm Φ (PolyVec.flattenBlocks (generateDecomps Φ
      (Decomposition.ofDigits Φ ddM ddI) pp.toPublicParams msg).innerDecomp) ≤ b / 2 := by
    refine vecLInftyNorm_flattenBlocks_le Φ _ fun i => ?_
    change vecLInftyNorm Φ (gadgetDecompose Φ ddI _) ≤ b / 2
    exact gadgetDecompose_vecLInftyNorm_le_of_digit_le Φ ddI
      (fun c e => balancedZmodDigit_natAbs_le hb hqi hbq c e) _
  have hκle : ‖(1 : Rq Φ)‖₁ ≤ κ := by rw [Rq.l1Norm_one Φ hdeg]; exact hκ
  refine ⟨⟨?_, heval⟩, vecInSb_honestInnerDecomp_balanced Φ hb hqi hbq _ pp.toPublicParams msg⟩
  rw [hu]
  exact verifiedOpening_honestOpening Φ (b : ZMod q) _ _ κ (Decomposition.ofDigits Φ ddM ddI)
    (gadgetDecompose_lawful Φ hinner hdeg ddI) hκle pp.toPublicParams msg hβ hγ

end RelInBox

end HonestBalanced

end FunctionalCommitment

/-! ## The balanced committer and paper-exact `QuadEval` -/

section CommitBalancedRelInBox

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α : ℕ}
variable {innerRows outerRows dRows m r : Nat} (b : ℕ)

set_option linter.unusedSectionVars false in
/-- `commitBalanced`'s commitment is the outer commitment of its own decompositions. Holds by
`rfl`; recorded so the `relInBox` corollary can be stated against the committer's output rather than
against a re-spelled `commitWithDecomps` term. -/
theorem commitBalanced_fst (hb : 1 < b)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r)
      (Nat.clog b q) dRows)
    (p : CMlPolynomial (Rq 𝓜(q, α)) (r + m)) :
    (commitBalanced b hb pp p).1 = commitWithDecomps 𝓜(q, α) pp.toPublicParams
      (generateDecomps 𝓜(q, α) (Decomposition.ofDigits 𝓜(q, α)
        (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q))
        (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q)))
        pp.toPublicParams (Hachi.toMatrix p)) :=
  rfl

set_option linter.unusedSectionVars false in
/-- `commitBalanced`'s decommitment is its honest decomposition data. Holds by `rfl`. -/
theorem commitBalanced_snd (hb : 1 < b)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r)
      (Nat.clog b q) dRows)
    (p : CMlPolynomial (Rq 𝓜(q, α)) (r + m)) :
    (commitBalanced b hb pp p).2 = generateDecomps 𝓜(q, α) (Decomposition.ofDigits 𝓜(q, α)
      (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q))
      (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q)))
      pp.toPublicParams (Hachi.toMatrix p) :=
  rfl

-- NB: these three results deliberately take **no** `[DecidableEq (ZMod q)]` binder, so that the
-- canonical `ZMod.decidableEq` is used in `Decomposition.ofDigits`. With a local instance binder
-- the committer's decomposition and the generic lemma's carry *different* `DecidableEq` instances,
-- and unifying them is not just slow but impossible — the symptom is a diverging `whnf`.
set_option linter.unusedSectionVars false in
/-- **`commitBalanced` establishes paper-exact `QuadEval`'s input relation `relInBox`.**
`mem_relInBox_of_honestBalanced` at the actual output of the balanced committer: the statement's
commitment is `(commitBalanced …).1` and the witness is the honest opening over
`(commitBalanced …).2`, so the paper-exact completeness theorem
(`quadEvalReduction_perfectCompleteness_balancedDigits`) now has a real committer to apply to.

What still has to be supplied is `heval`, Eq. (15) evaluation consistency of the committed
polynomial against the statement's bases — the polynomial layer's obligation, not the committer's.

**Scope, precisely.** `hachi`'s `commit` field uses the *unsigned* decomposition, so this does not
apply to `hachi` as packaged; and `hachi.opening` is still `sorry`, so nothing here is a claim about
`Commitment.perfectCorrectness`. What is established is the input relation of the paper-exact
`QuadEval` link, for the balanced committer. -/
theorem mem_relInBox_of_commitBalanced {κ : ℕ} (hb : 1 < b)
    (hbq : b ≤ q / 2) (hdeg : 1 ≤ 𝓜(q, α).φ.natDegree) (hclog : 0 < Nat.clog b q) (hκ : 1 ≤ κ)
    (pp : Hachi.PublicParamsD 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r)
      (Nat.clog b q) dRows)
    (p : CMlPolynomial (Rq 𝓜(q, α)) (r + m))
    (stmt : QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) (Nat.clog b q) outerRows (2 ^ r)
      (Nat.clog b q) dRows)
    (hu : stmt.u = (commitBalanced b hb pp p).1)
    (heval : evalConsistency 𝓜(q, α) (b : ZMod q) stmt.avec stmt.bvec stmt.y
      (honestOpening 𝓜(q, α) (Decomposition.ofDigits 𝓜(q, α)
        (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q))
        (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q)))
        pp.toPublicParams (Hachi.toMatrix p))) :
    (stmt, honestOpening 𝓜(q, α) (Decomposition.ofDigits 𝓜(q, α)
        (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q))
        (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q)))
        pp.toPublicParams (Hachi.toMatrix p))
      ∈ relInBox 𝓜(q, α) pp (b : ZMod q)
        ((2 ^ m) * Nat.clog b q * (𝓜(q, α).φ.natDegree * (b / 2) ^ 2)) (b / 2) κ b := by
  have hu' : stmt.u = commitWithDecomps 𝓜(q, α) pp.toPublicParams
      (generateDecomps 𝓜(q, α) (Decomposition.ofDigits 𝓜(q, α)
        (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q))
        (balancedZmodDigitDecomposition b (Nat.clog b q) hb (Nat.le_pow_clog hb q)))
        pp.toPublicParams (Hachi.toMatrix p)) :=
    hu.trans (commitBalanced_fst b hb pp p)
  -- `heval` is discharged against the *instantiated* goal: passing it positionally makes the
  -- unifier compare two copies of the `Rq 𝓜(q,α)` instance tower and blow up.
  exact mem_relInBox_of_honestBalanced 𝓜(q, α) hb (Nat.le_pow_clog hb q) (Nat.le_pow_clog hb q)
    hbq hdeg hclog hκ pp (Hachi.toMatrix p) stmt hu' heval

end CommitBalancedRelInBox

/-! ## TODO — completeness / honest-prover layer

The `opening` field of `hachi` is provisional (`sorry`). Materializing it needs, in order:

1. **the honest-prover layer for the links that still lack one.** `QuadEval` has it
   (`honestComputeV` / `honestComputeResp`, from `QuadEval.Gadgets`' `carrierCommit` / `zDecomp`),
   as do the `R^lin` adapter, the HMZ25 lift, the batching bridge and the nested zero-check — each
   with a completeness proof. Still open:
   * the sumcheck loop's `computeG` (`Sumcheck/Rounds.lean`), the honest round-polynomial pair. This
     one needs new infrastructure first: a *computable* `CPolynomial`-valued partial sum in the free
     coordinate, plus its agreement lemma against the proof-side `roundPoly`
     (`Sumcheck/RoundPoly.lean`, Computability section);
   * the final-evaluation and partial-evaluation tails' `computeY`;
2. **composition of those reductions**, blocked on the generic `Reduction.append_completeness`
   (`OracleReduction/Composition/Sequential/Append.lean`) and `liftContext_completeness`
   (`OracleReduction/LiftContext/Reduction.lean`), both still `sorry`. `HonestChain.lean` appends
   the finished prefix (`completePrefixReduction`) and proves its completeness modulo exactly those
   lemmas;
3. widening this scheme's `pSpec` from the bridge ▷ QuadEval prefix to the full opening spec;
4. only then `Commitment.perfectCorrectness` for `hachi` — and a decision on whether the packaged
   `commit` should switch to `commitBalanced`, which is what the paper-exact `QuadEval` relation
   needs. -/

end ArkLib.Lattices.Ajtai.InnerOuter
