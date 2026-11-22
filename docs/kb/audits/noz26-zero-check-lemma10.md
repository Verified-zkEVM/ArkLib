# NOZ26 Figure 5 / Lemma 10 audit

This page records the specification boundary for link 6 of ArkLib's Hachi opening chain. It is
based on the January 30, 2026 ePrint version of Nguyen–O'Rourke–Zhang, *Hachi: Efficient
Lattice-Based Multilinear Polynomial Commitments over Extension Fields* (`NOZ26`, §4.3,
Figure 5 and Lemma 10).

## Knowledge-error reference and scope

FMN24 Lemma 2.31 in the checked ePrint 2023/846, p.29, gives
`μ·ℓ·(k−1)/|S|`. NOZ26 Lemma 4 (January 30 version, p.10), while invoking FMN24 §7, prints
`∑ᵢ ℓᵢ·kᵢ/|Sᵢ|^{ℓᵢ}`. These are different bounds. Under the intended standard FMN-style CWSS
**accepting-tree** interpretation, the latter cannot be used as a general knowledge bound:
set `μ=1`, `ℓ=2`, `k=2`, take `S` a finite field and an empty relation over a singleton witness
carrier, and accept exactly when `c₁=0` for a uniform challenge in `S²`. No accepting
`SS(S,2,2)` family exists, since its first-coordinate sibling
must differ there, so the structured-tree extraction premise is vacuous. Cheating succeeds with
probability `1/|S|`, greater than the printed `4/|S|²` when `|S|>4`. This concerns that intended
reading; the displayed multi-round definitions omit the explicit accepting-leaf qualification,
which is explicit in FMN24's Sigma definition and §7.2. It is not a refutation under an
unconditional all-tree extraction interpretation. This is a discrepancy in the generic restatement,
not evidence that the Hachi scheme is insecure; protocol-specific bounds need their own analysis.

For ArkLib's split scalar rounds, put `μ=m₀+m₁`, `ℓ=1`, `k=2` in FMN24's numeric term. The
resulting **candidate** is `(m₀+m₁)/|F_{q^k}|`, matching the Schwartz–Zippel term numerically.
ArkLib's public theorem is CWSS **with escape**, not FMN24's plain knowledge conclusion. The
missing bridge must acquire a suitable tree, bound its actual `2^μ` leaves and execution costs,
and efficiently produce/reduce any escape. In particular the printed FMN growth expression
`(ℓ(k−1))^μ` is constant in this binary case and cannot by itself bound `2^μ`; see
[FMN24's version note](../papers/FMN24.md#version-notes). No knowledge-error, tree-acquisition or
efficiency theorem follows automatically from the existing deterministic tree theorem.

Last revalidated against the formalization: **18 August 2026** (declaration names and the shortness
section re-checked against the tree; every `#print axioms` claim below re-run).

> **Status (integrated; links 5, 6 and 7 all certified in both directions).**
> The corrected Lemma 10 is
> formalized *inside* the escape-threaded opening chain: `nestedZeroCheckPackage` reduces
> `relBatched → relNestedZeroCheck` and is composed as
> `batchPackage ▷ nestedZeroCheckPackage ▷ nestedSumcheckBridgePackage` in `Composition.lean`
> (inside `iteration`). The CWSS theorem `nestedZeroCheck_coordinateWiseSpecialSoundWithEscape` is
> **`sorry`-free and axiom-clean** (the `H_α`/`H₀` values used by the theorem are concrete), and
> the link-5 batching bridge's
> un-batching pull-back `mem_relLift_of_relBatched` is likewise **proven and axiom-clean relative
> to those definitions**. **Paper Eq. (22) is now formalized**: `mAlphaTilde` (`M̃_α`),
> `alphaTilde` (`α̃`) and `alphaContract` build the paper's public contraction against the committed
> table, and `alphaDefect_wTable` / `hAlpha_eq_zero_iff_alphaDefect` prove it equal to the per-row
> defect that `hAlphaEvals` writes down directly (axiom-clean).
>
> **Link 6's honest direction is now closed too.** `nestedZeroCheckReduction_perfectCompleteness`
> (`ZeroCheck/Completeness.lean`) proves perfect completeness of the scalar-round link relative
> to `relBatched`,
> `sorry`-free and axiom-clean. The completeness error is exactly zero, because `relBatched`
> asserts the polynomial identities and so both polynomials vanish wherever the challenges happen
> to land; nothing about the challenge distribution is used. So link 6 is now certified in both
> directions — and so is link 5: its forward theorem `relLift → relBatched` is
> `mem_relBatched_of_relLift` (`ZeroCheck/Batch.lean`), packaged as
> `batchReduction_perfectCompleteness` (`ZeroCheck/Completeness.lean`, through
> `ReduceClaim.reduction_completeness_of_imp`). The appended honest chain in `HonestChain.lean`
> uses proved composition with pure verifiers and suffix completeness from every shared state;
> its completeness has only standard axiom dependencies.
> Downstream, the link-7 sumcheck-bridge pull-back `mem_relNestedZeroCheck_of_nestedRoundRel`
> and the two sum identities `sum_sumcheckPolyZero` / `sum_sumcheckPolyAlpha` it rests on are now
> proved and axiom-clean, and the bridge is settled in the honest direction too
> (`mem_nestedRoundRel_of_relNestedZeroCheck`,
> `nestedSumcheckBridgeReduction_perfectCompleteness`).
> **The range half is now load-bearing:** shortness (`liftShort`) is *derived* from the range
> identity `H₀ ≡ 0` at the batching bridge (`hZero_eq_zero_imp_liftShort`),
> not carried as a free conjunct of `relBatched`.
>
> **The point seams carry `liftShort`, as the commitment's shortness index.**
> `relNestedZeroCheck` and `nestedRoundRel` each state it alongside `t = Com(w̃)` and the two point
> evaluations. `LiftCom` is the generic `CoordinateWise.BindingCommitment W Short` — fields `TCom`
> and `com` only — instantiated at `Short := liftShort Φ bound bDig`, and its `Collision` set
> requires both colliding openings to be short. This gives the abstract collision event
> `nestedZeroCheckEsc`; a Module-SIS conclusion additionally requires a concrete commitment
> instantiation and collision reduction. `LiftCom` assumes no binding property, and `relBatched`
> has no shortness conjunct. See "Shortness: two different notions, and where each one sits" below.
>
> All declarations live in the chain's namespace
> `ArkLib.Lattices.Ajtai.InnerOuter` (`Hachi/ZeroCheck/{Constraints,Batch,Reduction}.lean`); the
> transcript tree is ArkLib's generic `ChallengeTree`; its polynomial zero test is implemented for
> CompPoly in `ToCompPoly/Multilinear/NestedEvaluationTree.lean`.

## Paper claim

Figure 5 samples two uniform vector challenges `τ₀` and `τ₁`, receives a table `w̃`, checks
`t = Com(w̃)`, reconstructs the batched polynomials from Equations (22)–(23), and checks
`H₀(τ₀) = 0` and `Hα(τ₁) = 0`. Lemma 10 claims that a coordinate-wise special-sound family either
yields one opening satisfying both polynomial identities or breaks commitment binding. Remark 2
says the final instantiation should use the inner-outer commitment's weak binding from Lemma 7.

## Paper-to-Lean ledger

| Paper object or claim | Lean declaration | Status | Concern |
| --- | --- | --- | --- |
| Batched range identity, Eq. (23) | `ZeroCheck.hZero : CMlPolynomialEval F m₀` | represented, **concrete, computable, load-bearing** | The stored vector is exactly the Boolean table of range factors; multilinearity is structural. Entry content `wTable` reads the coefficients of the committed vector — the `z` block directly, the quotient block as its base-`b` digits — and `H₀ ≡ 0 ⇒ liftShort` is proven by `hZero_eq_zero_imp_liftShort`. Its soundness content is the `z` block: the digit rows are in range by construction, and the bound they would have carried is supplied by `rhoDigits_valMinAbs_natAbs_le` at radius `⌊b/2⌋` rather than `q/2`. See the constraint-encoding bullet in the conclusions for why that is a strengthening, not a loss. |
| Batched row identity, Eq. (22) | `ZeroCheck.hAlpha : CMlPolynomialEval F m₁` | represented, **concrete, computable, paper-faithful** | The stored vector is the per-row defect table `hAlphaEvals`, so multilinearity and the pull-back are structural. The paper's route through the `M̃_α`/`w̃`/`α̃` contraction is built separately (`mAlphaTilde`, `alphaTilde`, `alphaContract`, `alphaDefect`) and proved equal to that table by `alphaDefect_wTable`, with the relation-level form `hAlpha_eq_zero_iff_alphaDefect`. |
| Eq. (22) contraction ↔ row defect | `ZeroCheck.alphaDefect_wTable`, `hAlphaEvals_eq_alphaDefect`, `hAlpha_eq_zero_iff_alphaDefect` | proven, **axiom-clean** | §4.3's "represent the constraints by polynomials" step: the only place the table encoding of the witness (commitment/sumcheck side) meets the ring encoding (`relLift` side). Arity pins `hd : 0 < deg φ` and `(μ+n·δ)·deg φ ≤ 2^{m₀}`; the `Rq` column bound is `CyclotomicModulus.natDegree_lt_of_reduced`. |
| Figure-5 point checks | `ZeroCheck.relNestedZeroCheck` | deliberately repaired | Points are assembled directly from `m₀ + m₁` scalar challenge rounds; evaluation uses `CMlPolynomialEval.eval` directly. Also carries `liftShort` as the commitment's shortness index (see "Shortness" below); the weak-binding case is the separate escape event `nestedZeroCheckEsc`, not a conjunct of the relation. |
| Axis-cross counterexample | `MvPolynomial.exists_nonzero_vanishing_on_axis_cross` | proven | Refutes the identity-testing step for the *prose* reading of Lemma 10 (a star of scalar coordinates). |
| Nested zero-test kernel | `NestedEvaluationTree.eq_zero_of_vanishes_comp` (computable view `CMlPolynomialEval.eq_zero_of_polynomialVanishes_comp`/`_castAdd`/`_natAdd`; Hachi wrappers `hZero_eq_zero_of_evaluationTree`, `hAlpha_eq_zero_of_evaluationTree`) | proven, **axiom-clean** | A sibling-distinct complete `k`-ary tree with vanishing leaves forces a polynomial of individual degree `< k` to be zero, *read through a window of consecutive levels*. Mathlib-level statement in `ArkLib/Data/MvPolynomial/NestedEvaluationTree.lean`, computable view in `ArkLib/ToCompPoly/Multilinear/NestedEvaluationTree.lean`. Stated for general `k` (not just the multilinear `k = 2`), but with **one arity for every level**: a uniformly wider tree can certify a multilinear polynomial, whereas mixing a `k = 2` round with Lemma 9's `2d` or Lemma 11's `deg H + 1` would need per-level arity. |
| Transcript-tree size | `NestedEvaluationTree.numLeaves_eq_pow`, `nestedZeroCheck_numLeaves`, `nestedZeroCheck_numLeaves_lt` | proven, **axiom-clean**; two unformalized steps | `k ^ n` leaves, and `< 4·A·B` at minimal arities. `CWSSStructure` carries no size bound. These separate lemmas have two scope limits: (i) these count the *adapter's* `NestedEvaluationTree`, not the `ChallengeTree.LeafPath`s the extractor consumes, and (ii) minimality of `m₀`, `m₁` is a hypothesis of `_lt`, not enforced — `hμn`/`hn` bound the arities from below only. |
| Lemma-10 extraction (escape-threaded) | `ZeroCheck.nestedZeroCheckExtractor`, `nestedAssembly_escape_or_mem_relBatched` | proof-sorry-free | Escape pass-through ∨ weak-binding collision ∨ common opening with both identities zero. |
| Lemma-10 binding alternative | `ZeroCheck.nestedZeroCheckEsc` via `LiftCom.Collision` | integrated | Two **distinct short** openings of the shared `t` form a member of the abstract `K.Collision`. Stated as a `ChallengeTree.EscapeEvent` on `(statement, tree)` rather than an extractor output, so it cannot be satisfied trivially; the shortness both openings need is supplied by `relNestedZeroCheck`'s own `liftShort` conjunct. The concrete instantiation is `hachiLiftCom` (`RingSwitch/Reduction.lean`), the Ajtai product `D · (z ‖ digits(ρ))`, and `moduleSIS_relation_of_mem_Collision` proves its collision set satisfies `ModuleSIS.relation` at radius `2·bound`; what is still open is tying `D` to the inner-outer commitment's own key — see the note at the end of "Shortness" below. |
| Corrected Lemma 10 CWSS | `ZeroCheck.nestedZeroCheck_coordinateWiseSpecialSoundWithEscape` | sorry-free, **axiom-clean** | `m₀ + m₁` scalar rounds with `k = 2`; the structured transcript tree is converted to **one** evaluation tree of depth `m₀ + m₁`, with `H₀` read through its first `m₀` levels (`Fin.castAdd`) and `H_α` through its last `m₁` (`Fin.natAdd`); `#print axioms` = `propext`/`Classical.choice`/`Quot.sound` only. |
| Knowledge-error bridge (FMN24 Lemma 2.31; printed NOZ26 Lemma 4 differs) | no declaration | **missing (repo-wide)** | The scalar-round numeric candidate is `(m₀+m₁)/|F_{q^k}|`. The source discrepancy and missing acquisition, actual leaf-growth, escape and efficiency obligations are recorded above; this is not a formal ArkLib knowledge bound. |
| Honest completeness of this link | `ZeroCheck.nestedZeroCheckReduction_perfectCompleteness` | proven, **axiom-clean** | Full `Reduction.perfectCompleteness`, for arbitrary `oSpec`/`init`/`impl`. Two halves: `mem_relNestedZeroCheck_of_relBatched` is the algebra (`eval 0 = 0` at *arbitrary* points, hence zero error), and `nestedZeroCheckReduction_run_support` is the execution — an honest run cannot fail, and prover and verifier emit the same statement because both apply the same `castAdd`/`natAdd` split to the same transcript. The execution proof uses the generic `Reduction.perfectCompleteness_of_run_support` (`OracleReduction/Security/Basic.lean`). |
| Link-5 un-batching pull-back | `ZeroCheck.mem_relLift_of_relBatched` (`batchPackage`) | **the theorem is proven and axiom-clean; paper correspondence is partial** | `relBatched → relLift`; `H_α ≡ 0 ⇒` per-row eqs via `hAlpha_eq_zero_iff` + `hAlphaEvals_rowPoint` (arity pin `n ≤ 2 ^ m₁`); **`H₀ ≡ 0 ⇒ liftShort`** via `hZero_eq_zero_imp_liftShort` (arity pin `(μ+n·δ)·deg φ ≤ 2^{m₀}`, `hd`, range-base fit `b−1 ≤ γ`, and digit-base admissibility `DigitBaseOk q γ bDig` — the quotient half is free, the committed digits being `⌊bDig/2⌋`-bounded for every quotient). The obligation to derive the `H_α` table from paper Eq. (22) is discharged separately by `alphaDefect_wTable`. The forward/honest-completeness direction is the row below. |
| Link-5 forward/completeness direction | `ZeroCheck.mem_relBatched_of_relLift`; `ZeroCheck.batchReduction_perfectCompleteness` | proven, **axiom-clean** | An honest `relLift` witness satisfies `relBatched`: `hZero_eq_zero_of_liftShort` puts every table entry among `P_b`'s roots, and `hAlpha_eq_zero_of_rows` covers the whole Boolean table (zero-padded beyond row `n`). It needs neither arity hypothesis and nothing about `α`, but the range-base fit in the **opposite** orientation (`bound ≤ b − 1`) together with `DigitBaseOk q (b−1) b` — so a single two-sided parameterization is pinned to the paper's `bound = b − 1`, at which `γ = bZero − 1 = O(b)` rather than `q/2`. `batchReduction` is the link as a protocol object (verifier shared with `batchPackage` by `rfl`); its completeness uses this direction alone, via `ReduceClaim.reduction_completeness_of_imp`. |
| Link-5/link-6/link-7 composition | `batchPackage ▷ nestedZeroCheckPackage ▷ nestedSumcheckBridgePackage` (inside `iteration`) | **defined, compiles as a CWSS chain** | The seam relations match by `rfl`. This is the *soundness* composition; it does not close link 5's paper-encoding obligation. The honest counterpart in `HonestChain.lean` composes the three links with pure verifiers and state-uniform suffix completeness, and has only standard axiom dependencies. |

## Polynomial representation: multilinear value vectors and proof views

The two batched identities now use CompPoly's native Boolean-evaluation representation
`CMlPolynomialEval F m = Vector F (2 ^ m)`. This matches Eqs. (22)–(23): each entry is one
Boolean-cube constraint value, and the vector represents its unique multilinear extension.
Multilinearity is therefore guaranteed by the type rather than proved with `degreeOf` lemmas.

The derived Mathlib views `hZeroML` and `hAlphaML` rebuild the same value tables with
`MvPolynomial.MLE` and are used only in algebraic proofs (the nested-tree zero test crosses to
Mathlib internally); `hZero_eval_eq` / `hAlpha_eval_eq` bridge pointwise evaluations between the
two representations.

| Object | Computable definition | Mathlib view | Bridge lemma |
| --- | --- | --- | --- |
| Witness ring | `Rq Φ = {p : CPolynomial (ZMod q) // Φ.reduce p = p}` | `Φ.CyclotomicRing` | `Rq.toQuotient` |
| Quotients `rᵢ` | `LiftedWitness.r : Fin n → CPolynomial (ZMod q)` | `(r i).toPoly` | `CPolynomial.coeff_toPoly` |
| Row sum `∑ⱼ Mᵢⱼzⱼ` | `cRowSum` | `rowSum` | `rowSum_eq_sum_toPoly` |
| Evaluation at `α` | `cEvalAt` (`CPolynomial.eval₂`) | `evalAt` (`eval₂RingHom`) | `cEvalAt_cRowSum_eq_evalAt`, `cEvalAt_eq_evalAt_toPoly` |
| Range factor `P_b` | `rangeProduct` (scalar) | — | `rangeProduct_eq_zero_iff` |
| Table `w̃`, Eq. (21) | `wTable` | — | `wTable_zRow`, `wTable_rRow` |
| `H₀`, Eq. (23) | `hZero : CMlPolynomialEval F m₀` | `hZeroML` | `hZero_eq_zero_iff`, `hZero_eval_eq` |
| `H_α`, Eq. (22) | `hAlpha : CMlPolynomialEval F m₁` | `hAlphaML` | `hAlpha_eq_zero_iff`, `hAlpha_eval_eq` |
| Public matrix `M̃_α`, power vector `α̃` | `mAlphaTilde`, `alphaTilde` | — | `alphaDefect_wTable` (contraction = row defect), `hAlpha_eq_zero_iff_alphaDefect` |
| `mle[w̃]` and its opening | `cWTableMle`, `wTableMleEval` | — | `wTableMleEval_eq` |
| Sumcheck summands `F_{0,τ₀}`, `F_{α,τ₁}` | `sumcheckPolyZero`, `sumcheckPolyAlpha` (via `cEqualityPolynomial`, `cRangeProduct`, `cMultilinearExtension`, `alphaPublicEvals`) | `hZeroML`/`hAlphaML` in the sum identities | `sum_sumcheckPolyZero`, `sum_sumcheckPolyAlpha` (**both proven, axiom-clean**) |
| Round message `(g⁽⁰⁾, g⁽ᵅ⁾)` | `CPolynomial.degreeLE` subtypes | `Polynomial.degreeLE` | `CPolynomial.degreeLE_toPoly` |

Consequences worth recording:

- **The full identities are computable vector equalities.** `relBatched` states
  `hZero … = 0 ∧ hAlpha … = 0`; both sides are fixed-length CompPoly vectors, not sparse
  `Finsupp` polynomials.
- **The Mathlib views are proof-only.** `hZeroML`/`hAlphaML` are noncomputable derived definitions
  used inside algebraic proofs and in the sumcheck identity specifications. `relNestedZeroCheck`
  evaluates the primary vectors directly; `hZero_eval_eq`/`hAlpha_eval_eq` cross to the Mathlib
  views where needed, while their zero identities remain equivalent to the primary vector
  identities.
- **The sumcheck summands are concrete and their sum identities are proved.** The
  definitions `sumcheckPolyZero` (`F_{0,τ₀} = eq̃(τ₀, ·) · P_b(mle[w̃])`, per-variable degree
  `2b = roundDegZero b`), `sumcheckPolyAlpha` (the paper's
  `F_{α,τ₁} = mle[w̃] · mle[α̃(·) · ∑ᵢ eq̃(τ₁, i)·M̃_α(i, ·)]`, per-variable degree
  `2 = roundDegAlpha`), the public target `zcTargetAlpha = ∑ᵢ eq̃(τ₁, i)·yᵢ(α)` and the prover
  fold `hypercubeSum` all have concrete computable bodies (via `cEqualityPolynomial`,
  `cRangeProduct`, `cMultilinearExtension`, `alphaPublicEvals`). The two full-cube sum identities
  `sum_sumcheckPolyZero` (`∑ F_{0,τ₀} = H₀(τ₀)`) and `sum_sumcheckPolyAlpha`
  (`∑ F_{α,τ₁} = H_α(τ₁) + zcTargetAlpha`) are **proven and axiom-clean**; the latter runs the
  `M̃_α` contraction over the `n·δ` digit columns and closes it with `rhoDigits_evalAt`. The
  sumcheck bridge's pull-back invokes exactly these two and is therefore axiom-clean as well.
- **`sumcheckPolyAlpha` is summed over the witness cube.** Its `m₀` coordinates index the
  entries of `w̃`. The row index `i ∈ [n]` is summed internally in
  `∑ᵢ eq̃(τ₁, i) · M̃_α(i,x)`; the weighting point `τ₁` has `m₁` coordinates. The proved
  `sum_sumcheckPolyAlpha` identity gives the full witness-cube sum as
  `H_α(τ₁) + zcTargetAlpha`. The existing pins `n ≤ 2^{m₁}` and
  `(μ+n·δ)·deg φ ≤ 2^{m₀}` bound the row and witness-table embeddings respectively.

## Uniform-vector challenge gap (why the repair is needed)

This CWSS proof gap does not establish an attack on Figure 5. For a fixed nonzero polynomial
`H₀` of total degree at most `m₀`, chosen before an independent uniform point `τ₀`,
Schwartz–Zippel gives `Pr[H₀(τ₀) = 0] ≤ m₀/|F_{q^k}|`. The analogous estimate holds for a fixed
nonzero `H_α` of degree at most `m₁` before its own independent uniform point. Their sum
`(m₀ + m₁)/|F_{q^k}|` is only a conditional identity-testing estimate, not a protocol
knowledge-error theorem. Applying these fixing/independence hypotheses to the actual protocol,
acquiring a suitable tree, producing/reducing an escape and efficient extraction remain the
bridge obligations [above](#knowledge-error-reference-and-scope). A star-shaped family does not
deterministically certify the required polynomial identities. The scalar-round repair supplies
the structured-tree guarantee used by this chain's `CWSSPackage`.

Two independent errors in the printed lemma:

* **Shape.** A coordinate-wise star of vector challenges fixes all but one scalar coordinate on
  each arm, so it proves vanishing only on the axis cross through its center; for `m ≥ 2` the
  nonzero multilinear `(X₁-a)(X₂-b)` vanishes on that entire cross. Adding points to the same arms
  does not help. Under the lemma's own `ℓ = 2` reading the arms carry arbitrary distinct challenge
  *vectors* rather than collinear points, so the axis cross does not apply directly; the objection
  there is a dimension count — the space of multilinears in `m₀` variables has dimension `2 ^ m₀`
  and each accepting point imposes one linear condition, so `D` points cannot pin it down when
  `D < 2 ^ m₀`. This count is **not formalized**, and concerns only generic multilinear
  identity testing: `H₀`'s Boolean table is entrywise `rangeProduct b ∘ wTable` and therefore ranges
  over a structured, non-linear subset of `F ^ (2 ^ m₀)`, so a counterexample polynomial has to be
  exhibited as an actual `hZero … w` to refute the lemma's conclusion rather than its method. No
  such witness is formalized either.
* **Degree.** `D = max(2d, 2b − 1)` is a degree in `α` (Lemma 9) and in the witness value
  `w̃(u, ℓ)` respectively. Neither is a degree in a coordinate of `τ`, in which both batching
  polynomials are multilinear. So the printed lemma over-asks in `D` (two labels per coordinate
  suffice) while under-asking in shape.

ArkLib's repair samples each coordinate of `τ₀` and `τα` in its own scalar challenge round
(`m₀ + m₁` consecutive verifier rounds, soundness parameter `k = 2` per round). A coordinate-wise
family of accepting transcripts is then a complete, path-dependent binary evaluation tree with
sibling-distinct labels, and a multilinear polynomial vanishing at every leaf of such a tree is
identically zero (`NestedEvaluationTree.eq_zero_of_vanishes_comp`,
`ArkLib/Data/MvPolynomial/NestedEvaluationTree.lean`). Per coordinate the challenge distribution
stays uniform.

### Scalar-round protocol

`pSpecNestedZeroCheck` consists of `m₀ + m₁` consecutive scalar verifier-challenge rounds,
with no prover-message rounds. `nestedZeroCheckVerifier` splits the transcript into direct
points `τ₀` and `τα` and appends them to the statement. No execution-equivalence theorem
with Figure 5 or Fiat–Shamir compilation theorem is formalized here.

The CWSS certificate uses the complete sibling-distinct binary transcript tree. Its two
consecutive windows cover the `m₀` coordinates of `τ₀` and the `m₁` coordinates of `τα`.
`nestedZeroCheck_coordinateWiseSpecialSoundWithEscape` extracts from valid leaf witnesses
or establishes `nestedZeroCheckEsc`; it does not construct the transcript tree.

### Informal protocol and compilation observations

The following observations concern possible protocol presentations and proof obligations; they
are not Lean execution-equivalence, Fiat–Shamir or extraction-time theorems.

- **Interactive grouping.** Independent uniform scalar challenges have the same joint
  distribution whether sampled together as a vector or sent successively with no intervening
  prover messages. Within a challenge block, when the prover's next message and the verifier's
  checks use the completed vectors, grouping or splitting preserves this public transcript law.
  This sampling argument does not identify the complete ArkLib and paper protocols, their
  interleaved oracle effects or their costs. The scalar-round specification above supplies the
  typed structure used by the current tree proof.
- **Fiat–Shamir access.** Applying a scalar-round Fiat–Shamir argument requires a compiled
  transcript with the corresponding staged challenge access: subsequent challenge derivations
  are tied to the preceding transcript, including earlier scalar challenges, with an unambiguous
  domain-separated round encoding. Deriving an entire challenge vector from one oracle answer
  at a single fixed transcript is not covered by that scalar-round argument; it needs its own
  vector-challenge extraction and compilation analysis. This distinction concerns the modeled
  random-oracle queries and their dependencies, not a requirement of one physical hash-function
  invocation per coordinate. An implementation's batching or hash expansion must be related to
  the chosen oracle model separately. FMN24 gives a random-oracle Fiat–Shamir knowledge result
  for its CWSS setting; it does not by itself prove this missing ArkLib compilation bridge.
- **A product grid within one round.** A different sufficient identity-testing premise is a full
  Cartesian grid `∏ᵢ Sᵢ` for a challenge block, with `|Sᵢ| > degreeOfᵢ H`. If valid responses on
  this grid share one opening, vanishing at every grid point forces its polynomial `H` to be
  zero. For a multilinear polynomial, take `Sᵢ = {aᵢ, bᵢ}` with `aᵢ ≠ bᵢ`. Covering both
  challenge blocks with the same opening gives the corresponding two identity conclusions;
  distinct short valid openings instead lead to the existing abstract collision alternative.
  These grid points can be regarded as alternative challenges of a single vector-challenge
  round. However, this is a stronger structured-input premise than FMN24's star family
  `SS(S, ℓ, k)`, whose size is `ℓ(k−1)+1`; a full grid with `k` values per coordinate has `k^ℓ`
  points. Although it contains stars, extraction using the whole grid does not establish
  extraction from every star. It therefore supplies neither the unchanged FMN24 CWSS premise
  nor its knowledge bound automatically. The generic grid zero test
  `MvPolynomial.eq_zero_of_degreeOf_lt_card_of_eval_eq_zero_of_fin` is formalized in
  `ArkLib/Data/MvPolynomial/Interpolation.lean`; a same-round grid extraction contract, its
  acquisition algorithm, any escape reduction and their execution bounds are not established
  here.

### What the repair costs

The branching arity per round is only `2`, but there are `m₀ + m₁` challenge rounds instead of
one, so the transcript tree has `2 ^ (m₀ + m₁)` leaves — `NestedEvaluationTree.numLeaves_eq_pow` /
`nestedZeroCheck_numLeaves`. Since `hμn` pins `2^{m₀} ≥ (μ + n·δ)·deg φ` and `hn` pins
`2^{m₁} ≥ n`, with `m₀`, `m₁` chosen minimally that is `< 4·(μ + n·δ)·d·n` transcripts
(`nestedZeroCheck_numLeaves_lt`). This bounds the adapter's leaf count polynomially in the
witness dimensions; it does not bound acquisition or extraction time. `CWSSStructure` itself
imposes no size condition.

Three caveats worth keeping in view:

* **Concretely large.** At [NOZ26]'s `ℓ = 30` parameters (Fig. 9) the `H₀` table has
  `A = (μ + n·δ)·deg φ` entries, `δ = clog_b q`. The digit widening touches only the quotient
  block: at `q ≈ 2^32` and `deg φ = 2^10` it grows that block from `n·d = 5·2^10 ≈ 2^12.3` to
  `n·δ·d ≤ 5·32·2^10 ≈ 2^17.3` (`δ ≤ 32`, maximal at `b = 2` and falling as `b` grows — `δ = 4` at
  `b = 2^8`), i.e. it adds at most `≈ 0.25%` to the `≈ 2^26` that `μ·d` already contributes. So
  `A ≈ 2^26` and `m₀ = 26`, unless the un-widened table sat within that margin of the
  cap, in which case `m₀ = 27`. With `rlinRows = dRows + outerRows + 1 + 1 +
  innerRows = 5` giving `m₁ = 3`, the illustrative choice `m₀ = 26` gives `2^29` transcripts,
  against the `2D − 1 = 4095` of the printed
  lemma's `SS(F, 2, D)` family at `D = max(2d, 2b − 1) = 2048` — a factor `≈ 2^17`. Polynomial ≠
  small, and ROM/Fiat–Shamir knowledge-error translations degrade with tree size and RO-query count.
* **Not accounted for in the composition.** CWSS leaf counts multiply across rounds
  (`K = Πᵢ (ℓᵢ(kᵢ − 1) + 1)`), so the `2^29` above is a multiplicative factor on the whole §4.3
  chain's transcript tree, replacing the single Figure-5 round's `4095`. `Composition.lean` states no
  aggregate leaf count, so the chain-level size is nowhere bounded.
* **Wasteful.** Only `2^{m₀} + 2^{m₁} − 1` leaves are *used* (`H₀` needs one accepting
  continuation per `τ₀`-prefix; `H_α` needs one `m₁`-subtree), while `ChallengeTree.IsStructured`
  demands the complete `2^{m₀} · 2^{m₁}`-leaf tree. The generic structure cannot express the
  weaker two-armed hypothesis.
* **Unquantified.** FMN24 Lemma 2.31's term specializes numerically to
  `(m₀ + m₁)/|F_{q^k}|` for these scalar rounds, matching the unmodified protocol's
  Schwartz–Zippel term. This is only the conditional candidate discussed above, not a theorem
  about ArkLib's CWSS-with-escape chain. The deterministic nested-tree identity theorem is what
  the current formalization establishes.

### Scalar-round identity theorem

The formalization treats each coordinate of `(τ₀, τ₁)` as a separate challenge round and proves
the CWSS-with-escape certificate using a zero test by induction on the number of variables.
The required multivariate root-counting lemma is
`NestedEvaluationTree.eq_zero_of_vanishes_comp`, an induction on a path-dependent `k`-ary tree
rather than on a Cartesian grid; the per-coordinate degree is
`1`, so `k = 2` (both `H₀` and `H_α` are multilinear *in the challenge*; the `2b − 1` and `2`
appearing in the paper are witness-side sumcheck degrees). FMN24 Lemma 2.31's numeric term
specializes to `(m₀ + m₁)/|F_{q^k}|` at `ℓ = 1`, `k = 2`, matching Figure 5's numeric order.
This arithmetic supplies no missing knowledge theorem: the chain currently composes deterministic
CWSS-with-escape certificates, with the bridge obligations stated above.

## Other divergences from the printed Figure 5 / Lemma 10

The scalar-round construction also differs from the printed paper in the following respects.

- **No `1_{≤μ}` indicator in the range summand.** The paper's `F_{0,τ₀}` (p. 22) carries a trailing
  indicator factor `1_{≤μ}(x,y)` restricting the range check to the `z` rows. Eq. (23)'s `H₀`
  carries no such factor, sums over all `(u, ℓ)`, and the bullet above it imposes the constraint
  "for each `u ∈ [μ + n]` and `ℓ ∈ [d]`" — i.e. on the `r` rows too, consistent with the earlier
  `‖z‖∞, ‖r‖∞ ≤ b − 1`. The two readings differ exactly by the indicator, so the paper's own
  `∑_{u,ℓ} F_{0,τ₀}(u,ℓ) = H₀(τ₀)` is **false as printed**. ArkLib follows the Eq. (23) reading: no
  indicator, range constraint on every row of `w̃`, the `n·δ` quotient-digit rows included. Visible
  in `wTable_zRow`/`wTable_rRow` and in `hZero_eq_zero_imp_liftShort` reading both blocks — though
  only the `z` block is substantive there, the digit rows being in range by construction
  (`rhoDigits_valMinAbs_natAbs_le`). Recorded in the `sum_sumcheckPolyZero` docstring.
- **`D` vs `2D − 1` transcripts.** Lemma 10 asks for "`D` valid transcripts … `∈ SS(F_{q^k}, 2, D)`",
  but `SS(S, ℓ, k)` is defined with `ℓ(k−1)+1` elements, so at `(ℓ, k) = (2, D)` the family has
  `2D − 1` transcripts. This is now a paper-side reading note only: the active
  `nestedZeroCheckStructure` uses `k = 2` at each scalar round, where `ℓ(k−1)+1 = 2` children.
- **`D` is the wrong quantity, not just too small.** `D = max(2d, 2b − 1)`: `2d` is the degree in
  `α` bounded in Lemma 9, and `2b − 1` the degree of the range factor in the *witness value*
  `w̃(u, ℓ)`. In the challenge coordinates `τ` both `H₀` and `H_α` are multilinear — each
  `eq̃(τ, ·)` factor is either `τⱼ` or `1 − τⱼ` and the bracketed coefficients are `τ`-free — so the
  natural parameter is `k = 2` per coordinate. The printed lemma therefore over-asks in `D` while
  under-asking in tree shape.
- **`ℓ = 2`, not `log μ + log d + log n`.** The prose immediately above Lemma 10 says to treat
  `(τ₀, τ₁)` as `log μ + log d + log n` coordinates, contradicting the lemma's own `ℓ = 2`.
  The prose reading is refuted formally by the axis cross
  (`exists_nonzero_vanishing_on_axis_cross`); the `ℓ = 2` reading — where the arms carry arbitrary
  distinct vectors, not collinear points — is objected to only by the unformalized dimension count
  of the "Shape" bullet above. ArkLib follows neither as stated: each of the
  `m₀ + m₁` scalar coordinates is its own challenge round — close in spirit to the prose reading,
  but with the per-round transcript tree the extraction actually needs.
- **`τ₀` arity on p. 20.** `τ₀` is drawn from `F^{log μ + log d}` although `w̃`'s domain is
  `[μ + n·δ] × [d]` (the quotient block being its base-`b` digits), so the paper's arity there should read `log(μ + n·δ) + log d`. ArkLib's `m₀` is
  pinned to the latter by `hμn`.

The last three are paper-reading notes recorded here; the protocol-level deviation itself is
recorded in the module docstrings of `ZeroCheck.lean` and `ZeroCheck/Reduction.lean`.

## Shortness: two different notions, and where each one sits

The paper distinguishes weak-opening admissibility from range constraints:

* **Weak-opening admissibility** (Lemma 7: `‖cᵢ·sᵢ‖ ≤ β̄`, `‖cᵢ‖₁ ≤ ω̄`, `cᵢ ∈ Rq^×`) is
  slack-relative and appears in the binding precondition (Remark 2). An extracted weak opening
  `sⱼ = (z⁽ʲ⁾−z⁽⁰⁾)/c̄ⱼ` has a bound on `c̄ⱼ·sⱼ`, not a range bound on `sⱼ` itself.
* **The paper's range constraints** bound the raw witness and quotient by
  `‖z‖∞, ‖r‖∞ ≤ b − 1`.

ArkLib's actual `liftShort Φ bound bDig w` is
`vecLInftyNorm Φ w.z ≤ bound ∧ RhoDigitsShort Φ bound bDig w.ρ`
(`RingSwitch/Reduction.lean`). Its quotient condition bounds the balanced digits of `w.ρ`,
not the raw quotient. `LiftCom` abbreviates the generic
`CoordinateWise.BindingCommitment W Short`, with fields `TCom` and `com` and no binding
assumption. Here it is instantiated at `Short := liftShort Φ bound bDig`; no theorem in this
interface identifies that predicate with the paper's weak-opening admissibility.

**At the batching bridge — derived shortness.** `relBatched` carries the *full* identity
`H₀ ≡ 0`. Since every committed coefficient is a table entry of `wTable`, `H₀ ≡ 0` forces each
into the symmetric range `[−(b−1), b−1]`, so `liftShort` is a *consequence*. `relBatched`
therefore **carries no `liftShort` conjunct**; the pull-back
`mem_relLift_of_relBatched` derives it via `hZero_eq_zero_imp_liftShort` (see Link 5). The range
machinery is load-bearing: the proved pull-back derives the committed witness's shortness from
`H₀ ≡ 0`, rather than assuming it.

**At the point-check seams — explicit shortness.** `relNestedZeroCheck` and `nestedRoundRel`
each require `liftShort … p.2` alongside `t = Com(w̃)`, `H₀(τ₀) = 0` and `H_α(τ_α) = 0`.
`LiftCom.Collision` is
`{p | p.1 ≠ p.2 ∧ com p.1 = com p.2 ∧ Short p.1 ∧ Short p.2}`. Two distinct valid responses
therefore form a member of the abstract `K.Collision` and establish `nestedZeroCheckEsc`.
For a concrete Ajtai commitment, the shortness conditions provide a controlled difference;
arbitrary long openings have no guaranteed short-difference bound. The concrete theorem and
remaining key-generation obligation are described below.

`nestedZeroCheckEsc` is a `ChallengeTree.EscapeEvent` on `(statement, tree)`, not an extractor
output or a binding assumption on `LiftCom`. It asserts a valid leaf-response family containing
a collision; it does not produce that collision or bound its computational cost.

**Scope of a point evaluation.** A single evaluation `H₀^{w̃}(τ₀) = 0` does not in general
establish `H₀ ≡ 0`. The current proof recovers the zero identity from a complete
sibling-distinct depth-`m₀` tree whose valid leaf responses share one opening
(`eq_zero_of_vanishes_comp`). When distinct valid openings occur, the certificate establishes
the collision escape alternative; it does not assert the zero identity for those openings.

For the concrete commitment, the collision-to-Module-SIS relation theorem is available:
`hachiLiftCom` (`RingSwitch/Reduction.lean`) is the Ajtai product `D · (z ‖ digits(ρ))` at a key of
the matching width `μ + n·δ`, `nonrecursiveLiftCom` pins it for the chain (`Concrete.lean`), and
`moduleSIS_relation_of_mem_Collision` proves that a member of its collision set satisfies
`ModuleSIS.relation Φ _ D` at radius `2·bound` — nonzero (`liftMessage_injective`), short, in the
kernel. For an admissible digit base, the quotient digits have the controlled shortness bound
`rhoDigits_valMinAbs_natAbs_le`; `rhoShort_half` bounds the raw quotient only at `q/2`.

What is still open is the *other* half of the tie: `D` is taken as a parameter rather than sampled
by `keygen` alongside the inner-outer commitment's own key, so the escape is not yet discharged by
`outputToModuleSIS_valid_of_verified` (`InnerOuter/Security.lean`). `Composition.lean`'s closing
`TODO` block lists that as open work. Until it lands, "`liftShort` is the right binding regime for
Hachi" is an assumption of this chain about *which* key the hardness is asserted for, not about
whether the collision set is a genuine SIS instance. The range identity of `relBatched` is
discharged over the family by the binary-evaluation-tree zero test
(`hZero_eq_zero_of_evaluationTree`), so the zero-check retains its intended content.

## Residual gaps (out of Lemma-10 scope)

- **Constraint encoding — complete: the two identities and both sum identities are proved.** `hZero`
  and `hAlpha` are genuine multilinear extensions, both coefficient functions are concrete (no
  longer `sorry`), and both now correspond to the paper's own construction:
  - `hAlphaEvals` = the `α`-evaluated per-row lift defect, row-encoded into the `m₁`-cube via
    `rowPoint` (`hAlphaEvals_rowPoint`, axiom-clean); arity pin `n ≤ 2 ^ m₁`. It is a direct
    specification in the *ring* representation, but it is **no longer only that**: the paper's
    Eq. (22) contraction is built (`mAlphaTilde`, `alphaTilde`, `wTablePoint`, `alphaContract`,
    `alphaDefect`) and proved equal to it (`alphaDefect_wTable`, axiom-clean), with the
    relation-level consequence `hAlpha_eq_zero_iff_alphaDefect`. This encoding gap is closed.
  - `wTable` reads the coefficients of the **committed vector** (decoding the `m₀`-cube to
    `row := idx / d`, `col := idx % d`): the `z` block directly, the quotient block as its base-`b`
    digits (`rhoDigits`, `n·δ` rows).

    For an admissible digit base `bDig` (`1 < bDig ≤ q/2`), the digit rows are short by
    construction: `rhoDigits` bounds each entry at radius `⌊bDig/2⌋`
    (`rhoDigits_valMinAbs_natAbs_le`). The soundness content of `H₀` is the `z` block, whose
    shortness follows from `hZero_eq_zero_imp_liftShort`. These two
    bounds supply the shortness needed by `LiftCom.Collision` and its concrete Module-SIS
    interpretation (`moduleSIS_relation_of_mem_Collision`). `H₀` still pins `bZero` through
    the range constraint on `z`.

  Consequently `nestedZeroCheck_coordinateWiseSpecialSoundWithEscape` is **axiom-clean**:
  `#print axioms` reports no `sorryAx` (only ambient `propext`/`Classical.choice`/`Quot.sound`;
  `Classical.choice` is proof-local, assembling a response family from valid
  `ChallengeTree.LeafWitnesses` for the evaluation-tree argument). The standalone kernel
  `NestedEvaluationTree.eq_zero_of_vanishes_comp` is likewise axiom-clean.
  **Range-side soundness `H₀ ≡ 0 ⇒ liftShort` is now proven** (`hZero_eq_zero_imp_liftShort`,
  see Link 5). The two full-cube sum identities `sum_sumcheckPolyZero` / `sum_sumcheckPolyAlpha`
  are proved and axiom-clean too, so this file carries no remaining obligation.
- **Link 5 (batching bridge).** The un-batching pull-back `mem_relLift_of_relBatched`
  (`relBatched → relLift`, `ZeroCheck/Batch.lean`) is **proof-`sorry`-free and axiom-clean**
  (`#print axioms` = `propext`/`Classical.choice`/`Quot.sound`, no `sorryAx`). It establishes both
  residual claims of `relLift`:
  - the per-row `α`-equation from `H_α ≡ 0` (`hAlpha_eq_zero_iff` +
    `hAlphaEvals_rowPoint`, arity pin `n ≤ 2 ^ m₁`);
  - **shortness `liftShort` from `H₀ ≡ 0`** (`hZero_eq_zero_imp_liftShort`): every committed
    coefficient is a table entry (`wTable_zRow`/`wTable_rRow`), hence a root of the range factor
    `P_b`, hence a centered residue of absolute value `≤ b − 1`
    (`valMinAbs_natAbs_le_of_rangeProduct_eq_zero`, using injectivity of `φF` on `ZMod q`). This
    derives shortness rather than assuming it. `liftShort` has a single bound:
    the reconciliation is `b − 1 ≤ γ` on the `z` side, while the quotient side
    needs no reconciliation at all — the committed quotient block holds base-`b` *digits*
    (`rhoDigits`, `wTable_rRow`), which are `⌊b/2⌋`-bounded for every quotient
    (`rhoDigits_valMinAbs_natAbs_le`), so `DigitBaseOk q γ bDig` discharges it outright. Together
    with the column-encoding arity `(μ + n·δ)·deg φ ≤ 2^{m₀}`, these are threaded through
    `batchPackage` and `iteration`.

    Range-checking the raw quotient rows instead would need a second bound of its own, and
    `rhoShort_half` forces that one to `q/2`, pinning `γ = q/2 = bZero − 1` and emptying both the
    Eq. (20) ball check and `LiftCom.Collision` of content. See
    `HonestRangeParams.pinned_of_soundness_orientations`, which lands at `γ = bZero − 1 < q/2`.
  `K.com` and the bound conjunct are carried verbatim. That `hAlpha` is the polynomial constructed
  in paper Eq. (22) is proved separately by `alphaDefect_wTable` /
  `hAlpha_eq_zero_iff_alphaDefect`. The forward/honest-completeness theorem `relLift → relBatched`
  is now proved as well (`mem_relBatched_of_relLift`, packaged as
  `batchReduction_perfectCompleteness`), so this link — like link 6 — is certified in both
  directions. The nonrecursive honest chain uses the proved pure/guarded composition interfaces
  with state-uniform suffix correctness and has only standard axiom dependencies.
- **Executable witness-fed extraction.** `nestedZeroCheckExtractor` is an ordinary executable
  function: `ChallengeTree.LeafWitnesses` supplies an `Option` candidate output witness at each
  leaf, and the extractor returns the all-left entry unchanged, including `none`. Under the CWSS
  validity premise, its certificate proves that this lookup yields the required `relBatched`
  witness unless `nestedZeroCheckEsc` fires. It neither searches `relNestedZeroCheck` nor branches
  on acceptance at runtime. Classical choice appears only inside the proof, where valid leaf
  witnesses are assembled into the total response family required by the evaluation-tree argument.
  The certificate applies to the scalar-round structured tree with `2 ^ (m₀ + m₁)` leaves.
  It proves neither extraction from the paper's printed star family nor an execution-equivalence
  or Fiat–Shamir compilation theorem. Tree acquisition, escape production and execution-cost
  bounds remain open.
- **Sumcheck seam.** `nestedRoundRel` carries `liftShort` on the same shortness-index grounds as
  `relNestedZeroCheck` (see above), and the sumcheck
  bridge's pull-back `mem_relNestedZeroCheck_of_nestedRoundRel` is now **proved and axiom-clean**,
  the two sum identities it rests on (`sum_sumcheckPolyZero` / `sum_sumcheckPolyAlpha`) having
  been discharged. Further down the chain (out of Lemma-10 scope), the
  per-round CWSS `round_coordinateWiseSpecialSoundWithEscape` (Lemma 11) and the
  final-evaluation step (`finalCheck` / `finalEval_coordinateWiseSpecialSoundWith`)
  are proved and axiom-clean as well.
