# NOZ26 Figure 5 / Lemma 10 audit

This page records the specification boundary for link 6 of ArkLib's Hachi opening chain. It is
based on the January 30, 2026 ePrint version of Nguyen–O'Rourke–Zhang, *Hachi: Efficient
Lattice-Based Multilinear Polynomial Commitments over Extension Fields* (`NOZ26`, §4.3,
Figure 5 and Lemma 10).

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
> (`ZeroCheck/Completeness.lean`) proves perfect completeness of Figure 5 relative to `relBatched`,
> `sorry`-free and axiom-clean. The completeness error is exactly zero, because `relBatched`
> asserts the polynomial identities and so both polynomials vanish wherever the challenges happen
> to land; nothing about the challenge distribution is used. So link 6 is now certified in both
> directions — and so is link 5: its forward theorem `relLift → relBatched` is
> `mem_relBatched_of_relLift` (`ZeroCheck/Batch.lean`), packaged as
> `batchReduction_perfectCompleteness` (`ZeroCheck/Completeness.lean`, through
> `ReduceClaim.reduction_completeness_of_imp`). What a completeness statement for the *chain*
> still waits on is not a Hachi theorem but the generic `Reduction.append_completeness`, which is
> still `sorry`; the appended honest chain and the `sorryAx` it inherits are in `HonestChain.lean`.
> Downstream, the link-7 sumcheck-bridge pull-back `mem_relNestedZeroCheck_of_nestedRoundRel`
> and the two sum identities `sum_sumcheckPolyZero` / `sum_sumcheckPolyAlpha` it rests on are now
> proved and axiom-clean, and the bridge is settled in the honest direction too
> (`mem_nestedRoundRel_of_relNestedZeroCheck`,
> `nestedSumcheckBridgeReduction_perfectCompleteness`).
> **The range half is now load-bearing:** shortness (`liftShort`) is *derived* from the range
> identity `H₀ ≡ 0` at the batching bridge (`hZero_eq_zero_imp_liftShort`, resolution *option 1*),
> not carried as a free conjunct of `relBatched`.
>
> **The point seams carry `liftShort`, as the commitment's shortness index.**
> `relNestedZeroCheck` and `nestedRoundRel` each state it alongside `t = Com(w̃)` and the two point
> evaluations. `LiftCom` is the generic `CoordinateWise.BindingCommitment W Short` — fields `TCom`
> and `com` only — instantiated at `Short := liftShort Φ bound bDig`, and its `Collision` set
> requires **both** colliding openings to be short, which is what makes a collision a Module-SIS
> break rather than a triviality. Weak binding is not a field but the escape event
> `nestedZeroCheckEsc`. `relBatched` itself stays norm-free, so nothing derives `liftShort` from an
> assumption of `liftShort`. See "Shortness: two different notions, and where each one sits" below.
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
| Transcript-tree size | `NestedEvaluationTree.numLeaves_eq_pow`, `nestedZeroCheck_numLeaves`, `nestedZeroCheck_numLeaves_lt` | proven, **axiom-clean**; two unformalized steps | `k ^ n` leaves, and `< 4·A·B` at minimal arities. Stated because `CWSSStructure` carries no size bound: an exponential-family repair (e.g. the superseded Kronecker one at `D = 2 ^ m₀`) satisfies `coordinateWiseSpecialSound` just as well. But (i) these count the *adapter's* `NestedEvaluationTree`, not the `ChallengeTree.LeafPath`s the extractor consumes, and (ii) minimality of `m₀`, `m₁` is a hypothesis of `_lt`, not enforced — `hμn`/`hn` bound the arities from below only. |
| Lemma-10 extraction (escape-threaded) | `ZeroCheck.nestedZeroCheckExtractor`, `nestedAssembly_escape_or_mem_relBatched` | proof-sorry-free | Escape pass-through ∨ weak-binding collision ∨ common opening with both identities zero. |
| Lemma-10 binding alternative | `ZeroCheck.nestedZeroCheckEsc` via `LiftCom.Collision` | integrated | Two **distinct short** openings of the shared `t` are a member of `K.Collision`, hence a Module-SIS break of the fixed key ([NOZ26] Lemma 7 / Remark 2). Stated as a `ChallengeTree.EscapeEvent` on `(statement, tree)` rather than an extractor output, so it cannot be satisfied trivially; the shortness both openings need is supplied by `relNestedZeroCheck`'s own `liftShort` conjunct. The concrete instantiation is `hachiLiftCom` (`RingSwitch/Reduction.lean`), the Ajtai product `D · (z ‖ digits(ρ))`, and `moduleSIS_relation_of_mem_Collision` proves its collision set satisfies `ModuleSIS.relation` at radius `2·bound`; what is still open is tying `D` to the inner-outer commitment's own key — see the note at the end of "Shortness" below. |
| Corrected Lemma 10 CWSS | `ZeroCheck.nestedZeroCheck_coordinateWiseSpecialSoundWithEscape` | sorry-free, **axiom-clean** | `m₀ + m₁` scalar rounds with `k = 2`; the structured transcript tree is converted to **one** evaluation tree of depth `m₀ + m₁`, with `H₀` read through its first `m₀` levels (`Fin.castAdd`) and `H_α` through its last `m₁` (`Fin.natAdd`); `#print axioms` = `propext`/`Classical.choice`/`Quot.sound` only. |
| Knowledge error (`∑ᵢ ℓᵢkᵢ/|Sᵢ|^{ℓᵢ}`, [FMN24] Lemma 4) | no declaration | **missing (repo-wide)** | ArkLib has no CWSS-to-knowledge-soundness theorem, so the *quantitative* content of both the paper's claim and this repair — `2(m₀+m₁)/|F_{q^k}|`, negligible — exists only in prose. This is the layer in which the repair's cost over the Schwartz–Zippel bound for unmodified Figure 5 would become visible. |
| Honest completeness of this link | `ZeroCheck.nestedZeroCheckReduction_perfectCompleteness` | proven, **axiom-clean** | Full `Reduction.perfectCompleteness`, for arbitrary `oSpec`/`init`/`impl`. Two halves: `mem_relNestedZeroCheck_of_relBatched` is the algebra (`eval 0 = 0` at *arbitrary* points, hence zero error), and `nestedZeroCheckReduction_run_support` is the execution — an honest run cannot fail, and prover and verifier emit the same statement because both apply the same `castAdd`/`natAdd` split to the same transcript. An earlier revision of this row estimated the whole obligation at "a few lines"; that was true only of the algebra. The execution half needed a new framework lemma, `Reduction.perfectCompleteness_of_run_support` (`OracleReduction/Security/Basic.lean`), since ArkLib had no way to reach `perfectCompleteness` for a challenge-only protocol of arbitrary length. That lemma is generic and every later link can reuse it. |
| Link-5 un-batching pull-back | `ZeroCheck.mem_relLift_of_relBatched` (`batchPackage`) | **the theorem is proven and axiom-clean; paper correspondence is partial** | `relBatched → relLift`; `H_α ≡ 0 ⇒` per-row eqs via `hAlpha_eq_zero_iff` + `hAlphaEvals_rowPoint` (arity pin `n ≤ 2 ^ m₁`); **`H₀ ≡ 0 ⇒ liftShort`** via `hZero_eq_zero_imp_liftShort` (arity pin `(μ+n·δ)·deg φ ≤ 2^{m₀}`, `hd`, range-base fit `b−1 ≤ γ`, and digit-base admissibility `DigitBaseOk q γ bDig` — the quotient half is free, the committed digits being `⌊bDig/2⌋`-bounded for every quotient). The obligation to derive the `H_α` table from paper Eq. (22) is discharged separately by `alphaDefect_wTable`. The forward/honest-completeness direction is the row below. |
| Link-5 forward/completeness direction | `ZeroCheck.mem_relBatched_of_relLift`; `ZeroCheck.batchReduction_perfectCompleteness` | proven, **axiom-clean** | An honest `relLift` witness satisfies `relBatched`: `hZero_eq_zero_of_liftShort` puts every table entry among `P_b`'s roots, and `hAlpha_eq_zero_of_rows` covers the whole Boolean table (zero-padded beyond row `n`). It needs neither arity hypothesis and nothing about `α`, but the range-base fit in the **opposite** orientation (`bound ≤ b − 1`) together with `DigitBaseOk q (b−1) b` — so a single two-sided parameterization is pinned to the paper's `bound = b − 1`, at which `γ = bZero − 1 = O(b)` rather than `q/2`. `batchReduction` is the link as a protocol object (verifier shared with `batchPackage` by `rfl`); its completeness uses this direction alone, via `ReduceClaim.reduction_completeness_of_imp`. |
| Link-5/link-6/link-7 composition | `batchPackage ▷ nestedZeroCheckPackage ▷ nestedSumcheckBridgePackage` (inside `iteration`) | **defined, compiles as a CWSS chain** | The seam relations match by `rfl`. This is the *soundness* composition; it does not close link 5's paper-encoding obligation. The honest counterpart — appending the three links' completeness — is in `HonestChain.lean` and is `sorryAx`-tainted through the generic `Reduction.append_completeness`. |

## Polynomial representation: multilinear value vectors and proof views

The two batched identities now use CompPoly's native Boolean-evaluation representation
`CMlPolynomialEval F m = Vector F (2 ^ m)`. This matches Eqs. (22)–(23): each entry is one
Boolean-cube constraint value, and the vector represents its unique multilinear extension.
Multilinearity is therefore guaranteed by the type rather than proved with `degreeOf` lemmas.

The derived Mathlib views `hZeroML` and `hAlphaML` rebuild the same value tables with
`MvPolynomial.MLE` and are used only in algebraic proofs (the nested-tree zero test crosses to
Mathlib internally); `hZeroML_eq_zero_iff` / `hAlphaML_eq_zero_iff` connect the proof views'
zero identities to the primary vectors, and `hZero_eval_eq` / `hAlpha_eval_eq` bridge pointwise
evaluations.

| Object | Computable definition | Mathlib view | Bridge lemma |
| --- | --- | --- | --- |
| Witness ring | `Rq Φ = {p : CPolynomial (ZMod q) // Φ.reduce p = p}` | `Φ.CyclotomicRing` | `Rq.toQuotient` |
| Quotients `rᵢ` | `LiftedWitness.r : Fin n → CPolynomial (ZMod q)` | `(r i).toPoly` | `CPolynomial.coeff_toPoly` |
| Row sum `∑ⱼ Mᵢⱼzⱼ` | `cRowSum` | `rowSum` | `rowSum_eq_sum_toPoly` |
| Evaluation at `α` | `cEvalAt` (`CPolynomial.eval₂`) | `evalAt` (`eval₂RingHom`) | `cEvalAt_cRowSum_eq_evalAt`, `cEvalAt_eq_evalAt_toPoly` |
| Range factor `P_b` | `rangeProduct` (scalar) | — | `rangeProduct_eq_zero_iff` |
| Table `w̃`, Eq. (21) | `wTable` | — | `wTable_zRow`, `wTable_rRow` |
| `H₀`, Eq. (23) | `hZero : CMlPolynomialEval F m₀` | `hZeroML` | `hZero_eq_zero_iff`, `hZeroML_eq_zero_iff` |
| `H_α`, Eq. (22) | `hAlpha : CMlPolynomialEval F m₁` | `hAlphaML` | `hAlpha_eq_zero_iff`, `hAlphaML_eq_zero_iff` |
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
- **The `m₀`-cube signature of `sumcheckPolyAlpha` is correct — there is no arity mismatch here.**
  Worth stating positively, because the pairing of the return type `CMvPolynomial m₀ F` with the
  batching point `τ₁ : Fin m₁ → F` invites the worry that the `m₀`-cube sum over-counts the
  `m₁`-cube. It does not. In the paper,
  `F_{α,τ₁}(x,y) := w̃(x,y) · α̃(y) · ∑ᵢ eq̃(τ₁, i) · M̃_α(i,x)` is summed over the `w̃` coordinates
  `(u,ℓ)` — the `m₀`-cube — while the row index `i ∈ [n]` (the `m₁` side) is summed *internally*,
  inside the `∑ᵢ eq̃(τ₁, i)·M̃_α(i,x)` factor. `i` is not a cube coordinate, so there is nothing to
  over-count, and the two "fixes" the worry suggests would each break something correct: inserting a
  `∏_{j ≥ m₁} (1 − Xⱼ)` masking factor moves the sum away from `H_α(τ₁) + a` and so falsifies
  `sum_sumcheckPolyAlpha`, whose statement is faithful to p. 22; re-typing to `CMvPolynomial m₁ F`
  makes the `w̃(x,y)` factor untypable, since `w̃` lives on the `m₀`-cube. The sumcheck development therefore needs no
  extra `m₀`/`m₁` pin — the pins `n ≤ 2^{m₁}` and `(μ+n·δ)·deg φ ≤ 2^{m₀}` already carried by link 5
  are about the row-indexing and range-table embeddings, not about this sum.

## Uniform-vector challenge gap (why the repair is needed)

**Figure 5 is not unsound. Lemma 10's proof strategy is.** Since `w̃` is committed before `τ` is
drawn, Schwartz–Zippel bounds `Pr[H₀(τ₀) = 0 ∣ H₀ ≢ 0] ≤ m₀/|F_{q^k}|`, so the protocol *as
printed* is knowledge-sound with error `≈ (m₀ + m₁)/|F_{q^k}|`. What is not provable is the
*deterministic* certification of the identity `H₀ ≡ 0` from a star-shaped family. The claim of this
page is therefore "the paper's zero-check cannot be proved by coordinate-wise special soundness",
not "the paper's zero-check is broken"; the repair exists because this chain composes through CWSS
([FMN24], `CWSSPackage`) rather than through a probabilistic bound.

Two independent errors in the printed lemma:

* **Shape.** A coordinate-wise star of vector challenges fixes all but one scalar coordinate on
  each arm, so it proves vanishing only on the axis cross through its center; for `m ≥ 2` the
  nonzero multilinear `(X₁-a)(X₂-b)` vanishes on that entire cross. Adding points to the same arms
  does not help. Under the lemma's own `ℓ = 2` reading the arms carry arbitrary distinct challenge
  *vectors* rather than collinear points, so the axis cross does not apply directly; the objection
  there is a dimension count — the space of multilinears in `m₀` variables has dimension `2 ^ m₀`
  and each accepting point imposes one linear condition, so `D` points cannot pin it down. That
  count is **not formalized**, and note that it would in any case bound only *generic* multilinear
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

### What the repair actually changes

**Interactively, nothing.** `pSpecNestedScalar` has no `P_to_V` round, so no prover message
separates the `m₀ + m₁` challenge rounds: the verifier map, the prover, and the distribution of the
challenge vector are identical to Figure 5's. The changes are (i) the *shape of transcript tree*
the extractor is handed — a path-dependent binary tree instead of a star — and (ii) under
Fiat–Shamir, that the coordinates be hashed **sequentially** rather than derived from one atomic
random-oracle call. (ii) is the only real protocol-level cost, and it is a genuine one: a
single-hash implementation is *not* covered by this theorem without a multi-coordinate forking
lemma.

**Path dependence is more than the protocol needs.** An interactive extractor rewinding a
one-round Figure 5 prover can request *any* set of challenge vectors, hence a full product grid,
which contains what the induction needs; the mathematically minimal repair is therefore "replace
the star `SS(S, ℓ, k)` by a product set in the same single round", with no round splitting and no
FS caveat. Round splitting is chosen because `SS(S, ℓ, k)` is star-shaped *by definition*, so a
product-shaped family is a new soundness notion requiring a new [FMN24]-Lemma-4 analogue and new
composition theorems; the split-round version reuses both verbatim. This trade-off, not a
mathematical necessity, is why the pSpec has `m₀ + m₁` rounds.

### What the repair costs

The branching arity per round is only `2`, but there are `m₀ + m₁` challenge rounds instead of
one, so the transcript tree has `2 ^ (m₀ + m₁)` leaves — `NestedEvaluationTree.numLeaves_eq_pow` /
`nestedZeroCheck_numLeaves`. Since `hμn` pins `2^{m₀} ≥ (μ + n·δ)·deg φ` and `hn` pins
`2^{m₁} ≥ n`, with `m₀`, `m₁` chosen minimally that is `< 4·(μ + n·δ)·d·n` transcripts
(`nestedZeroCheck_numLeaves_lt`) — polynomial in the witness dimensions, so extraction stays
polynomial. These bounds are now *theorems* rather than prose, because `CWSSStructure` carries no
size condition and therefore cannot itself tell a usable repair from an exponential one.

Three caveats worth keeping in view:

* **Concretely large.** At [NOZ26]'s `ℓ = 30` parameters (Fig. 9) the `H₀` table has
  `A = (μ + n·δ)·deg φ` entries, `δ = clog_b q`. The digit widening touches only the quotient
  block: at `q ≈ 2^32` and `deg φ = 2^10` it grows that block from `n·d = 5·2^10 ≈ 2^12.3` to
  `n·δ·d ≤ 5·32·2^10 ≈ 2^17.3` (`δ ≤ 32`, maximal at `b = 2` and falling as `b` grows — `δ = 4` at
  `b = 2^8`), i.e. it adds at most `≈ 0.25%` to the `≈ 2^26` that `μ·d` already contributes. So
  `A ≈ 2^26` and `m₀ = 26` as before, unless the un-widened table sat within that margin of the
  cap, in which case `m₀ = 27`. With `rlinRows = dRows + outerRows + 1 + 1 +
  innerRows = 5` giving `m₁ = 3`: about `2^29` transcripts, against the `2D − 1 = 4095` of the printed
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
* **Unquantified.** By [FMN24] Lemma 4 the knowledge error of a coordinate-wise special-sound
  family is `∑ᵢ ℓᵢ·kᵢ/|Sᵢ|^{ℓᵢ}`, so at `m₀ + m₁` rounds with `(ℓ, k) = (1, 2)` over
  `S = F_{q^k}` it is `2(m₀ + m₁)/|F_{q^k}|` — negligible at Hachi's field size, and about a
  factor two worse than the `(m₀ + m₁)/|F_{q^k}|` that Schwartz–Zippel gives for the unmodified
  protocol. That lemma is **not formalized in ArkLib**, so none of this arithmetic is
  machine-checked. What the repair buys in exchange is a *deterministic* identity equivalence (the
  nested-tree zero test), which is what the CWSS framework requires.

### Superseded: the one-round Kronecker-seed repair

An earlier repair kept Figure 5's single challenge round but replaced the vector challenges by
two scalar seeds `(ρ₀, ρ_α)` evaluated on Kronecker curves `κ_m(ρ) = (ρ, ρ², ρ⁴, …)`, with
soundness parameter `D = max(2, 2^{m₀}, 2^{m₁})` and identity recovery by univariate root
counting on the pullback `LinearMvExtension.powAlgHom`. It was superseded by the scalar-round
design. Two facts recorded the limit of the seed-based route: for **any** `2^m − 1` seeds there
is a nonzero multilinear polynomial vanishing at all of them, and a collision branch of that
extractor shares an opening across only `2^m − 1` seeds — one short of the root count. Note also
that the Kronecker rendering satisfies the Lean *definition* of CWSS just as well as the adopted
one — what disqualified it (`D = 2^{m₀}` children in a single round, hence an exponential
branching factor) is invisible to `CWSSStructure`, which is why the leaf-count lemmas above are
now stated explicitly.

**Nothing of this route is formalized any more.** Both its Hachi-specific declarations
(`zeroCheckD`, `relZeroCheck`, `kroneckerPoint`-based points, `buildWitnessE`,
`arm_eq_zero_of_family`, …) and the generic Kronecker lemmas that supported it
(`kroneckerPoint`, `kroneckerExp`, `powAlgHom_eq_zero_iff`,
`powAlgHom_injective_on_multilinear`, `multilinear_eq_zero_of_kronecker_roots`,
`exists_nonzero_multilinear_vanishing_on_kronecker_seeds`) have been removed. What survives in
`LinearMvExtension.lean` is the univariate/multilinear conversion itself — `powAlgHom`,
`linearMvExtension`, and their degree bounds, all of which predate this audit and are used by
`ArkLib/Data/CodingTheory/ReedSolomon/Multilinear.lean`. The axis-cross counterexample that
motivates the whole repair survives as `MvPolynomial.exists_nonzero_vanishing_on_axis_cross`, moved
to `ArkLib/Data/MvPolynomial/Multilinear.lean` alongside the rest of the multilinear API — it never
depended on the univariate pullback.
The paragraphs above are therefore a record of a rejected design, not a description of live Lean
code.

**Why it was rejected, quantitatively.** Beyond the arity objection, the seed route *degraded the
soundness error*. For a nonzero `H₀` the univariate pullback `powAlgHom H₀` has degree
`≤ 2^{m₀} − 1`, so a seed lands on a root with probability up to `2^{m₀}/|F_{q^k}|`. At the paper's
Figure 9 parameters (`q ≈ 2^32`, `k = 4` so `|F_{q^k}| ≈ 2^128`; `deg φ = 2^10` and `w̃` length
`(μ + n·δ)·deg φ ≲ 2^26` — see the digit-widening note above — hence `m₀ ≈ 26`, which is also what
`hμn` pins) that is `≈ 2^-102`, against `≈ 2^-123`
for Figure 5's uniform `τ₀` by Schwartz–Zippel — a **~21-bit regression** on a `λ = 128` target.
Buying those bits back was not cheap: `k` must divide `d/2 = 512` ([NOZ26] Lemma 1 / Theorem 1), so
`k` is a power of two — `k = 5` would suffice numerically but is illegal, and the next legal value
is `k = 8`, taking the sumcheck cost `26·k·32·(16+2)` bits from `≈ 7.3 KB` to `≈ 14.6 KB`, i.e.
**double**, plus `F_{q^8}` arithmetic throughout. The adopted scalar-round design has no such
regression: its error is `2(m₀ + m₁)/|F_{q^k}|`, a factor two off the unmodified protocol's
Schwartz–Zippel bound (see "What the repair costs" above).

Two accounting notes on that comparison, since both are easy to get wrong:

- [NOZ26] Lemma 4's `ℓ·k/|S|^ℓ` must **not** be read as `2·D/|F_{q^k}|²` for the seed route. `H₀`
  depends only on `ρ₀` and `H_α` only on `ρ_α`, so a cheating prover needs one seed bad, not both;
  the `|S|^ℓ` denominator would price in an independence the protocol does not have. A knowledge
  error below the direct `2^{m₀}/|F_{q^k}|` bound is in any case impossible, since knowledge error
  dominates the success probability of a witness-less prover.
- The comparison baseline is Figure 5's Schwartz–Zippel error `m₀/|F_{q^k}|`, not
  `2·max(2d, 2b−1)/|F_{q^k}|²`; the latter mixes the paper's `D` with a denominator that does not
  apply.

No bound better than `2^{m₀}/|F_{q^k}|` was ever proved for that reparametrisation, and whether a
*realisable* table attains it stayed open: the sharpness theorem gave tightness for arbitrary
multilinears, but a protocol adversary must exhibit an `H₀` of the form `∑ᵢ eq̃(t,i)·P_b(w̃(i))`,
which that lemma did not construct.

### Scalar-round route (correspondence with the authors)

The axis-cross gap was raised with the [NOZ26] authors directly, and this subsection records that
correspondence, which is the provenance of the design now formalized.

In a reply of 2026-07-31, George O'Rourke confirmed the diagnosis — that Schwartz–Zippel cannot be
invoked under CWSS, because the CWSS tree constrains only the coordinate-wise structure of the
challenges and says nothing about their distribution — and also noted that the printed analysis
takes `(τ₀, τ₁)` as a two-coordinate vector even though the two coordinates are drawn from
`F_{q^k}^{log μ + log d}` and `F_{q^k}^{log n}`, neither of which is `F_{q^k}`.
The formalization treats each coordinate of `(τ₀, τ₁)` as a separate challenge round and proves
plain `(k, …, k)`-special soundness by induction on the number of variables. The required
multivariate root-counting lemma is `NestedEvaluationTree.eq_zero_of_vanishes_comp`, an induction
on a path-dependent `k`-ary tree rather than on a Cartesian grid; the per-coordinate degree is
`1`, so `k = 2` (both `H₀` and `H_α` are multilinear *in the challenge*; the `2b − 1` and `2`
appearing in the paper are witness-side sumcheck degrees). The error stays at Figure 5's order,
`2(m₀ + m₁)/|F_{q^k}|` by [FMN24] Lemma 4 at `ℓᵢ = 1`, `kᵢ = 2`; that lemma itself is still not
formalized in ArkLib, so the arithmetic remains prose. This form supports the generic
CWSS-to-knowledge-soundness composition used by the rest of the chain.

## Other divergences from the printed Figure 5 / Lemma 10

These are deliberate and correct, but they are not the axis-cross repair and a reader comparing this
formalization against the printed paper will otherwise read them as bugs.

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

[NOZ26] carries **two unrelated** shortness notions, and the whole difficulty here came from
identifying them:

* **weak-opening admissibility** (Lemma 7: `‖cᵢ·sᵢ‖ ≤ β̄`, `‖cᵢ‖₁ ≤ ω̄`, `cᵢ ∈ Rq^×`) —
  *slack-relative*, part of what "opening" means for an Ajtai-style scheme, and the precondition
  of its binding property (Remark 2). Note an extracted weak opening `sⱼ = (z⁽ʲ⁾−z⁽⁰⁾)/c̄ⱼ` is
  **not** range-short: only `c̄ⱼ·sⱼ` is bounded;
* **`liftShort`** — the *range* claim `‖z‖∞, ‖r‖∞ ≤ b − 1` that Figure 4 checks and that
  `H₀ ≡ 0` proves.

The formalization does **not** carry a separate type for the first notion. `LiftCom` is an
abbreviation for the generic `CoordinateWise.BindingCommitment W Short`
(`RingSwitch/Reduction.lean`), a two-field structure — the commitment space `TCom` and the
deterministic map `com` — indexed by the shortness regime its binding guarantee is restricted to.
Hachi instantiates that index with the range predicate itself,
`LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig)`, and the two notions are therefore
**identified** rather than separated. Consequently:

**At the batching bridge — derived shortness.** `relBatched` carries the *full* identity
`H₀ ≡ 0`. Since every committed coefficient is a table entry of `wTable`, `H₀ ≡ 0` forces each
into the symmetric range `[−(b−1), b−1]`, so `liftShort` is a *consequence*. `relBatched`
therefore **carries no `liftShort` conjunct**; the pull-back
`mem_relLift_of_relBatched` derives it via `hZero_eq_zero_imp_liftShort` (see Link 5). This is
the range machinery is load-bearing, and knowledge soundness *proves* the committed witness short
rather than assuming it.

**At the point-check seams — `liftShort` is present as the commitment's shortness index.**
`relNestedZeroCheck` and `nestedRoundRel` each carry `liftShort … p.2` alongside
`t = Com(w̃)`, `H₀(τ₀) = 0` and `H_α(τ_α) = 0`. This is not a range assumption smuggled in ahead
of its proof, and it is not optional: `LiftCom.Collision` is defined as
`{p | p.1 ≠ p.2 ∧ com p.1 = com p.2 ∧ Short p.1 ∧ Short p.2}`, so a colliding pair only counts as a
Module-SIS break when **both** openings are short — a collision of two long openings of an Ajtai
commitment is easy to produce and yields nothing. The conjunct is exactly what lets the
differing-witness branch of the extractor land in `K.Collision` and fire the escape event; see the
"Every conjunct the collision side needs is supplied by `relNestedZeroCheck` itself" note on
`nestedAssembly_escape_or_mem_relBatched`, and the "Where the norm sits" section of
`ZeroCheck/Reduction.lean`'s module docstring, which is the authoritative statement of this design.
`nestedZeroCheck_coordinateWiseSpecialSoundWithEscape` is axiom-clean under it.

Weak binding is **not a field** of `LiftCom` and not an extractor output. It enters as the escape
event `nestedZeroCheckEsc` — a `ChallengeTree.EscapeEvent` on `(statement, tree)`, the Hachi
analogue of the generic `CommittedScalar.escLocal`/`escEvent`. Making it an event rather than a
hypothesis is what keeps it from being trivially satisfiable, since a compressing commitment's
collision set is never empty.

**Why the point evaluation is insufficient.** A single accepting branch pins only
`H₀^{w̃}(τ₀) = 0` at one point, and shortness is *not* derivable from that: a nonzero multilinear
polynomial vanishing at any single prescribed point always exists, and recovering `H₀ ≡ 0` for
one opening needs the *complete* sibling-distinct depth-`m₀` tree — all `2^{m₀}` leaves — to
share that opening (`eq_zero_of_vanishes_comp`). The collision branch of
`nestedAssembly_escape_or_mem_relBatched` is by definition the case where the leaves do *not*
share one opening, so it can never run the zero test for a *single* colliding opening. (The
superseded Kronecker-seed variant hit the same wall in sharp form — `2^m − 1` seeds never suffice —
as recorded in "Superseded: the one-round Kronecker-seed repair" above.)

Note this is **not** a weakening of the binding assumption to unconditional binding, which would
be false for Ajtai commitments: `Collision`'s `Short` conjuncts are precisely what keeps the
regime conditional. A concrete `LiftCom` whose collision set really is a Module-SIS target now exists:
`hachiLiftCom` (`RingSwitch/Reduction.lean`) is the Ajtai product `D · (z ‖ digits(ρ))` at a key of
the matching width `μ + n·δ`, `nonrecursiveLiftCom` pins it for the chain (`Concrete.lean`), and
`moduleSIS_relation_of_mem_Collision` proves that a member of its collision set satisfies
`ModuleSIS.relation Φ _ D` at radius `2·bound` — nonzero (`liftMessage_injective`), short, in the
kernel. That the norm conjunct is non-vacuous is exactly what committing the quotient's **digits**
buys: with the raw quotient the block was only `q/2`-bounded (`rhoShort_half`).

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

    **Superseded reasoning, recorded because it was the argument for the raw layout.** An earlier
    version of this audit held that `H₀` must range-check *raw* `z`/`r` coefficients, since digits
    "are always in range by construction" and a digit table would make the check vacuous. The first
    half is right and the conclusion is wrong. The digit rows of `H₀` *are* automatically satisfied
    here — `wTable` computes them from `w` by `rhoDigits`, so within this model nothing can put an
    out-of-range value there — and `H₀`'s soundness content is therefore the `z` block alone
    (`hZero_eq_zero_imp_liftShort`'s first conjunct). But the raw layout's apparent non-vacuity was
    illusory: the only unconditional bound on a raw Hachi quotient is `q/2` (`rhoShort_half`,
    sharp), so the quotient half of `H₀ ≡ 0` could only be *satisfiable* at `bZero − 1 ≥ q/2` — a
    range box that is all of `ZMod q`, hence a check with no content, at a range polynomial of
    degree linear in `q`.

    The trade is therefore between a check that is trivially satisfied at a **small** base and one
    that is trivially satisfied at a base so large it is vacuous anyway. The digit layout wins
    twice over: the bound the quotient half would have supplied is supplied by *construction*, at
    radius `⌊b/2⌋` instead of `q/2` (`rhoDigits_valMinAbs_natAbs_le`), and that is what makes
    `LiftCom.Collision` a real Module-SIS instance (`moduleSIS_relation_of_mem_Collision`).
    `H₀` stays load-bearing for the `z` block, and it is still what pins `bZero`.

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
    derives shortness rather than assuming it. Since the gadget refactor `liftShort` has a
    **single** bound: the reconciliation is `b − 1 ≤ γ` on the `z` side, while the quotient side
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
  directions; what an end-to-end completeness statement still hits is the generic
  `Reduction.append_completeness`, not a Hachi obligation.
- **Executable witness-fed extraction.** `nestedZeroCheckExtractor` is an ordinary executable
  function: `ChallengeTree.LeafWitnesses` supplies an `Option` candidate output witness at each
  leaf, and the extractor returns the all-left entry unchanged, including `none`. Under the CWSS
  validity premise, its certificate proves that this lookup yields the required `relBatched`
  witness unless `nestedZeroCheckEsc` fires. It neither searches `relNestedZeroCheck` nor branches
  on acceptance at runtime. Classical choice appears only inside the proof, where valid leaf
  witnesses are assembled into the total response family required by the evaluation-tree argument.
  The remaining caveat is the repaired scalar-round setting, not missing witnesses: it is not a
  proof of the paper's printed star extraction, it requires sequential Fiat–Shamir hashing, and its
  complete transcript tree has `2 ^ (m₀ + m₁)` leaves.
- **Sumcheck seam.** `nestedRoundRel` carries `liftShort` on the same shortness-index grounds as
  `relNestedZeroCheck` (see above), and the sumcheck
  bridge's pull-back `mem_relNestedZeroCheck_of_nestedRoundRel` is now **proved and axiom-clean**,
  the two sum identities it rests on (`sum_sumcheckPolyZero` / `sum_sumcheckPolyAlpha`) having
  been discharged. Further down the chain (out of Lemma-10 scope), the
  per-round CWSS `round_coordinateWiseSpecialSoundWithEscape` (Lemma 11) and the
  final-evaluation step (`finalCheck` / `finalEval_coordinateWiseSpecialSoundWith`)
  are proved and axiom-clean as well.

## Design choices

1. At the batching bridge, derive shortness from the range identity `H₀ ≡ 0`
   (`hZero_eq_zero_imp_liftShort`), so `relBatched` does not carry a shortness conjunct;
2. At the point/sumcheck seams, keep `liftShort` as a relation conjunct there, as the
   index of `CoordinateWise.BindingCommitment`. This is what
   makes a colliding pair a member of `LiftCom.Collision`. The cost is that the point seams
   *assume* a predicate the chain elsewhere proves; the reason that is not circular is that the
   relation which proves it — `relBatched`, via `H₀ ≡ 0` — carries no shortness conjunct of its
   own, so nothing derives `liftShort` from an assumption of `liftShort`.
3. Do not weaken binding to *unconditional* on raw tables: it would erase the conjunct but is
   **unsound** — two long openings of one Ajtai commitment are easy to find and yield no
   Module-SIS solution. Keeping `Collision`'s `Short` conjuncts preserves the conditional regime.
