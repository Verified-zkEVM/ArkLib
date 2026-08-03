# NOZ26 Figure 5 / Lemma 10 audit

This page records the specification boundary for link 6 of ArkLib's Hachi opening chain. It is
based on the January 30, 2026 ePrint version of Nguyen–O'Rourke–Zhang, *Hachi: Efficient
Lattice-Based Multilinear Polynomial Commitments over Extension Fields* (`NOZ26`, §4.3,
Figure 5 and Lemma 10).

Last revalidated against the formalization: **3 August 2026**.

> **Status (integrated; link-5 completeness direction still open).** The corrected Lemma 10 is
> formalized *inside* the escape-threaded opening chain: `nestedZeroCheckPackage` reduces
> `relBatchedE → relNestedZeroCheckE` and is composed as
> `batchPackage ▷ nestedZeroCheckPackage ▷ nestedSumcheckBridgePackage` in `Composition.lean`
> (`openCore`). The CWSS theorem `nestedZeroCheck_coordinateWiseSpecialSound` is **`sorry`-free and
> axiom-clean** (the `H_α`/`H₀` values used by the theorem are concrete), and the link-5 batching bridge's
> un-batching pull-back `mem_relLiftE_of_relBatchedE` is likewise **proven and axiom-clean relative
> to those definitions**. **Paper Eq. (22) is now formalized**: `mAlphaTilde` (`M̃_α`),
> `alphaTilde` (`α̃`) and `alphaContract` build the paper's public contraction against the committed
> table, and `alphaDefect_wTable` / `hAlpha_eq_zero_iff_alphaDefect` prove it equal to the per-row
> defect that `hAlphaEvals` writes down directly (axiom-clean). The residual link-5 obligation is
> the forward/honest-completeness theorem `relLiftE → relBatchedE`, which is still absent.
> Downstream, the link-7 sumcheck-bridge pull-back `mem_relNestedZeroCheckE_of_nestedRoundRelE`
> is now **proved**, but `#print axioms` shows it inherits `sorryAx` from the two still-`sorry`
> sum identities `sum_sumcheckPolyZero` / `sum_sumcheckPolyAlpha` (F5).
> **The range half is now load-bearing:** shortness (`liftShort`) is *derived* from the range
> identity `H₀ ≡ 0` at the batching bridge (`hZero_eq_zero_imp_liftShort`, resolution *option 1*),
> not carried as a free conjunct of `relBatched`.
>
> **Temporary point-seam assumption.** `relNestedZeroCheck` and `nestedRoundRel` carry `liftShort` as a
> semantic admissibility conjunct. This is needed by the norm-conditioned weak-binding escape
> `K.collision_mem`: a single point evaluation or partial-sum claim cannot establish that an
> individual colliding opening is short. These relations do not carry the global identity
> `H₀ ≡ 0`; the zero-check extracts that identity from a distinct binary evaluation tree in the
> common-opening branch. At the batching bridge, shortness remains derived from `H₀ ≡ 0`, not
> assumed.
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
| Batched range identity, Eq. (23) | `ZeroCheck.hZero : CMlPolynomialEval F m₀` | represented, **concrete, computable, load-bearing** | The stored vector is exactly the Boolean table of range factors; multilinearity is structural. Entry content `wTable` reads the committed `z`/`r` coefficients directly, and `H₀ ≡ 0 ⇒ liftShort` is proven by `hZero_eq_zero_imp_liftShort`. |
| Batched row identity, Eq. (22) | `ZeroCheck.hAlpha : CMlPolynomialEval F m₁` | represented, **concrete, computable, paper-faithful** | The stored vector is the per-row defect table `hAlphaEvals`, so multilinearity and the pull-back are structural. The paper's route through the `M̃_α`/`w̃`/`α̃` contraction is built separately (`mAlphaTilde`, `alphaTilde`, `alphaContract`, `alphaDefect`) and proved equal to that table by `alphaDefect_wTable`, with the relation-level form `hAlpha_eq_zero_iff_alphaDefect`. |
| Eq. (22) contraction ↔ row defect | `ZeroCheck.alphaDefect_wTable`, `hAlphaEvals_eq_alphaDefect`, `hAlpha_eq_zero_iff_alphaDefect` | proven, **axiom-clean** | §4.3's "represent the constraints by polynomials" step: the only place the table encoding of the witness (commitment/sumcheck side) meets the ring encoding (`relLift` side). Arity pins `hd : 0 < deg φ` and `(μ+n)·deg φ ≤ 2^{m₀}`; the `Rq` column bound is `CyclotomicModulus.natDegree_lt_of_reduced`. |
| Figure-5 point checks | `ZeroCheck.relNestedZeroCheck` / `relNestedZeroCheckE` | deliberately repaired | Points are assembled directly from `m₀ + m₁` scalar challenge rounds; evaluation uses `CMlPolynomialEval.eval` directly; escape-threaded (`Set.withEscape K.esc`). |
| Axis-cross counterexample | `LinearMvExtension.exists_nonzero_vanishing_on_axis_cross` | proven | Formally refutes the identity-testing step used by the uniform-vector argument. |
| Nested zero-test kernel | `CMlPolynomialEval.BinaryEvaluationTree.eq_zero_of_polynomialVanishes` (Hachi wrappers `hZero_eq_zero_of_binaryEvaluationTree`, `hAlpha_eq_zero_of_binaryEvaluationTree`) | proven, **axiom-clean** | A sibling-distinct complete binary tree with vanishing leaves forces the computable multilinear polynomial to be zero (`ToCompPoly/Multilinear/NestedEvaluationTree.lean`). |
| Lemma-10 extraction (escape-threaded) | `ZeroCheck.buildNestedWitnessE`, `buildNestedWitnessE_mem_relBatchedE` | proof-sorry-free | Escape pass-through ∨ weak-binding collision ∨ common opening with both identities zero. |
| Lemma-10 binding alternative | `LiftCom.escOfCollision` via `K.collision_mem` | integrated | Distinct short openings of the shared `t` become an escape `e ∈ K.esc` (Hachi weak binding). |
| Corrected Lemma 10 CWSS | `ZeroCheck.nestedZeroCheck_coordinateWiseSpecialSound` | sorry-free, **axiom-clean** | `m₀ + m₁` scalar rounds with `k = 2`; the structured transcript tree is converted to CompPoly binary evaluation trees; `#print axioms` = `propext`/`Classical.choice`/`Quot.sound` only. |
| Link-5 un-batching pull-back | `ZeroCheck.mem_relLiftE_of_relBatchedE` (`batchPackage`) | **the theorem is proven and axiom-clean; paper correspondence is partial** | `relBatchedE → relLiftE`; `H_α ≡ 0 ⇒` per-row eqs via `hAlpha_eq_zero_iff` + `hAlphaEvals_rowPoint` (arity pin `n ≤ 2 ^ m₁`); **`H₀ ≡ 0 ⇒ liftShort`** via `hZero_eq_zero_imp_liftShort` (arity pin `(μ+n)·deg φ ≤ 2^{m₀}`, `hd`, range-base fits `b−1 ≤ γ`, `b−1 ≤ ρBound`). The obligation to derive the `H_α` table from paper Eq. (22) is discharged separately by `alphaDefect_wTable`; what remains missing for link 5 is only the forward/honest-completeness direction. |
| Link-5 forward/completeness direction | no declaration | **missing** | There is no theorem showing that an honest `relLiftE` witness satisfies `relBatchedE`, nor an honest-completeness result for `batchPackage`. This is separate from CWSS, whose direction only needs the pull-back. |
| Link-5/link-6/link-7 composition | `batchPackage ▷ nestedZeroCheckPackage ▷ nestedSumcheckBridgePackage` (`openCore`) | **defined, compiles as a CWSS chain** | The seam relations match by `rfl`. This does not close link 5's paper-encoding or honest-completeness obligations. |

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
| Sumcheck summands `F_{0,τ₀}`, `F_{α,τ₁}` | `sumcheckPolyZero`, `sumcheckPolyAlpha` (via `cEqualityPolynomial`, `cRangeProduct`, `cMultilinearExtension`, `alphaPublicEvals`) | `hZeroML`/`hAlphaML` in the sum identities | `sum_sumcheckPolyZero`, `sum_sumcheckPolyAlpha` (**both still `sorry`**) |
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
- **The sumcheck summands are now concrete; only their sum identities remain `sorry`.** The
  definitions `sumcheckPolyZero` (`F_{0,τ₀} = eq̃(τ₀, ·) · P_b(mle[w̃])`, per-variable degree
  `2b = roundDegZero b`), `sumcheckPolyAlpha` (the paper's
  `F_{α,τ₁} = mle[w̃] · mle[α̃(·) · ∑ᵢ eq̃(τ₁, i)·M̃_α(i, ·)]`, per-variable degree
  `2 = roundDegAlpha`), the public target `zcTargetAlpha = ∑ᵢ eq̃(τ₁, i)·yᵢ(α)` and the prover
  fold `hypercubeSum` all have concrete computable bodies (via `cEqualityPolynomial`,
  `cRangeProduct`, `cMultilinearExtension`, `alphaPublicEvals`). What remains `sorry`
  (milestone F5/F7) are the two full-cube sum identities `sum_sumcheckPolyZero`
  (`∑ F_{0,τ₀} = H₀(τ₀)`) and `sum_sumcheckPolyAlpha` (`∑ F_{α,τ₁} = H_α(τ₁) + zcTargetAlpha`).
  The sumcheck bridge's proved pull-back invokes exactly these two, which is where its `sorryAx`
  comes from.
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
  makes the `w̃(x,y)` factor untypable, since `w̃` lives on the `m₀`-cube. F7 therefore needs no
  extra `m₀`/`m₁` pin — the pins `n ≤ 2^{m₁}` and `(μ+n)·deg φ ≤ 2^{m₀}` already carried by link 5
  are about the row-indexing and range-table embeddings, not about this sum.

## Uniform-vector challenge gap (why the repair is needed)

A coordinate-wise star of vector challenges fixes all but one scalar coordinate on each arm. It
therefore proves vanishing only on the axis cross through its center. For at least two variables,
the nonzero multilinear polynomial `(X₁-a)(X₂-b)` vanishes on that entire cross. Increasing the
number of points on the same arms does not repair the argument.

ArkLib's repair samples each coordinate of `τ₀` and `τα` in its own scalar challenge round
(`m₀ + m₁` consecutive verifier rounds, soundness parameter `k = 2` per round). A coordinate-wise
family of accepting transcripts is then a complete, path-dependent binary evaluation tree with
sibling-distinct labels, and a multilinear polynomial vanishing at every leaf of such a tree is
identically zero (`CMlPolynomialEval.BinaryEvaluationTree.eq_zero_of_polynomialVanishes`,
`ToCompPoly/Multilinear/NestedEvaluationTree.lean`). Per coordinate the challenge distribution
stays uniform; only the round structure changes.

### What the repair costs

The branching arity per round is only `2`, but there are `m₀ + m₁` challenge rounds instead of
one, so the transcript tree has `2^{m₀ + m₁}` leaves. Since `hμn` pins
`2^{m₀} ≥ (μ + n)·deg φ` and `hn` pins `2^{m₁} ≥ n`, with `m₀`, `m₁` chosen minimally that is
`O((μ + n)·d·n)` transcripts —
polynomial in the witness dimensions, so the extraction stays polynomial. By [NOZ26] Lemma 4 the
knowledge error of a coordinate-wise special-sound family is `∑ᵢ ℓᵢ·kᵢ/|Sᵢ|^{ℓᵢ}`, so at
`m₀ + m₁` rounds with `(ℓ, k) = (1, 2)` over `S = F_{q^k}` it is `2(m₀ + m₁)/|F_{q^k}|` —
negligible at Hachi's field size. What the repair buys in exchange is a *deterministic* identity
equivalence (the nested-tree zero test), strictly stronger than the Schwartz–Zippel bound
Lemma 10 actually needed.

### Superseded: the one-round Kronecker-seed repair

An earlier repair kept Figure 5's single challenge round but replaced the vector challenges by
two scalar seeds `(ρ₀, ρ_α)` evaluated on Kronecker curves `κ_m(ρ) = (ρ, ρ², ρ⁴, …)`, with
soundness parameter `D = max(2, 2^{m₀}, 2^{m₁})` and identity recovery by univariate root
counting (`multilinear_eq_zero_of_kronecker_roots`). It was superseded by the scalar-round
design; the sharpness theorem `exists_nonzero_multilinear_vanishing_on_kronecker_seeds` records
the limit of the seed-based route (for **any** `2^m − 1` seeds there is a nonzero multilinear
polynomial vanishing at all of them, and a collision branch of that extractor shares an opening
across only `2^m − 1` seeds — one short of the root count). Its Hachi-specific declarations
(`zeroCheckD`, `relZeroCheck`, `kroneckerPoint`-based points, `buildWitnessE`,
`arm_eq_zero_of_family`, …) have been removed; the generic Kronecker lemmas remain available in
`LinearMvExtension.lean` independently of this protocol.

## Other divergences from the printed Figure 5 / Lemma 10

These are deliberate and correct, but they are not the axis-cross repair and a reader comparing this
formalization against the printed paper will otherwise read them as bugs.

- **No `1_{≤μ}` indicator in the range summand.** The paper's `F_{0,τ₀}` (p. 22) carries a trailing
  indicator factor `1_{≤μ}(x,y)` restricting the range check to the `z` rows. Eq. (23)'s `H₀`
  carries no such factor, sums over all `(u, ℓ)`, and the bullet above it imposes the constraint
  "for each `u ∈ [μ + n]` and `ℓ ∈ [d]`" — i.e. on the `r` rows too, consistent with the earlier
  `‖z‖∞, ‖r‖∞ ≤ b − 1`. The two readings differ exactly by the indicator, so the paper's own
  `∑_{u,ℓ} F_{0,τ₀}(u,ℓ) = H₀(τ₀)` is **false as printed**. ArkLib follows the Eq. (23) reading: no
  indicator, range constraint on both row blocks. Visible in `wTable_zRow`/`wTable_rRow` and in
  `hZero_eq_zero_imp_liftShort` discharging a `z`-side *and* an `r`-side bound. Recorded in the
  `sum_sumcheckPolyZero` docstring.
- **`D` vs `2D − 1` transcripts.** Lemma 10 asks for "`D` valid transcripts … `∈ SS(F_{q^k}, 2, D)`",
  but `SS(S, ℓ, k)` is defined with `ℓ(k−1)+1` elements, so at `(ℓ, k) = (2, D)` the family has
  `2D − 1` transcripts. This is now a paper-side reading note only: the active
  `nestedZeroCheckStructure` uses `k = 2` at each scalar round, where `ℓ(k−1)+1 = 2` children.
- **`ℓ = 2`, not `log μ + log d + log n`.** The prose immediately above Lemma 10 says to treat
  `(τ₀, τ₁)` as `log μ + log d + log n` coordinates, contradicting the lemma's own `ℓ = 2`.
  ArkLib follows neither as stated: each of the `m₀ + m₁` scalar coordinates is its own
  challenge round — close in spirit to the prose reading, but with the per-round transcript
  tree the extraction actually needs.
- **`τ₀` arity on p. 20.** `τ₀` is drawn from `F^{log μ + log d}` although `w̃`'s domain is
  `[μ + n] × [d]`, so the paper's arity there should read `log(μ + n) + log d`. ArkLib's `m₀` is
  pinned to the latter by `hμn`.

The last three are paper-reading notes recorded here; the protocol-level deviation itself is
recorded in the module docstrings of `ZeroCheck.lean` and `ZeroCheck/Reduction.lean`.

## Shortness: derived where possible (option 1), assumed only where unavoidable (option 2)

Shortness (`liftShort`) enters the chain in two structurally different places, and the two are
handled differently.

**At the batching bridge — derived (option 1).** `relBatched` carries the *full* identity
`H₀ ≡ 0`. Since every committed coefficient is a table entry of `wTable`, `H₀ ≡ 0` forces each
into the symmetric range `[−(b−1), b−1]`, so `liftShort` is a *consequence*. `relBatched`
therefore **no longer carries `liftShort` as a conjunct**; the pull-back
`mem_relLiftE_of_relBatchedE` derives it via `hZero_eq_zero_imp_liftShort` (see Link 5). This is
the fix requested in review PR #656: the range machinery is load-bearing, and knowledge soundness
*proves* the committed witness short rather than assuming it.

**At the point-check seams — temporarily assumed (option 2).** The differing-witness branch of
Lemma 10 gives two tables with the same commitment. `LiftCom.collision_mem` (Hachi Remark 2 /
Lemma 7) is **norm-conditioned**: a collision becomes an escape only when *both* openings are
short. But `relNestedZeroCheck` (and the sumcheck round relation `nestedRoundRel`) only pin
*point* evaluations `H₀(τ₀) = 0` — one assembled point per accepting branch. A single point does
**not** recover `H₀ ≡ 0` for that opening (that needs the whole binary evaluation tree to share
one opening, which is exactly the *non*-collision case). So the two colliding openings'
shortness cannot be derived from the checks, and `relNestedZeroCheck`/`nestedRoundRel` carry the
`liftShort` conjunct for now. This is completeness-preserving (the honest `w̃` is short) and is
*resolution option 2*.

**Why the point evaluation is insufficient.** A single accepting branch pins only
`H₀^{w̃}(τ₀) = 0` at one point, and shortness is *not* derivable from that: a nonzero multilinear
polynomial vanishing at any single prescribed point always exists, and recovering `H₀ ≡ 0` for
one opening needs the *complete* sibling-distinct depth-`m₀` tree — all `2^{m₀}` leaves — to
share that opening (`eq_zero_of_polynomialVanishes`). The collision branch of
`buildNestedWitnessE` is by definition the case where the leaves do *not* share one opening, so
it can never run the zero test for a *single* colliding opening. (The superseded Kronecker-seed
variant hit the same wall in sharp form: see
`exists_nonzero_multilinear_vanishing_on_kronecker_seeds` above.)

Consequently the temporary fix is to state shortness explicitly at these seams. The range
identity of `relBatched` is still discharged over the family by the binary-evaluation-tree zero
test (`hZero_eq_zero_of_binaryEvaluationTree`), so the zero-check retains its intended content.
Removing the temporary shortness assumption requires either unconditional binding or an
extraction interface that supplies admissibility evidence before the collision branch.

## Residual gaps (out of Lemma-10 scope)

- **F5 encoding — the two identities are complete; only the sumcheck summands remain.** `hZero`
  and `hAlpha` are genuine multilinear extensions, both coefficient functions are concrete (no
  longer `sorry`), and both now correspond to the paper's own construction:
  - `hAlphaEvals` = the `α`-evaluated per-row lift defect, row-encoded into the `m₁`-cube via
    `rowPoint` (`hAlphaEvals_rowPoint`, axiom-clean); arity pin `n ≤ 2 ^ m₁`. It is a direct
    specification in the *ring* representation, but it is **no longer only that**: the paper's
    Eq. (22) contraction is built (`mAlphaTilde`, `alphaTilde`, `wTablePoint`, `alphaContract`,
    `alphaDefect`) and proved equal to it (`alphaDefect_wTable`, axiom-clean), with the
    relation-level consequence `hAlpha_eq_zero_iff_alphaDefect`. So this is no longer an F5 gap.
  - `wTable` reads the committed `z`/`r` coefficients **directly** (decoding the `m₀`-cube to
    `row := idx / d`, `col := idx % d`), so `H₀ ≡ 0` is a genuine (non-vacuous) shortness statement
    on the committed data. (Re-decomposing to base-`b` digits would be vacuous — digits are always
    in range by construction; the paper's gadget decomposition is the honest prover's pre-commit
    step, not part of the range test.)

  Consequently `nestedZeroCheck_coordinateWiseSpecialSound` is **axiom-clean**: `#print axioms`
  reports no `sorryAx` (only ambient `propext`/`Classical.choice`/`Quot.sound`; the
  `Classical.choice` is the constructivity caveat below, from `buildNestedWitnessE`'s branch
  selection). The standalone kernel `eq_zero_of_polynomialVanishes` is likewise axiom-clean.
  **Range-side soundness `H₀ ≡ 0 ⇒ liftShort` is now proven** (`hZero_eq_zero_imp_liftShort`,
  see Link 5) — no longer an F5 gap. **Still F5 (out of Lemma-10 scope):** the two sum identities
  `sum_sumcheckPolyZero` / `sum_sumcheckPolyAlpha` (the summand *definitions* are now concrete).
- **Link 5 (batching bridge).** The un-batching pull-back `mem_relLiftE_of_relBatchedE`
  (`relBatchedE → relLiftE`, `ZeroCheck/Batch.lean`) is **proof-`sorry`-free and axiom-clean**
  (`#print axioms` = `propext`/`Classical.choice`/`Quot.sound`, no `sorryAx`). It establishes both
  residual claims of `relLift`:
  - the per-row `α`-equation from `H_α ≡ 0` (`hAlpha_eq_zero_iff` +
    `hAlphaEvals_rowPoint`, arity pin `n ≤ 2 ^ m₁`);
  - **shortness `liftShort` from `H₀ ≡ 0`** (`hZero_eq_zero_imp_liftShort`): every committed
    coefficient is a table entry (`wTable_zRow`/`wTable_rRow`), hence a root of the range factor
    `P_b`, hence a centered residue of absolute value `≤ b − 1`
    (`valMinAbs_natAbs_le_of_rangeProduct_eq_zero`, using injectivity of `φF` on `ZMod q`). This is
    resolution *option 1*: shortness is **derived**, not assumed. The reconciliation with
    `liftShort`'s two bounds is the pair of hypotheses `b − 1 ≤ γ` (z-side) and `b − 1 ≤ ρBound`
    (r-side), together with the column-encoding arity
    `(μ+n)·deg φ ≤ 2^{m₀}`; these are threaded through `batchPackage` and `openCore`.
  `K.com` and the bound conjunct are carried verbatim. That `hAlpha` is the polynomial constructed
  in paper Eq. (22) is proved separately by `alphaDefect_wTable` /
  `hAlpha_eq_zero_iff_alphaDefect`. **Still missing:** the forward/honest-completeness theorem
  `relLiftE → relBatchedE`.
- **Constructivity.** `buildNestedWitnessE` (and the leaf selection `nestedPathResponse`, like
  the generic `treeExtractor`) select per-branch witnesses with classical choice. A constructive
  extractor would need witness-bearing trees or a decidable enumeration interface.
- **Sumcheck seam.** `nestedRoundRel` carries the `liftShort` conjunct, and the sumcheck
  bridge's pull-back `mem_relNestedZeroCheckE_of_nestedRoundRelE` is now **proved** — but
  `#print axioms` shows it inherits `sorryAx` from the two `sorry` sum identities above, so the
  bridge is only as discharged as F5. Further down the chain (out of Lemma-10 scope), the
  per-round CWSS `round_coordinateWiseSpecialSound` (Lemma 11, milestone F7) and the
  final-evaluation step (`finalCheck` / `finalEval_coordinateWiseSpecialSound`, milestone F8)
  remain `sorry`.

## Resolution options (for the record)

1. **[adopted at the batching bridge]** derive shortness from the range identity `H₀ ≡ 0`
   (`hZero_eq_zero_imp_liftShort`), so `relBatched` does not carry a shortness conjunct;
2. **[temporary at point/sumcheck seams]** keep `liftShort` as a relation conjunct so differing
   openings are known short before invoking weak binding;
3. redesign the composed extraction interface so the collision seam consumes downstream
   witness/extractor evidence constructively, or strengthen the binding interface. Directly
   deriving shortness from a point claim is unavailable (a nonzero multilinear polynomial
   vanishing at any single point always exists — see "Why the point evaluation is insufficient"
   above), and weakening `collision_mem` is unsound.
