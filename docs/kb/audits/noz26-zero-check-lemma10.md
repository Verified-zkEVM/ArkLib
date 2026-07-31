# NOZ26 Figure 5 / Lemma 10 audit

This page records the specification boundary for link 6 of ArkLib's Hachi opening chain. It is
based on the January 30, 2026 ePrint version of Nguyen–O'Rourke–Zhang, *Hachi: Efficient
Lattice-Based Multilinear Polynomial Commitments over Extension Fields* (`NOZ26`, §4.3,
Figure 5 and Lemma 10).

Last revalidated against the formalization: **30 July 2026**.

> **Status (integrated, with a link-5 encoding gap).** The corrected Lemma 10 is now formalized
> *inside* the escape-threaded
> opening chain: `zeroCheckPackage` reduces `relBatchedE → relZeroCheckE` and is composed as
> `batchPackage ▷ zeroCheckPackage ▷ sumcheckBridgePackage` in `Composition.lean` (`openCore`).
> The CWSS theorem `zeroCheck_coordinateWiseSpecialSound` is **`sorry`-free and axiom-clean** (the
> `H_α`/`H₀` values used by the theorem are concrete), and the link-5 batching bridge's
> un-batching pull-back `mem_relLiftE_of_relBatchedE` is likewise **proven and axiom-clean relative
> to those definitions**. Link 5 is nevertheless **not yet a faithful formalization of paper
> Eq. (22)**: `hAlphaEvals` is defined directly as the target per-row lift defect. The paper's
> contraction from `M̃_α`, `w̃`, and `α̃`, and a theorem proving that contraction equal to the
> defect, are absent. The package also has no forward/honest-completeness theorem
> `relLiftE → relBatchedE`.
> **The range half is now load-bearing:** shortness (`liftShort`) is *derived* from the range
> identity `H₀ ≡ 0` at the batching bridge (`hZero_eq_zero_imp_liftShort`, resolution *option 1*),
> not carried as a free conjunct of `relBatched`.
>
> **Temporary point-seam assumption.** `relZeroCheck` and `roundRel` carry `liftShort` as a
> semantic admissibility conjunct. This is needed by the norm-conditioned weak-binding escape
> `K.collision_mem`: a single point evaluation or partial-sum claim cannot establish that an
> individual colliding opening is short. These relations do not carry the global identity
> `H₀ ≡ 0`; the zero-check still extracts that identity by root counting in the common-opening
> branch. At the batching bridge, shortness remains derived from `H₀ ≡ 0`, not assumed.
>
> All declarations live in the chain's namespace
> `ArkLib.Lattices.Ajtai.InnerOuter` (`Hachi/ZeroCheck/{Constraints,Batch,Reduction}.lean`); the
> generic engine is `OracleReduction/…/CoordinateWiseSpecialSoundness/ChallengeRoundTree.lean`.

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
| Batched row identity, Eq. (22) | `ZeroCheck.hAlpha : CMlPolynomialEval F m₁` | **partial / specification shortcut** | The stored vector is the per-row defect table `hAlphaEvals`, so multilinearity and the pull-back are proved. But the paper defines this identity through the `M̃_α`/`w̃`/`α̃` contraction. That contraction and its equivalence to the direct defect table are not formalized. |
| Figure-5 point checks | `ZeroCheck.relZeroCheck` / `relZeroCheckE` | deliberately repaired | Points are derived from scalar Kronecker seeds, not sampled uniformly as vectors; evaluation uses `CMlPolynomialEval.eval` directly; escape-threaded (`Set.withEscape K.esc`). |
| Axis-cross counterexample | `LinearMvExtension.exists_nonzero_vanishing_on_axis_cross` | proven | Formally refutes the identity-testing step used by the uniform-vector argument. |
| Kronecker root-counting kernel | `LinearMvExtension.multilinear_eq_zero_of_kronecker_roots`, `ZeroCheck.arm_eq_zero_of_family` | proven, **axiom-clean** | `D ≥ 2^m` univariate roots + Kronecker injectivity; no `sorryAx`. |
| Lemma-10 extraction (escape-threaded) | `ZeroCheck.buildWitnessE`, `buildWitnessE_mem_relBatchedE` | proof-sorry-free | Escape pass-through ∨ weak-binding collision ∨ common opening with both identities zero. |
| Lemma-10 binding alternative | `LiftCom.escOfCollision` via `K.collision_mem` | integrated | Distinct short openings of the shared `t` become an escape `e ∈ K.esc` (Hachi weak binding). |
| Corrected Lemma 10 CWSS | `ZeroCheck.zeroCheck_coordinateWiseSpecialSound` | sorry-free, **axiom-clean** | `(ℓ, k) = (2, D)`; assembled by `ChallengeRoundTree.coordinateWiseSpecialSound_of_mkWitness`; `#print axioms` = `propext`/`Classical.choice`/`Quot.sound` only. |
| Link-5 un-batching pull-back | `ZeroCheck.mem_relLiftE_of_relBatchedE` (`batchPackage`) | **the theorem is proven and axiom-clean; paper correspondence is partial** | `relBatchedE → relLiftE`; `H_α ≡ 0 ⇒` per-row eqs via `hAlpha_eq_zero_iff` + `hAlphaEvals_rowPoint` (arity pin `n ≤ 2 ^ m₁`); **`H₀ ≡ 0 ⇒ liftShort`** via `hZero_eq_zero_imp_liftShort` (arity pin `(μ+n)·deg φ ≤ 2^{m₀}`, `hd`, range-base fits `b−1 ≤ γ`, `b−1 ≤ ρBound`). The missing obligation is to derive the current `H_α` table from paper Eq. (22), not the already-proved pull-back from that table. |
| Link-5 forward/completeness direction | no declaration | **missing** | There is no theorem showing that an honest `relLiftE` witness satisfies `relBatchedE`, nor an honest-completeness result for `batchPackage`. This is separate from CWSS, whose direction only needs the pull-back. |
| Link-5/link-6/link-7 composition | `batchPackage ▷ zeroCheckPackage ▷ sumcheckBridgePackage` (`openCore`) | **defined, compiles as a CWSS chain** | The seam relations match by `rfl`. This does not close link 5's paper-encoding or honest-completeness obligations. |

## Polynomial representation: multilinear value vectors and proof views

The two batched identities now use CompPoly's native Boolean-evaluation representation
`CMlPolynomialEval F m = Vector F (2 ^ m)`. This matches Eqs. (22)–(23): each entry is one
Boolean-cube constraint value, and the vector represents its unique multilinear extension.
Multilinearity is therefore guaranteed by the type rather than proved with `degreeOf` lemmas.

The Kronecker algebra remains phrased over Mathlib's `MvPolynomial.restrictDegree`. The derived
views `hZeroML` and `hAlphaML` rebuild the same value tables with `MvPolynomial.MLE`;
`hZeroML_eq_zero_iff` and `hAlphaML_eq_zero_iff` connect those proof views to the primary vectors.

| Object | Computable definition | Mathlib view | Bridge lemma |
| --- | --- | --- | --- |
| Witness ring | `Rq Φ = {p : CPolynomial (ZMod q) // Φ.reduce p = p}` | `Φ.CyclotomicRing` | `Rq.toQuotient` |
| Quotients `rᵢ` | `LiftedWitness.r : Fin n → CPolynomial (ZMod q)` | `(r i).toPoly` | `CPolynomial.coeff_toPoly` |
| Row sum `∑ⱼ Mᵢⱼzⱼ` | `cRowSum` | `rowSum` | `rowSum_eq_sum_toPoly` |
| Evaluation at `α` | `cEvalAt` (`CPolynomial.eval₂`) | `evalAt` (`eval₂RingHom`) | `cEvalAt_cRowSum_eq_evalAt`, `cEvalAt_eq_evalAt_toPoly` |
| Range factor `P_b` | `rangeProduct` (scalar) | — | `rangeProduct_eq_zero_iff` |
| Table `w̃`, Eq. (21) | `wTable` | — | `wTable_zRow`, `wTable_rRow` |
| `H₀`, Eq. (23) | `hZero : CMlPolynomialEval F m₀` | `hZeroML` | `hZero_eq_zero_iff`, `hZeroML_eq_zero_iff` |
| `H_α` defect-table specification (intended to represent Eq. (22)) | `hAlpha : CMlPolynomialEval F m₁` | `hAlphaML` | `hAlpha_eq_zero_iff`, `hAlphaML_eq_zero_iff`; no bridge from the paper's `M̃_α`/`w̃`/`α̃` contraction |
| `mle[w̃]` and its opening | `cWTableMle`, `wTableMleEval` | — | `wTableMleEval_eq` |
| Round message `(g⁽⁰⁾, g⁽ᵅ⁾)` | `CPolynomial.degreeLE` subtypes | `Polynomial.degreeLE` | `CPolynomial.degreeLE_toPoly` |

Consequences worth recording:

- **The full identities are computable vector equalities.** `relBatched` states
  `hZero … = 0 ∧ hAlpha … = 0`; both sides are fixed-length CompPoly vectors, not sparse
  `Finsupp` polynomials.
- **The Mathlib views are proof-only.** `hZeroML`/`hAlphaML` are noncomputable derived definitions
  used by Kronecker root counting and the current sumcheck identity specifications. `relZeroCheck`
  evaluates the primary vectors directly; `hZero_eval_eq`/`hAlpha_eval_eq` cross to the Mathlib
  views inside the extraction proof, while their zero identities remain equivalent to the primary
  vector identities.
- **Still stubs, hence not computable in substance.** The sumcheck summands
  `sumcheckPolyZero`, `sumcheckPolyAlpha`, the public target `zcTargetAlpha` and the prover fold
  `hypercubeSum` have CompPoly *types* (`CMvPolynomial m₀ F`, `F`) but `sorry` bodies, as do
  `sum_sumcheckPolyZero`/`sum_sumcheckPolyAlpha` (milestone F7). Their intended computable shapes
  are `F_{0,τ₀} = eq̃(τ₀, ·) · P_b(mle[w̃])` (per-variable degree `2b = roundDegZero b`) and
  `F_{α,τ₁} = eq̃(τ₁, ·) · (mle[rowSum(α)] − φ(α)·mle[r(α)])` (per-variable degree
  `2 = roundDegAlpha`), with `zcTargetAlpha = ∑ᵢ eq̃(τ₁, i)·yᵢ(α)` accounting for the public
  right-hand side.
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

ArkLib's repair samples scalar seeds `ρ₀, ρα` and evaluates on Kronecker curves
`κ_m(ρ) = (ρ, ρ², ρ⁴, ...)`. A multilinear polynomial pulls back injectively to a univariate
polynomial of degree below `2^m`; `2^m` distinct seeds then determine the identity. This changes
the challenge distribution and raises the soundness parameter to `D = max(2, 2^{m₀}, 2^{mα})`.

### What the repair costs

Because `hμn` pins `2^{m₀} ≥ (μ + n)·deg φ`, the branching arity of the extraction tree grows from
the paper's `O(d + b)` to `O(μ·d)`. This is the obvious objection to the repair and the answer is
favourable. By [NOZ26] Lemma 4 the knowledge error of a coordinate-wise special-sound family is
`ℓ·k/|S|^ℓ`, so at `(ℓ, k) = (2, D)` over `S = F_{q^k}` it is `2·D/|F_{q^k}|²`, i.e. roughly
`2(μ + n)d/|F_{q^k}|²` in place of `2·max(2d, 2b−1)/|F_{q^k}|²`. That is still negligible at Hachi's
field size, and `D` is polynomial in the witness dimensions so the transcript tree stays polynomial.
What the repair buys in exchange is a *deterministic* identity equivalence
(`multilinear_eq_zero_of_kronecker_roots`), strictly stronger than the Schwartz–Zippel bound Lemma 10
actually needed. Recorded in the `zeroCheckD` docstring.

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
  `2D − 1` transcripts. `2D − 1` is what `zeroCheckStructure` uses, through `chalStructure`'s
  `arity = ℓ·(k−1)+1`.
- **`ℓ = 2`, not `log μ + log d + log n`.** The prose immediately above Lemma 10 says to treat
  `(τ₀, τ₁)` as `log μ + log d + log n` coordinates, contradicting the lemma's own `ℓ = 2`. ArkLib
  follows `ℓ = 2`, the two coordinates being the scalar seeds `(ρ₀, ρ_α)`.
- **`τ₀` arity on p. 20.** `τ₀` is drawn from `F^{log μ + log d}` although `w̃`'s domain is
  `[μ + n] × [d]`, so the paper's arity there should read `log(μ + n) + log d`. ArkLib's `m₀` is
  pinned to the latter by `hμn`.

The last three are recorded in the `zeroCheckD` docstring.

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
short. But `relZeroCheck` (and the sumcheck round relation `roundRel`) only pin *point*
evaluations `H₀(κ(ρ₀)) = 0` — one point on a Kronecker curve per accepting branch. A single point
does **not** recover `H₀ ≡ 0` for that opening (that needs the whole `≥ 2^{m₀}`-seed family to
share one opening, which is exactly the *non*-collision case). So the two colliding openings'
shortness cannot be derived from the checks, so `relZeroCheck`/`roundRel` carry the `liftShort`
conjunct for now. This is completeness-preserving (the honest `w̃` is short) and is
*resolution option 2*.

**Why the point evaluation is insufficient.** A single accepting branch pins only
`H₀^{w̃}(κ_{m₀}(ρ₀)) = 0`, and shortness is *not* derivable from that: recovering `H₀ ≡ 0` for one
opening needs `2^{m₀}` distinct seeds sharing it (`multilinear_eq_zero_of_kronecker_roots`), and that
count is sharp — `LinearMvExtension.exists_nonzero_multilinear_vanishing_on_kronecker_seeds` builds,
for **any** `2^{m₀} − 1` seeds, a nonzero multilinear vanishing at all of them. Since the CWSS family
is a star (centre plus `D − 1 = 2^{m₀} − 1` siblings per coordinate), the collision branch of
`buildWitnessE` can never assemble enough seeds for a *single* colliding opening.

Consequently the temporary fix is to state shortness explicitly at these seams. The range
identity of `relBatched` is still discharged by Kronecker root counting over the family
(`arm_eq_zero_of_family`), so the zero-check retains its intended content. Removing the temporary
shortness assumption requires either unconditional binding or an extraction interface that
supplies admissibility evidence before the collision branch.

## Residual gaps (out of Lemma-10 scope)

- **F5 encoding — concrete values, but incomplete paper correspondence.** `hZero`/`hAlpha` are
  genuine multilinear extensions, and both coefficient functions are concrete (no longer
  `sorry`):
  - `hAlphaEvals` = the `α`-evaluated per-row lift defect, row-encoded into the `m₁`-cube via
    `rowPoint` (`hAlphaEvals_rowPoint`, axiom-clean); arity pin `n ≤ 2 ^ m₁`. This is a direct
    specification of the desired result, not yet a formalization of the paper's Eq. (22)
    contraction. A definition of that contraction and an extensional-equality theorem are still
    required.
  - `wTable` reads the committed `z`/`r` coefficients **directly** (decoding the `m₀`-cube to
    `row := idx / d`, `col := idx % d`), so `H₀ ≡ 0` is a genuine (non-vacuous) shortness statement
    on the committed data. (Re-decomposing to base-`b` digits would be vacuous — digits are always
    in range by construction; the paper's gadget decomposition is the honest prover's pre-commit
    step, not part of the range test.)

  Consequently `zeroCheck_coordinateWiseSpecialSound` is now **axiom-clean**: `#print axioms` reports
  no `sorryAx` (only ambient `propext`/`Classical.choice`/`Quot.sound`; the `Classical.choice` is the
  constructivity caveat below, from `buildWitnessE`'s branch selection). The standalone kernel
  `arm_eq_zero_of_family` is axiom-clean. **Range-side soundness `H₀ ≡ 0 ⇒ liftShort` is now
  proven** (`hZero_eq_zero_imp_liftShort`, see Link 5) — no longer an F5 gap. **Still F5 (out of
  Lemma-10 scope):** the sumcheck-summand stubs (`sumcheckPoly*`, `hypercubeSum`, `sum_*`).
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
  `K.com` and the bound conjunct are carried verbatim. This proves the CWSS direction for the
  current relation, but does not prove that `hAlpha` is the polynomial constructed in paper
  Eq. (22). There is also no forward/honest-completeness theorem `relLiftE → relBatchedE`.
- **Constructivity.** `buildWitnessE` (and the generic `treeExtractor`) select per-branch
  witnesses with classical choice. A constructive extractor would need witness-bearing trees or a
  decidable enumeration interface.
- **Sumcheck seam.** `roundRel` now carries the `liftShort` conjunct, but the sumcheck bridge's
  pull-back `mem_relZeroCheckE_of_roundRelE` that must re-supply it remains a skeleton `sorry`
  (milestone F7).

## Resolution options (for the record)

1. **[adopted at the batching bridge]** derive shortness from the range identity `H₀ ≡ 0`
   (`hZero_eq_zero_imp_liftShort`), so `relBatched` does not carry a shortness conjunct;
2. **[temporary at point/sumcheck seams]** keep `liftShort` as a relation conjunct so differing
   openings are known short before invoking weak binding;
3. redesign the composed extraction interface so the collision seam consumes downstream
   witness/extractor evidence constructively, or strengthen the binding interface. Directly
   deriving shortness from a point claim is provably unavailable (see the sharpness theorem
   above), and weakening `collision_mem` is unsound.
