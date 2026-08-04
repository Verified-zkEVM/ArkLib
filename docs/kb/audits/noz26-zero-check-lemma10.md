# NOZ26 Figure 5 / Lemma 10 audit

This page records the specification boundary for link 6 of ArkLib's Hachi opening chain. It is
based on the January 30, 2026 ePrint version of Nguyen–O'Rourke–Zhang, *Hachi: Efficient
Lattice-Based Multilinear Polynomial Commitments over Extension Fields* (`NOZ26`, §4.3,
Figure 5 and Lemma 10).

Last revalidated against the formalization: **31 July 2026**.

> **Status (integrated; link-5 completeness direction still open).** The corrected Lemma 10 is now formalized
> *inside* the escape-threaded
> opening chain: `zeroCheckPackage` reduces `relBatchedE → relZeroCheckE` and is composed as
> `batchPackage ▷ zeroCheckPackage ▷ sumcheckBridgePackage` in `Composition.lean` (`openCore`).
> The CWSS theorem `zeroCheck_coordinateWiseSpecialSound` is **`sorry`-free and axiom-clean** (the
> `H_α`/`H₀` values used by the theorem are concrete), and the link-5 batching bridge's
> un-batching pull-back `mem_relLiftE_of_relBatchedE` is likewise **proven and axiom-clean relative
> to those definitions**. **Paper Eq. (22) is now formalized**: `mAlphaTilde` (`M̃_α`),
> `alphaTilde` (`α̃`) and `alphaContract` build the paper's public contraction against the committed
> table, and `alphaDefect_wTable` / `hAlpha_eq_zero_iff_alphaDefect` prove it equal to the per-row
> defect that `hAlphaEvals` writes down directly (axiom-clean). The residual link-5 obligation is
> the forward/honest-completeness theorem `relLiftE → relBatchedE`, which is still absent.
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
| Batched row identity, Eq. (22) | `ZeroCheck.hAlpha : CMlPolynomialEval F m₁` | represented, **concrete, computable, paper-faithful** | The stored vector is the per-row defect table `hAlphaEvals`, so multilinearity and the pull-back are structural. The paper's route through the `M̃_α`/`w̃`/`α̃` contraction is built separately (`mAlphaTilde`, `alphaTilde`, `alphaContract`, `alphaDefect`) and proved equal to that table by `alphaDefect_wTable`, with the relation-level form `hAlpha_eq_zero_iff_alphaDefect`. |
| Eq. (22) contraction ↔ row defect | `ZeroCheck.alphaDefect_wTable`, `hAlphaEvals_eq_alphaDefect`, `hAlpha_eq_zero_iff_alphaDefect` | proven, **axiom-clean** | §4.3's "represent the constraints by polynomials" step: the only place the table encoding of the witness (commitment/sumcheck side) meets the ring encoding (`relLift` side). Arity pins `hd : 0 < deg φ` and `(μ+n)·deg φ ≤ 2^{m₀}`; the `Rq` column bound is `CyclotomicModulus.natDegree_lt_of_reduced`. |
| Figure-5 point checks | `ZeroCheck.relZeroCheck` / `relZeroCheckE` | deliberately repaired | Points are derived from scalar Kronecker seeds, not sampled uniformly as vectors; evaluation uses `CMlPolynomialEval.eval` directly; escape-threaded (`Set.withEscape K.esc`). |
| Axis-cross counterexample | `LinearMvExtension.exists_nonzero_vanishing_on_axis_cross` | proven | Formally refutes the identity-testing step used by the uniform-vector argument. |
| Kronecker root-counting kernel | `LinearMvExtension.multilinear_eq_zero_of_kronecker_roots`, `ZeroCheck.arm_eq_zero_of_family` | proven, **axiom-clean** | `D ≥ 2^m` univariate roots + Kronecker injectivity; no `sorryAx`. |
| Lemma-10 extraction (escape-threaded) | `ZeroCheck.buildWitnessE`, `buildWitnessE_mem_relBatchedE` | proof-sorry-free | Escape pass-through ∨ weak-binding collision ∨ common opening with both identities zero. |
| Lemma-10 binding alternative | `LiftCom.escOfCollision` via `K.collision_mem` | integrated | Distinct short openings of the shared `t` become an escape `e ∈ K.esc` (Hachi weak binding). |
| Corrected Lemma 10 CWSS | `ZeroCheck.zeroCheck_coordinateWiseSpecialSound` | sorry-free, **axiom-clean** | `(ℓ, k) = (2, D)`; assembled by `ChallengeRoundTree.coordinateWiseSpecialSound_of_mkWitness`; `#print axioms` = `propext`/`Classical.choice`/`Quot.sound` only. |
| Link-5 un-batching pull-back | `ZeroCheck.mem_relLiftE_of_relBatchedE` (`batchPackage`) | **the theorem is proven and axiom-clean; paper correspondence is partial** | `relBatchedE → relLiftE`; `H_α ≡ 0 ⇒` per-row eqs via `hAlpha_eq_zero_iff` + `hAlphaEvals_rowPoint` (arity pin `n ≤ 2 ^ m₁`); **`H₀ ≡ 0 ⇒ liftShort`** via `hZero_eq_zero_imp_liftShort` (arity pin `(μ+n)·deg φ ≤ 2^{m₀}`, `hd`, range-base fits `b−1 ≤ γ`, `b−1 ≤ ρBound`). The obligation to derive the `H_α` table from paper Eq. (22) is discharged separately by `alphaDefect_wTable`; what remains missing for link 5 is only the forward/honest-completeness direction. |
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
| `H_α`, Eq. (22) | `hAlpha : CMlPolynomialEval F m₁` | `hAlphaML` | `hAlpha_eq_zero_iff`, `hAlphaML_eq_zero_iff` |
| Public matrix `M̃_α`, power vector `α̃` | `mAlphaTilde`, `alphaTilde` | — | `alphaDefect_wTable` (contraction = row defect), `hAlpha_eq_zero_iff_alphaDefect` |
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
the paper's `O(d + b)` to `O(μ·d)` — and, more importantly, the soundness error degrades. For a
nonzero `H₀` the univariate pullback `powAlgHom H₀` has degree `≤ 2^{m₀} − 1`, so a seed lands on a
root with probability up to `2^{m₀}/|F_{q^k}|`. At the paper's Figure 9 parameters (`q ≈ 2^32`,
`k = 4` so `|F_{q^k}| ≈ 2^128`; `deg φ = 2^10` and `w̃` length `≤ 2^26`, hence `m₀ ≈ 26`, which is
also what `hμn` pins) that is `≈ 2^-102`, against `≈ 2^-123` for Figure 5's uniform `τ₀` by
Schwartz–Zippel — a **~21-bit regression** on a `λ = 128` target.

Buying those bits back is not cheap. `k` must divide `d/2 = 512` ([NOZ26] Lemma 1 / Theorem 1), so
`k` is a power of two: `k = 5` would suffice numerically but is illegal, and the next legal value is
`k = 8`. The paper's sumcheck cost `26·k·32·(16+2)` bits `≈ 7.3 KB` at `k = 4` then becomes
`≈ 14.6 KB`, i.e. **double**, plus `F_{q^8}` arithmetic throughout.

Two accounting notes, since both are easy to get wrong:

- [NOZ26] Lemma 4's `ℓ·k/|S|^ℓ` must **not** be read as `2·D/|F_{q^k}|²` here. `H₀` depends only on
  `ρ₀` and `H_α` only on `ρ_α`, so a cheating prover needs one seed bad, not both; the `|S|^ℓ`
  denominator would price in an independence the protocol does not have. A knowledge error below the
  direct `2^{m₀}/|F_{q^k}|` bound is in any case impossible, since knowledge error dominates the
  success probability of a witness-less prover.
- The comparison baseline is Figure 5's Schwartz–Zippel error `m₀/|F_{q^k}|`, not
  `2·max(2d, 2b−1)/|F_{q^k}|²`; the latter mixes the paper's `D` with a denominator that does not
  apply.

No bound better than `2^{m₀}/|F_{q^k}|` is currently proved for this reparametrisation, and whether
a *realisable* table attains it is open: `exists_nonzero_multilinear_vanishing_on_kronecker_seeds`
gives tightness for arbitrary multilinears, but a protocol adversary must exhibit an `H₀` of the
form `∑ᵢ eq̃(t,i)·P_b(w̃(i))`, which that lemma does not construct.

What the repair buys in exchange is a *deterministic* identity equivalence
(`multilinear_eq_zero_of_kronecker_roots`), which is what the printed Lemma 10's root-counting step
needed and did not have. Whether that trade is the right one is a protocol question for the paper's
authors rather than a formalization question, and it is **not settled here**.

### Alternative repair routes under discussion (not yet claims)

The axis-cross gap was raised with the [NOZ26] authors directly, and this subsection records the
state of that correspondence. It is **not** a set of established results: nothing below is
formalized in ArkLib, and the statements are the authors' and our suggestions, not theorems.

In a reply of 2026-07-31, George O'Rourke confirmed the diagnosis — that Schwartz–Zippel cannot be
invoked under CWSS, because the CWSS tree constrains only the coordinate-wise structure of the
challenges and says nothing about their distribution — and also noted that the printed analysis
takes `(τ₀, τ₁)` as a two-coordinate vector even though the two coordinates are drawn from
`F_{q^k}^{log μ + log d}` and `F_{q^k}^{log n}`, neither of which is `F_{q^k}`. Two alternatives
were proposed there, both of which leave Figure 5's protocol unchanged:

1. drop CWSS for this step and argue knowledge soundness directly by Schwartz–Zippel, at the cost
   of no longer being able to compose the chain through a single generic CWSS-to-knowledge-soundness
   step;
2. treat each coordinate of `(τ₀, τ₁)` as a separate challenge round and prove plain
   `(k, …, k)`-special soundness by root counting with induction on the number of variables.

Route 2 looks the more promising one for this formalization, since it would keep the error at
Figure 5's order (`≈ 2^-122` by [NOZ26] Lemma 4 at `ℓᵢ = 1`, `kᵢ = 2`, summed over the
`log(μ + n) + log d + log n` coordinates) while still landing on a CWSS-shaped notion. Two caveats
before anyone relies on that: the required multivariate root-counting lemma is **not** in the tree,
and the relevant per-coordinate degree is `1` (both `H₀` and `H_α` are multilinear *in the
challenge*; the `2b − 1` and `2` appearing in the paper are witness-side sumcheck degrees), so the
per-coordinate parameter would be `k = 2` rather than the larger values a first reading suggests.

Until the authors settle the route, treat the Kronecker reparametrisation in this file as
provisional. Also recorded in the `zeroCheckD` docstring.

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
  `K.com` and the bound conjunct are carried verbatim. That `hAlpha` is the polynomial constructed
  in paper Eq. (22) is proved separately by `alphaDefect_wTable` /
  `hAlpha_eq_zero_iff_alphaDefect`. **Still missing:** the forward/honest-completeness theorem
  `relLiftE → relBatchedE`.
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
