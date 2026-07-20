# Why Hachi's Ring Switch + Sumcheck Is a Different Protocol Than `ArkLib/ProofSystem/RingSwitching/`

## 1. The intuition in one paragraph

Both protocols exist to solve the same headache: a polynomial is **committed over a small ring**,
but the claim you need to verify lives **in a big ring**. The formalized protocol
(`ProofSystem/RingSwitching/`, following DP24/Binius) solves it the *hard, interactive* way,
because in its setting the evaluation point is scattered across the big ring: it must fold the
claim with a **fresh random challenge** and then run a **dedicated sumcheck** just to move the
claim onto the packed polynomial — paying interaction rounds and soundness error for the
privilege. Hachi never has this problem, because it arranges for the evaluation point to lie
inside the *small* ring: the same reduction then collapses to a **single algebraic identity**
(the trace formula), needing one prover message, zero challenges, zero rounds of sumcheck, and
zero soundness error. Hachi does still run a sumcheck later — but that sumcheck proves a
*different statement* (linear relations + norm bounds of the commitment opening), over a
*different ring*, with a *different soundness argument*. So the two constructions overlap in
their algebra (packing basis, embeddings — the `RingSwitchingProfile` data), and in nothing that
is on the wire.

Slogan: **same algebra, different protocol.** The formalized module's *protocol* half
(`BatchingPhase`, `SumcheckPhase`, `General`) is the interactive machinery DP24 needs and Hachi
deliberately avoids; its *data* half (`Profile`, `packMLE`) is exactly what Hachi reuses.

## 2. Three things called "ring switching" — keep them apart

| | Direction | Mechanism | Where |
|---|---|---|---|
| **DP24 / ArkLib module** | small field `B` → large field `L` (for the opening) | pack, then *interactive*: fold `ŝ` + batching challenge + packing sumcheck | `ProofSystem/RingSwitching/` |
| **Hachi §3** | extension field `F_{q^k}` → cyclotomic ring `R_q` | pack via ψ, then *deterministic*: one message `Y` + trace check | Hachi paper §3, Thm 2 |
| **Hachi §4.3 (HMZ25)** | cyclotomic ring `R_q` → extension field `F_{q^k}` | lift `Mz = y` to `Z_q[X]`, evaluate at random `α ← F_{q^k}` | Hachi paper §4.3, Fig. 4 |

The formalized module corresponds to row 1. Hachi's "ring switch + sumcheck" subprotocol is rows
2 and 3 glued together — and neither row runs row 1's protocol.

## 3. What the formalized protocol actually does, and why each move exists

Setting of `ProofSystem/RingSwitching/` (DP24 §3): `t` is a multilinear committed over the small
field `B`; the claim is `t̃(r) = s` where the point `r` lives in `L^ℓ` — **arbitrary big-field
coordinates**. The packed polynomial `t' = packMLE(t)` (over `L`, with `ℓ − κ` variables) is what
the big-field PCS can open, so the whole job is: *turn a claim about `t` at `r` into a claim
about `t'` at some point.* Because `r` is arbitrary, there is no algebraic shortcut, and the
protocol earns its reduction interactively:

1. **Batching phase** (`BatchingPhase.lean`): the prover sends a folded element `ŝ` in a carrier
   algebra `A` (for Binius: `L ⊗_B L`). The verifier checks `s` against `ŝ`'s column
   decomposition, then sends a **random batching challenge** `r'' ∈ L^κ` that collapses the `2^κ`
   packed coordinates into one sumcheck target. Cost: one round, `κ/|L|` soundness error.
2. **Sumcheck phase** (`SumcheckPhase.lean`): a **degree-2** sumcheck over `L`, `ℓ − κ` rounds,
   on the specific polynomial `eq̃ · t'` (multiplier `compute_A_func`, built from the profile
   basis), ending in an `eq̃`-tensor consistency check (`compute_final_eq_value`). Cost: `2/|L|`
   per round + `1/|L|`.
3. **Opening**: the residual claim `t'(r') = s'` at the *random* point `r'` produced by the
   sumcheck goes to the underlying big-field PCS (`mlIOPCS` parameter in `General.lean`).

Note what the sumcheck is *for* here: it exists **only to relocate the evaluation claim** from
`t` at `r` to `t'` at a fresh random point. It proves nothing else. Its soundness is
Schwartz–Zippel, hence the `[IsDomain L]` hypothesis on every soundness theorem in the module.

## 4. What Hachi does instead — step by step

### 4a. Hachi's packing reduction (§3) needs no protocol at all

Hachi's evaluation point `x ∈ (R_q^H)^ℓ` lies in the **small** field (the subfield
`R_q^H ≅ F_{q^k}` inside `R_q`). That one assumption deletes the entire interactive pipeline:

- Pack the coefficients: `F_i := ψ(f-blocks)`, and pack the tail-of-point monomials:
  `v := ψ(tail monomials)` — both *computable from public data + the witness*, no interaction.
- The prover sends **one ring element** `Y` (the claimed value of the packed polynomial `F` at
  the head of the point).
- The verifier checks **one equation**: `Tr_H(Y · σ₋₁(v)) = (d/k)·y` (Theorem 2's trace
  identity).
- Remaining claim: "`F` evaluates to `Y`" — handed to the `R_q`-level PCS (the already-formalized
  Fig. 3 / Lemma 8 chain).

Message-by-message comparison of the *reduction step itself*:

| | ArkLib `FullRingSwitching` | Hachi §3 |
|---|---|---|
| Prover sends | `ŝ ∈ A` (carrier element) | `Y ∈ R_q` |
| Verifier challenge | `r'' ∈ L^κ` (batching) | — none |
| Extra sumcheck | `ℓ − κ` rounds, degree 2 | — none |
| Verifier check | column-decomposition + `eq̃`-tensor final check | one trace equation |
| Soundness cost | `κ/|L| + Σ 2/|L| + 1/|L|` | **0** (deterministic) |

Why can Hachi get away with this and Binius cannot? Two reasons, both parameter-driven:

- Binius's point is genuinely a big-field point (it comes out of FRI-style machinery), so the
  algebraic shortcut is unavailable. Hachi *chooses* its statement so the point is subfield-valued.
- Where Hachi does need to peel off packed coordinates (§3.2), it just **sends the `k − 1`
  partial evaluations in the clear** — affordable because Hachi's packing factor is tiny
  (`k = 4` at the paper's parameters, Fig. 9). Binius packs `2^κ ≫ k` coefficients per big-field
  element; sending `2^κ` partial evaluations would blow up the proof, which is *why* DP24 invented
  the batching-challenge + sumcheck route in the first place.

So instantiating `FullRingSwitching` for Hachi §3 would not be "formalizing Hachi with reused
code" — it would be formalizing a **different protocol** (different transcript: a carrier
element, a challenge, and `ℓ − κ` sumcheck rounds that Hachi never sends), with strictly worse
costs, that no longer matches any figure or lemma of the paper.

### 4b. Hachi's actual sumcheck (§4.3) proves a different statement

Hachi *does* contain a sumcheck — but look at what it is for. After Fig. 3, the prover must show
its committed opening satisfies the linear system of Eq. (20) **and** that the witness
coefficients are small. §4.3 does this by:

1. **The HMZ25 lift (Fig. 4)**: rewrite `Mz = y` over `R_q` as `Mz = y + (X^d + 1)·r` over
   `Z_q[X]`, and evaluate everything at a random `α ← F_{q^k}`. This is the *opposite-direction*
   ring switch (ring → field), and it costs a `(2d−1)/q^k` soundness error (Lemma 9). Nothing in
   `ProofSystem/RingSwitching/Packing/` performs or models this move (the generic
   formalization of the move itself is `ProofSystem/RingSwitching/Lift/` — see §7).
2. **Batch + sumcheck over `F_{q^k}` (Figs. 5–7)**: the constraints — including the range
   constraint `w̃·(w̃−1)(w̃+1)···(w̃−b+1)(w̃+b−1) = 0` — are `eq̃`-batched into `H_0, H_α` and
   proven by sumcheck.

Compare that sumcheck to the one in `SumcheckPhase.lean`, item by item:

| | `RingSwitching/Packing/SumcheckPhase` | Hachi §4.3 sumcheck |
|---|---|---|
| Purpose | relocate an evaluation claim onto the packed `t'` | prove **linear relations + norm bounds** of an opening |
| Polynomial | `eq̃ · t'`, hardwired via `compute_A_MLE` | `F_{0,τ₀}` (range product), `F_{α,τ₁}` (constraint poly `M̃_α`) |
| Per-round degree | pinned to **2** (`combinator := X`) | **`2b + 1`** (the range product) |
| Final round | `eq̃`-tensor check (`compute_final_eq_value`) | evaluate `M̃_α`, check sumcheck consistency |
| Ring | `L` (in Hachi's dictionary that would be `R_q` — **not a domain**) | `F_{q^k}` (a genuine field) |
| Soundness style | RBR knowledge soundness, `[IsDomain L]`, currently `sorry` | CWSS / special soundness (Lemmas 10–11, Fig. 6 single-round view) |

Not one row matches. The *shared* ingredient — "rounds of univariate polynomials + challenges" —
lives one level below, in `ArkLib/ProofSystem/Sumcheck/Structured/`, whose
`SumcheckMultiplierParam` is degree-generic and whose docstrings already name Hachi's
`d := 2b+1`. That substrate is the reuse target; `RingSwitching/Packing/SumcheckPhase` is a thin
DP24-specific wrapper around it, and every DP24-specific thing in the wrapper is wrong for Hachi.

## 5. The framework mismatch (the least visible, most binding reason)

Even if the transcripts matched, the security statements would not compose. Everything Hachi in
this repo — including the finished Fig. 3 / Lemma 8 theorem — is proven as **coordinate-wise
special soundness** (CWSS): tree extraction, composed with `CWSSStructure.append`/`seqCompose`.
The paper's own Lemmas 9, 10, 11 are special-soundness statements, and its Fig. 6
"reinterpretation of sumcheck as single-round protocols" exists precisely so the sumcheck
composes with Lemma 8 in that framework. The `RingSwitching` module instead states **round-by-round
knowledge soundness** (state functions, Schwartz–Zippel error terms), with all five theorems
currently `sorry`. There is no RBR↔CWSS bridge in the repo. Plugging the module's sumcheck into
the Hachi chain would therefore require (a) building that bridge, and (b) still proving the
module's open soundness leaves — more work than proving the paper's own lemmas directly on the
`Sumcheck/Structured` substrate, for a protocol that would no longer be the paper's.

A side note on `[IsDomain L]`: it is *not* the blocker for §4.3 (there `L = F_{q^k}` is a field).
It *is* a hard blocker for ever running the module's generic soundness over `R_q` itself
(`R_q` is not a domain) — which rules out the other conceivable reuse direction, too.

## 6. What *is* compatible (don't over-conclude)

The module was designed as **data layer + protocol layer**, and the data layer fits Hachi
exactly:

- `RingSwitchingProfile` (`Profile.lean`) is `CommRing`-only by design; the Hachi instance
  (`B = R_q^H`, `L = A = R_q`, `φ₀ = id`, `φ₁ = σ₋₁`, basis = ψ) is plan milestone M1, and its
  data reappears verbatim in the paper's §4.5 Greyhound handoff (Eqs. 27–28).
- `packMLE` (`Prelude.lean`) is `CommRing`-generic and describes *both* of Hachi's packings:
  §3.1's `F_i = ψ(blocks)` (basis = ψ) and §4.5's Eq. (25) `ŵ_j` (basis = `Z`-powers of
  `F_{q^k}/F_q`).
- `Sumcheck/Structured/` (the substrate *under* the module) is the right base for the §4.3
  sumcheck, at degree `2b+1`, with CWSS proofs.

So the accurate statement is not "the ring-switching formalization is unusable for Hachi", but:
**Hachi reuses the ring-switching *algebra* and replaces the ring-switching *interaction***
— because Hachi's statement is engineered (subfield-valued points, tiny packing factor `k`) so
that the interaction is unnecessary, and its sumcheck serves a different master (norms and linear
relations, not claim relocation).

## 7. Update (2026-07-17): two construction folders, each with its own abstraction

The layout was restructured twice so the taxonomy above is visible in the tree itself:

- `ProofSystem/RingSwitching/Basic.lean` — family umbrella stating the taxonomy (rows 1–3 of §2).
- `ProofSystem/RingSwitching/Packing/` — the small→large packing family:
  `Profile.lean` (the shared packing data layer) + the DP24/Binius protocol files
  (`Prelude`, `Spec`, `BatchingPhase`, `SumcheckPhase`, `General`); consumed by
  `ProofSystem/Binius/FRIBinius/`. Hachi §3's head is the planned second `Profile` instance.
- `ProofSystem/RingSwitching/Lift/` — **the generic Hachi-style switch now exists**:
  `Presentation.lean` (proof-free `Presentation R S` + `IsPresentation` laws over *any* monic
  modulus, with the full lift algebra and the 2d-point interpolation engine proven over the
  laws) and `Reduction.lean` (the protocol layer over the committed-scalar shell, with the
  recovery obligation and CWSS at `k = 2d` proven once, generically).
- `OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean` — the
  committed-scalar seam (`BindingCommitment` + three-way extractor + CWSS package), in the
  CWSS toolkit, namespace `CoordinateWise`. It mentions no rings and is not a ring switch.
- `Commitments/Functional/Hachi/RingSwitch/Reduction.lean` — now the **cyclotomic instance**
  of `Lift`: `cyclotomicPresentation` with laws discharged from
  `Data/Lattices/CyclotomicRing/QuotientLift.lean` (reduced to the law-discharge kit), plus
  Hachi's norms and commitment interface. All public names/signatures preserved; the chain in
  `Composition.lean` is untouched and still sorry-free.

So the §6 conclusion is upgraded: Hachi's §4.3 switch now *is* an instance of a generic
ring-switching abstraction — just not of the packing one. The two abstractions remain
separate constructions, exactly as §§4–5 predicted; what they do share — the round-shape
verifier skeletons and the embed-and-evaluate algebra — now lives at the folder top level
(§8), while the committed-scalar seam itself is consumed only by the `Lift` side and the
`pSpecScalar` wire shape is common to both.

## 8. Update (2026-07-17): the shared verifier skeletons and embed-and-evaluate algebra, and why the data layers stop there

Two genuinely shared layers now live at the folder top level.

**The round-shape verifiers** (`ProofSystem/RingSwitching/RoundVerifiers.lean`): every
verifier round of the family is "one prover message, a deterministic local check, an
accept/reject statement update", over one of two wires. `messageRoundOracleVerifier` (wire
`pSpecMessage`) is instantiated by DP24's final eq̃-consistency step and is exactly the shape
of Hachi §3's planned trace-check head (one message `Y`, one deterministic check, zero
challenges). `scalarRoundOracleVerifier` (wire `pSpecScalar`) is instantiated by DP24's
batching round; its check-free limit — extend the statement, defer every check to the output
relation — is the committed-scalar verifier the `Lift` switch builds on.
Inside `Packing/`, the three DP24 verifier checks additionally collapsed to one
subroutine, the eq̃-weighted coordinate sum `eqWeightedCoordSum`.

**The embed-and-evaluate algebra** — transport a polynomial claim by pushing
its small-ring coefficients through a ring embedding and evaluating in the target carrier:

- `ProofSystem/RingSwitching/Transport/Eval.lean` — the univariate leg (`evalAt`, `evalAt_apply`,
  and the interpolation kernel `eq_of_evalAt_eq`, generalized from field targets to any
  domain), consumed by `Lift/`;
- `ProofSystem/RingSwitching/Transport/Coeffs.lean` — the multivariate leg (`embedCoeffs`, the
  degree-generic coefficient transport with its evaluation law), whose `d = 1` case is
  `Packing/`'s `componentWise_embed_MLE`. The degree-generic statement also covers
  higher-degree sumcheck round polynomials (Hachi's `d = 2b + 1`).

Alongside, `Lift/Presentation.lean` gained the **exactness layer**: a
modulus-multiple of degree below the monic modulus vanishes, so `rep` is additive *on the
nose* (`rep_zero`, `rep_add`, `rep_neg`, `rep_sum`) — strictly stronger than the shipped
coset-divisibility lemmas, derived purely from the existing `IsPresentation` laws.

Two negative results, checked while deciding **against** a common parent for the two data
layers (a "faithful coordinates of the large ring over the small ring" structure that both
`RingSwitchingProfile` and `Presentation` would instantiate):

- **Coordinate additivity is not derivable from `decomposeRows_spec` alone.** The
  reconstruction law forces joint injectivity of `decomposeRows`, but not additivity: with
  `A = L` and a rank-≥2 spanning family, non-additive sections satisfying the law exist
  (e.g. over `ℚ(√2)`). Since `A = L` is precisely the planned Hachi §3 profile shape, the
  additive strengthening cannot be assumed family-wide.
- **`rep` is not multiplicative on the nose** (only up to modulus multiples — e.g. in
  `R[X]/(X² + 1)`), so the exactness layer stops at the additive structure.

Above a spanning-and-faithful core the two law sets are therefore incomparable, and neither
side's proofs would consume a lemma stated at the join (`Packing` goes through
`Basis.sum_repr`; `Lift` needs the full `R[X]` ring structure). The shared layer
stays at the embed-and-evaluate algebra.
