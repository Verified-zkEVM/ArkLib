# The §4.5/§3.2 Partial-Evaluation Gap in Hachi — Analysis

Companion to [`HACHI_LEMMA10_GAP.md`](HACHI_LEMMA10_GAP.md) (which documents the Lemma 10
zero-check gap and its adopted Kronecker repair). Subject: **the partial-evaluation step of
Hachi (NOZ26, ePrint 2026/156) §4.5 (Eqs. (24)–(26)), and its generic form §3.2** — the
reduction from the per-slice well-formedness claims `yᵢ = fᵢ(x)` to the single `Z`-packed
evaluation claim `f′(x) = ∑ᵢ yᵢ·Z^{⟨i⟩}` is **not knowledge-sound as stated**. The
skeleton isolates this in one zero-round bridge,
[`Recursion/ZBatchBridge.lean`](ArkLib/Commitments/Functional/Hachi/Recursion/ZBatchBridge.lean),
whose pull-back sorry is flagged as *expected unprovable as stated*.

**Status: confirmed algebraic gap as written, found during the skeleton design review
(2026-07-13) and re-audited against the paper (2026-07-15). The explicit counterexample below is
information-theoretic and survives an honest downstream proof. A CWSS-native repair is adopted at
the design level in §3: reconstruct the DP24 tensor carrier from the already-sent `yᵢ`, fingerprint
it after the `yᵢ` are fixed, relocate the resulting claim by a degree-two sumcheck, and reuse the
paper's existing Eq. (27) element `p` at the endpoint. The repair has not yet replaced the skeleton's
faithful-but-unprovable `ZBatchBridge`. It has not been cross-checked with the authors.**

## 1. The step in question

§3.2 (and §4.5's recursion step, which follows the same pattern with `eq`-weights in place of
monomials): to prove `f(x) = y` for a committed polynomial `f` with **base-field** (`Z_q`)
coefficients at a point `x` with coordinates in the **extension field** `F = F_{q^k}`
(`k = 2^κ`), the prover sends the `2^κ` partial evaluations

```
yᵢ := fᵢ(x_rest) ∈ F,        i ∈ {0,1}^κ,
```

the verifier checks (or, for purity, derives `y₀` from)

```
y = ∑ᵢ mᵢ(x_top) · yᵢ                                       (Eq. (24) / §3.2 display)
```

and the remaining obligation — "all the yᵢ are well-formed" — is **replaced** by the single
packed claim (Eq. (26) / §3.2's f′-display), which the downstream protocol then proves:

```
f′(x_rest) = ∑ᵢ yᵢ · Z^{⟨i⟩},     where f′ := ∑ᵢ fᵢ · Z^{⟨i⟩}.
```

The paper's implicit claim is that this replacement is an equivalence ("proving well-formedness
of all (yᵢ)ᵢ is equivalent to proving (26)").

## 2. The gap

The packed claim pins only **one** `F`-linear combination of the per-slice defects
`εᵢ := yᵢ − fᵢ(x_rest) ∈ F`:

```
∑ᵢ Z^{⟨i⟩} · εᵢ = 0.                                        (*)
```

If the `εᵢ` were base-field scalars, (\*) would force `εᵢ = 0` (the `Z`-powers are an
`F_q`-basis). But `fᵢ(x_rest)` is evaluated at extension-field coordinates, so `εᵢ` ranges over
all of `F`: (\*) is `k` `F_q`-linear conditions on `k²` `F_q`-dimensions — a `k(k−1)`-dimensional
kernel for every `k ≥ 2`.

**Concrete cheat (`κ = 1`, `k = 2`, `F = F_q[Z]`).** Let `f(X₁, X₂)` be committed honestly with
slices `f₀, f₁` and true partials `tᵢ = fᵢ(x₂)`. The adversary sends

```
y₁ := t₁ − δ,     y₀ := t₀ + Z·δ,        δ ∈ F arbitrary.
```

Then `y₀ + Z·y₁ = t₀ + Z·t₁` — the packed claim (26) is **true for the honest committed `f′`**
and is proven by an entirely honest downstream run. The verifier's Eq. (24) check accepts the
claimed value

```
y = y₀ + x₁·y₁ = f(x) + δ·(Z − x₁),
```

so for any `x₁ ≠ Z` **every** target value `y` is reachable: the extractor holds the honest
`f`, all checks pass, and `f(x) ≠ y`. The same computation goes through with `eq`-weights
(§4.5) in place of monomials, and with the derive-`y₀` (footnote 5/10) convention — the cheat
vector simply enters through the sent `y₁`.

Note the contrast with the **generic §3.1 transformation** (Lemma 5/Theorem 2, the trace
check): there the downstream claim pins the packed element `Y` *exactly* (the residual claim is
an equality of ring elements), and the trace check transfers it to `y` with no slack — §3.1 is
unaffected. The slack is created precisely by §3.2/§4.5's `k²`-dimensional `yᵢ`-layer between
the two.

Also note Remark 1 of the paper flags a *different* issue with applying §3.1 to base-field
polynomials (extracted `f` lands in `F_{q^k}[X]`), and offers §3.2 as the fix — the gap above
says the fix itself does not extract.

## 3. Adopted repair: carrier-free-on-the-wire CWSS relocation

The repair uses the tensor carrier from DP24/Binius, but the prover does **not** send that carrier:
the verifier can reconstruct it from the `yᵢ` that Hachi already sends. Likewise, the usual
terminal field evaluation produced by the relocation sumcheck is not sent: the verifier derives it
from Hachi's existing Eq. (27) ring element `p`. Thus the values carried across the recursion
boundary remain exactly the paper's `(k−1)` extension-field elements and one ring element `p`.

The price is interaction: one post-`yᵢ` batching challenge and a degree-two relocation sumcheck.
This is a change to the paper's protocol, but it stays entirely within Hachi's CWSS proof currency.

### 3.1 The existing `yᵢ` determine the tensor carrier

Write `B := F_q`, `L := F_{q^k}`, `k := 2^κ`, and choose a `B`-basis
`(βᵢ)_{i < k}` of `L` (the paper's `Z`-basis). Split the Boolean index as `j ‖ i`, where
`j ∈ {0,1}^{mLow}`, `i ∈ {0,1}^κ`, and `mLow = ℓ−κ`. For the short base-field table `w̃`, define

```
ŵⱼ := ∑ᵢ w̃_{j‖i} · βᵢ ∈ L,
tᵢ := ∑ⱼ eq(j, a₀) · w̃_{j‖i} ∈ L.                         (true partials)
```

This is §4.5's multilinear/`eq` notation. For generic §3.2, replace `eq(j, a₀)` by the
corresponding tail-monomial weight; the tensor and CWSS arguments below use only `B`-linearity and
are otherwise identical.

Consider the tensor algebra `A := L ⊗_B L`. Once the verifier has the full derived family
`(yᵢ)ᵢ`, it can form locally

```
S_y := ∑ᵢ yᵢ ⊗ βᵢ ∈ A.                                    (public; not sent)
```

The committed table determines

```
S_w := ∑ⱼ eq(j, a₀) ⊗ ŵⱼ
     = ∑ᵢ tᵢ ⊗ βᵢ.                                        (witness carrier)
```

The second equality follows by expanding `ŵⱼ` and exchanging the sums. Since
`(1 ⊗ βᵢ)ᵢ` is an `L`-basis of `A`,

```
S_y = S_w    ↔    ∀ i, yᵢ = tᵢ.
```

This is exactly the missing `k²`-dimensional statement. The paper's Eq. (26) applies only one
non-injective projection to it; the repair tests the full tensor equality across a CWSS family.
The tensor is a proof device and verifier-local computation, not a new prover message.

### 3.2 Post-`yᵢ` scalar fingerprint

After the `yᵢ` are fixed, the verifier samples a fresh scalar `ρ ∈ L`. The ordering is
load-bearing: an earlier Hachi challenge cannot be reused, because then a malicious prover could
choose its `yᵢ` after seeing the fingerprint.

For each `ρ`, define the `B`-linear map `λ_ρ : L → L` by

```
λ_ρ(βᵤ) := ρᵘ,       0 ≤ u < k,
```

and the induced `B`-balanced map `Λ_ρ : A → L` by

```
Λ_ρ(x ⊗ z) := λ_ρ(x) · z.
```

The verifier computes the initial target directly from the existing partials:

```
s₀(ρ) := Λ_ρ(S_y) = ∑ᵢ λ_ρ(yᵢ) · βᵢ.                     (public)
```

On the witness side, define the public table

```
A_ρ(j) := λ_ρ(eq(j, a₀)).
```

Then

```
Λ_ρ(S_w) = ∑ⱼ A_ρ(j) · ŵⱼ.
```

The direct Vandermonde weights `ρᵘ` are the simplest choice. An equivalent DP24-shaped choice is
`λ_ρ(βᵤ) := eq(u, (ρ, ρ², …, ρ^{2^{κ−1}}))`; its Kronecker pull-back also has degree `< k` and is
injective. The rest of the protocol is unchanged by this choice.

The multiplier is efficiently evaluable without materializing `S_y`. If `(βᵤ*)ᵤ` is the
trace-dual basis, then

```
λ_ρ(x) = ∑ᵤ ρᵘ · Tr_{L/B}(βᵤ* · x).
```

Equivalently, write this `B`-linear map as a linearized polynomial
`λ_ρ(x) = ∑_{h<k} c_h(ρ)·x^{q^h}`. Because the Boolean `eq` coefficients lie in `B`, the
multilinear extension of `A_ρ` can be evaluated at `r ∈ L^{mLow}` as

```
Ã_ρ(r) = ∑_{h<k} c_h(ρ) ·
          ∏_v ((1−r_v)(1−a₀,v^{q^h}) + r_v·a₀,v^{q^h}).
```

Thus both prover and verifier can evaluate the public multiplier in `O(k·mLow)` field operations.

### 3.3 Relocate onto the fixed short table

Run a standard sumcheck over the `mLow` Boolean variables for

```
H_ρ(X) := Ã_ρ(X) · mle[ŵ](X).
```

Both factors are multilinear, so every round polynomial has degree at most two. Starting from
`s₀(ρ)`, the sumcheck ends at a point `r′ ∈ L^{mLow}` and a target `s_m` satisfying

```
s_m = Ã_ρ(r′) · mle[ŵ](r′).
```

This is the DP24 relocation step: it consumes the repointed tensor claim while retaining Hachi's
variable reduction. Crucially, `ρ` appears only in the public multiplier and targets. The committed
witness remains the paper's fixed short table `ŵ`; there is no challenge-scaled witness,
re-decomposition, or change to the `ψ(ŵ)` norm bound.

### 3.4 Reuse Eq. (27)'s `p`; do not send a terminal field value

A usual relocation protocol would now send `s′ := mle[ŵ](r′) ∈ L`. Hachi already has a larger
message that proves exactly this evaluation: form the paper's Eq. (27) element `p ∈ R′_q` using
the endpoint `r′`, and pass the same `p` to the next `QuadEval` invocation.

Let `n := d′/k`, coerced into `L`. With the paper's normalization, Theorem 2 gives

```
Tr_H(p) = n · mle[ŵ](r′).
```

The final relocation guard can therefore avoid both a separate `s′` and division:

```
n · s_m = Ã_ρ(r′) · Tr_H(p).                              (terminal guard)
```

Here `n` is nonzero, hence invertible in `L`: Hachi has odd characteristic
`q ≡ 5 (mod 8)`, while `d′/k` is a power of two. Avoiding division in the verifier equation does
not remove this fact from the extraction proof, which cancels `n`. The guard remains correct when
`Ã_ρ(r′) = 0`. The same `p` is the next iteration's public `QuadEval.y`; its downstream CWSS proof
establishes that `p` is well-formed for the reinterpreted
commitment. Eq. (27) already includes the `σ₋₁(ψ(f))` tail factor inside `p`, so the trace guard
must apply `Tr_H` directly to `p`, not multiply by that tail a second time.

### 3.5 CWSS extraction

For each outer `ρ` child, first apply the nested scalar `3`-special extractors to its full accepting
relocation-sumcheck subtree and then the downstream `QuadEval` extractor. If any two extracted short
openings of the fixed commitment differ, use Hachi's existing weak-binding/MSIS escape. Otherwise
binding gives one common opening across all branches. For that opening, write the tensor defect in
the first-factor basis as

```
D := S_y − S_w = ∑_{u=0}^{k−1} βᵤ ⊗ dᵤ.
```

For each `ρ` child, the **extracted** sumcheck identity, scaled trace guard, and well-formed next
`QuadEval` relation imply

```
Q_D(ρ) := Λ_ρ(D) = ∑_{u=0}^{k−1} dᵤ · ρᵘ = 0.
```

Use a scalar CWSS round with `(ℓ, k) = (1, 2^κ)`. Its star supplies `k` distinct `ρ` values while
the `yᵢ` prefix is shared. Since `deg Q_D < k`, deterministic interpolation gives `Q_D = 0`, hence
all `dᵤ = 0`, `D = 0`, and finally every `yᵢ = tᵢ`. This is a CWSS tree-extraction argument, not
a Fiat–Shamir or single-transcript Schwartz–Zippel argument.

At the CWSS level this is a deterministic implication and requires only that `L` contain `k`
distinct challenges. When the FMN24 CWSS-to-knowledge-soundness theorem is applied later, this
round contributes `k / |L|` to the knowledge-error bound under the paper's convention.

Each degree-two relocation round uses ordinary scalar `3`-special soundness. These structures
append to the existing Hachi CWSS chain:

```
partial evaluations
  ▷ scalar k-special batching challenge ρ
  ▷ mLow scalar 3-special sumcheck rounds
  ▷ scaled trace handoff using p
  ▷ next QuadEval CWSS package.
```

### 3.6 Communication, shortness, and arity

The values carried across the recursion boundary are unchanged from paper Eq. (28):

```
(k−1) elements of L     +     one p ∈ R′_q.
```

There is no tensor-carrier message and no terminal `mle[ŵ](r′)` message. The repair is nevertheless
not communication-free: it adds one verifier challenge `ρ`, `mLow` sumcheck challenges, and
`mLow` degree-two round polynomials. A quadratic can be compressed to two field elements using the
round's sum constraint (three if sent uncompressed), so the added prover communication is
`2·mLow` field elements compressed or `3·mLow` uncompressed.

The next ring polynomial still has

```
mLow − α′ + κ = (ℓ−κ) − α′ + κ = ℓ−α′
```

variables. The short witness is still `ŵ`, the next commitment still opens `ψ(ŵ)`, and the paper's
`‖ψ(ŵ)‖∞ ≤ 2β` bound and `reinterpretCom(t)` convention are unchanged.

### 3.7 The omitted partial must be chosen dynamically

This issue is specific to §4.5's `eq` weights; §3.2's monomial coefficient of `y_{0…0}` is one.
The paper's footnote 10 says that `y_{0…0}` can always be derived. That is not total when
`eq(0…0, a₁) = 0`. To retain exactly `k−1` sent values, the verifier instead chooses a canonical
index `i*` satisfying

```
eq(i*, a₁) ≠ 0
```

and derives

```
y_{i*} := (y − ∑_{i ≠ i*} eq(i, a₁)·yᵢ) / eq(i*, a₁).
```

Such an index always exists because `∑ᵢ eq(i, a₁) = 1`. This correction is independent of the
Eq. (26) gap, but is needed for a total implementation of the adopted repair.

## 4. Other repair space and non-solutions

| # | Approach | Sound? | Notes |
|---|---|---|---|
| 1 | **Carrier-free-on-the-wire CWSS relocation (§3)** | ✓ adopted | Reconstruct `S_y` from the existing partials; one post-`yᵢ` scalar `k`-special fork; degree-two relocation sumcheck; reuse `p`. Preserves the paper's boundary values, short witness, and `ℓ−α′` landing arity, but adds interaction. |
| 2 | **Generic §3.1 packing instead of §3.2/§4.5** (paper Fig. 2, row 1) | ✓ fallback | Treat the table as `F`-entried and `ψ`-pack whole `F`-elements. Costs `κ` extra variables (`ℓ−α+κ` instead of `ℓ−α`) and requires a sparse commitment reinterpretation. It also inherits Remark 1's extracted-coefficients-in-`F_{q^k}` caveat. |
| 3 | **Read more information from the unchanged Eq. (27) element `p`** | ✗ | The `Z`-packing has already collapsed the slice dimension before `ψ` and before `p` is formed, and Eq. (27)'s prescribed trace checks only that collapsed evaluation. Coefficient projections or alternative post-processing do not create the challenge-indexed independent equations needed to recover every `yᵢ`; the checked relation must change after the `yᵢ` are fixed. |
| 4 | **Keep the paper's zero-round Eq. (26) step** | ✗ | Broken by §2 for every `k ≥ 2`; no parameter choice helps because the slack is information-theoretic in the `yᵢ` layer. |

## 5. Formalization impact

- **Keep the sound head, fix its omission rule.** `Recursion/PartialEval.lean` may still send
  `k−1` values and stop at `relPartialEvalE`, but `deriveFamily` must omit a dynamically selected
  nonzero `eq` coordinate as in §3.7 rather than always `0…0`.
- **Replace, do not prove, `ZBatchBridge`.** The theorem
  `mem_relPartialEvalE_of_relHatEvalE` is false. Replace `zBatchPackage` by the scalar batching
  challenge and degree-two relocation chain of §§3.2–3.5. Its CWSS pull-back target is precisely
  `relPartialEvalE`: `k` accepting `ρ` continuations recover every per-`i` claim.
- **Change the terminal relation.** The relocation sumcheck should end in the scaled product
  relation `n·s_m = Ã_ρ(r′)·Tr_H(p)`, not a standalone `relHatEvalE` at the original `a₀` and not a
  separately sent field evaluation. `TraceHandoff` must build Eq. (27)'s `e`/`f` vectors from
  `r′`, apply the trace directly to `p`, and emit the same next-iteration `QuadEvalStatement`.
- **Reuse DP24 at the algebra/substrate level.** The carrier identities and degree-two sumcheck
  match `ProofSystem/RingSwitching/{BatchingPhase,SumcheckPhase}.lean`, but the Hachi package needs
  a CWSS proof rather than that module's current RBR proof. Keep the two tensor expansions explicit
  (`∑ yᵢ⊗βᵢ` versus `∑ βᵤ⊗zᵤ`) rather than relying on ambiguous row/column names when adapting
  `compute_s0`.
- **Update composition.** In `Hachi/Composition.lean`, replace the ⚠ zero-round bridge by the
  batching-plus-relocation packages before the modified trace handoff. Until this is implemented,
  the top-level certificate must continue to advertise the existing unprovable seam.
