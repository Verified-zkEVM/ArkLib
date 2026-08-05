# The Lemma 10 Gap in Hachi — Analysis and Repair

Companion to [`HACHI_RING_SWITCHING_PLAN.md`](HACHI_RING_SWITCHING_PLAN.md) (milestone F6, risk
R7) and [`HACHI_RING_SWITCHING_COMPARISON.md`](HACHI_RING_SWITCHING_COMPARISON.md). Subject:
**Lemma 10 of Hachi (NOZ26, ePrint 2026/156, §4.3, Fig. 5)** — the coordinate-wise special
soundness (CWSS) claim for the zero-check challenge round — is not provable as stated, and the
gap is witnessed by an explicit, protocol-level counterexample against the paper's own
range-check polynomial. This file states the gap precisely, shows which repairs work and which
do not, and records the rendering adopted by the formalization plan.

> **Status update (3 August 2026).** The formalization no longer uses the one-round
> Kronecker-curve rendering that §3.K and §4 record as "adopted". It now implements the
> **fully sequential scalar rounds** of §3.2 (there judged sound but dominated): each of the
> `m₀ + m₁` coordinates of `(τ₀, τ_α)` is its own `k = 2` challenge round, and extraction runs
> the path-dependent binary-evaluation-tree zero test of
> `ArkLib/ToCompPoly/Multilinear/NestedEvaluationTree.lean`
> (`EvaluationTree.eq_zero_of_vanishes_comp`, since 4 August 2026 stated Mathlib-level in
> `ArkLib/Data/MvPolynomial/NestedEvaluationTree.lean` for `k`-ary trees and individual degree
> `< k`, with the computable view in `ToCompPoly/`). The active theorem is
> `nestedZeroCheck_coordinateWiseSpecialSound` (`Hachi/ZeroCheck/Reduction.lean`), sorry-free and
> axiom-clean. The analysis below — in particular §2's counterexample and the comparison of
> repairs — remains the reference for *why* a repair is needed, with one correction recorded in
> the audit page: Figure 5 itself is sound as printed — Schwartz–Zippel gives it knowledge error
> `≈ (m₀+m₁)/|F|` — so what is being repaired is the CWSS *proof strategy*, not the protocol.
> The formal counterexample covers the prose reading (a star of scalar coordinates); the lemma's
> own `ℓ = 2` reading is objected to on dimension-counting grounds only, which is not formalized.
> Only the "adopted" markers in
> §3.K and §4 are historical. Current status lives in
> `docs/kb/audits/noz26-zero-check-lemma10.md`.

**TL;DR.** A star-shaped family of accepting transcripts certifies that a batched
constraint polynomial vanishes on the *axis cross* through the star's center — and for a
multilinear polynomial in at least two challenge variables, cross-vanishing does **not** imply
that the polynomial is zero. An adversary can commit to a witness with a single out-of-range
entry and present a perfectly valid, correctly structured one-round star from which no
extractor can succeed without breaking binding. No choice of the paper's parameter `D` helps.
The protocol itself is very likely still sound for uniformly random challenges, but the stated
deterministic tree-extraction claim is false.

The best repair is still **one round**. Restrict each random evaluation point to the Kronecker
curve

```
κ_m(ρ) := (ρ, ρ², ρ⁴, …, ρ^(2^(m-1))).
```

For an `m`-variate multilinear `H`, the pullback `H(κ_m(T))` is univariate of degree less than
`2^m`, and the pullback is injective: distinct multilinear monomials become the distinct powers
`T^0,…,T^(2^m−1)`. Sample independent scalar seeds `(ρ_0,ρ_α) ∈ F²` in one verifier round and
send `τ_0 := κ_{m_0}(ρ_0)` and `τ_α := κ_{m_α}(ρ_α)`. With

```
D := max(2^m_0, 2^m_α),
```

an `SS(F,2,D)` star gives `D` roots of each pullback on its corresponding arm, hence both
original identities. Its tree has `2D−1` leaves. If the two checks share one seed `ρ`, the same
argument gives ordinary `D`-special soundness with only `D` leaves. The existing equality-kernel
sumchecks remain unchanged because they simply receive the structured points `κ_m(ρ)`. The
tradeoff is that the evaluation points are curve-distributed rather than uniform in `F^m`, and
the error scale becomes `D/|F|` rather than `m/|F|`; one must assume `D ≤ |F|` and choose the
extension field accordingly. The coordinate-zipped construction below remains a sound fallback
when retaining the original uniform challenge distribution is more important than one-roundness.

Throughout, `F := F_{q^k}` is the challenge field; `m_0` and `m_α` (also written `m_1`) are the
arities of `H_0` and `H_α`; `N_0 := 2^m_0`, `N_α := 2^m_α`, and
`D := max(N_0,N_α)`; and "multilinear" means
degree at most one in each challenge variable. The paper calls the second point `τ_1`; this file
also writes `τ_α` to make its role unambiguous. In the zipped fallback, `r := max(m_0,m_α)` and
`s := min(m_0,m_α)`.

## 1. Faithful setting

Hachi §4.3 must prove, for a committed witness `w̃` (Eq. (21): the `Z_q`-coefficient table of
the Eq. (20) solution `(ŵ, t̂, ẑ)` and the quotient digits, indexed by `(u, ℓ)`), that

- the lifted linear rows hold at the challenge `α` (already reduced by Fig. 4 / Lemma 9), and
- every entry of `w̃` is in range: `w̃(u,ℓ) · ∏_{j=1}^{b−1} (w̃(u,ℓ) − j)(w̃(u,ℓ) + j) = 0`.

Both constraint families are batched with the equality kernel (Eqs. (22), (23)):

```
H_α(t) := Σ_{i ∈ [n]}  eq̃(t, i) · ( Σ_{u,ℓ} M̃_α(i,u) · w̃(u,ℓ) · α̃(ℓ)  −  y_i(α) )
H_0(t) := Σ_{u,ℓ}      eq̃(t, (u,ℓ)) · w̃(u,ℓ) · ∏_{j=1}^{b−1} (w̃(u,ℓ) − j)(w̃(u,ℓ) + j)
```

Both are **multilinear in `t`** (only `eq̃` depends on `t`, and `eq̃(·, i)` is multilinear).
Fig. 5 has the verifier send `τ_0` (for `H_0`) and `τ_1` (for `H_α`) in one round; the claims
`H_0(τ_0) = 0` and `H_α(τ_1) = 0` then seed the sumcheck (Figs. 6–7).

**Lemma 10 (paper, condensed).** Given `D := max(2d, 2b−1)` valid transcripts
`((τ_{i,0}, τ_{i,1}), w̃_i)` with `(τ_{i,0}, τ_{i,1})_i ∈ SS(F_{q^k}, 2, D)`, one can either
extract a valid opening `w̃` of `t` satisfying `H_0 ≡ 0` and `H_α ≡ 0`, or break binding of
`Com`. *Proof (paper):* if two `w̃_i` differ, binding breaks; otherwise "by definition of
`D = max(2d, 2b−1)` and the coordinate-wise special soundness, we have found at least `2d`
(resp. `2b−1`) distinct roots for `H_α` (`H_0`), which implies that the aforementioned
polynomials are equal to zero."

The statement is ambiguous about the CWSS shape — the lemma writes `SS(F, 2, D)` (which types
the challenge as a vector of `ℓ = 2` field elements, impossible for
`(τ_0, τ_1) ∈ F^{m_0} × F^{m_1}`), while the surrounding text says to treat `(τ_0, τ_1)` "as a
vector of `log μ + log d + log n` coordinates" (`ℓ = m := m_0 + m_1`; note this count is itself
inconsistent with the paper's own Eq. (21)/(23) index space `[μ+n] × [d]` — see plan F5 — and
the transcript count "`D` valid transcripts" disagrees with the `SS(S, ℓ, k)` set size
`K = ℓ(k−1)+1` under either reading: `2D−1` for `ℓ = 2`, `m(D−1)+1` coordinate-wise). §2
refutes the coordinate-wise reading (the substantive one); §3.0 disposes of the literal
`ℓ = 2` reading.
Recall the CWSS/`SS(S, ℓ, k)` shape ([FMN24] Def. 2.9, NOZ26 §2.3, formalized as
`CoordinateWise.IsSpecialSoundFamily`,
[Basic.lean:81](ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean#L81)):
a **star** — one central vector `c`, plus `k−1` siblings per coordinate `i`, each agreeing with
`c` everywhere except at coordinate `i`.

## 2. The gap

### 2.1 What a star actually certifies

**Lemma A (star ⇒ cross, and nothing more).** Let `H ∈ F[t_1, …, t_m]` be multilinear and let a
family of points vanish `H`, consisting of a center `c ∈ F^m` and, for each coordinate `j`, at
least one point `c^{(j)}` with `c^{(j)}_i = c_i` for `i ≠ j` and `c^{(j)}_j ≠ c_j`. Then `H`
vanishes identically on every axis line `L_j := { p : p_i = c_i for all i ≠ j }`.

*Proof.* The restriction of `H` to `L_j` is a univariate polynomial of degree ≤ 1 in `t_j`
(multilinearity). It vanishes at the two distinct points `c_j` and `c^{(j)}_j`, hence is the
zero polynomial. ∎

So *any* number `k ≥ 2` of siblings per coordinate certifies exactly: `H` vanishes on the
**axis cross** `⋃_j L_j` through `c`. The question is whether cross-vanishing forces `H ≡ 0`.
For `m = 1` it does (the cross is the whole space). For `m ≥ 2` it does not:

**Counterexample B (polynomial level).** Let `m ≥ 2`, `a, b ∈ F`, and
`H*(t) := (t_1 − a)(t_2 − b)`. `H*` is multilinear and `H* ≢ 0` (it is `1` at
`(a+1, b+1, …)`), yet `H*` vanishes on the entire cross through any center `c` with `c_1 = a`,
`c_2 = b`: every point of every axis line through `c` retains `t_1 = a` or `t_2 = b`. Moreover,
since `{eq̃(·, i)}_{i ∈ {0,1}^m}` is a basis of the multilinear polynomials (evaluation at the
Boolean points is the identity matrix: `eq̃(i', i) = δ_{i,i'}`), we have
`H* = Σ_i eq̃(t, i) · H*(i)` — so `H*` is *exactly of the batched form* in Eqs. (22)/(23), with
coefficient vector `c_i := H*(i)` not all zero. ∎

Lemma A + Counterexample B already refute the paper's proof *step* ("roots ⇒ zero"). The
following upgrades this to a refutation of the lemma's *statement*, i.e. an attack an adversary
can actually mount inside the protocol.

### 2.2 A constructive, protocol-level counterexample (via the range check)

The range-check polynomial `H_0` is the easiest to weaponize because the adversary controls its
coefficients **entrywise**: the coefficient of `eq̃(t, (u,ℓ))` is
`P_b(w̃(u,ℓ))` where `P_b(v) := v·∏_{j=1}^{b−1}(v−j)(v+j)`, a fixed nonzero polynomial of
degree `2b−1`.

**Construction.** Assume `q > 2b−1` (true for all real parameters; Fig. 9 has `q ≈ 2^32`,
`b = 16`) and `m_0 ≥ 2` (always: `m_0` is the log of the witness table size). Note the entries
of `w̃` live in `Z_q` (Eq. (21): they are `X`-coefficients of `R_q`-elements), so the
out-of-range value must be chosen in `Z_q`, and — because the paper instantiates *weak* binding
(Remark 2 / Lemma 7), whose second-opening consequence is norm-conditioned — it must also be
**small**, so that the eventual opening pair yields a genuinely short MSIS solution.

1. Set `v* := b ∈ Z_q`. Then `P_b(v*) = b·∏_{j=1}^{b−1}(b−j)(b+j)`: every factor lies in
   `{1, …, 2b−1}`, hence is nonzero mod `q` by `q > 2b−1`, so `P_b(v*) ≠ 0`. Pick any index
   `(u*, ℓ*)` covered by the range check (all of them under Eq. (23); take `u* ≤ μ` if the
   `1_{≤μ}` convention of `F_{0,τ_0}` is used).
2. Build `w̃` as the **all-zero table except** entry `(u*, ℓ*) := v*` (all other entries must be
   in range, else `H_0` acquires further `eq̃`-monomials and step 4's cross argument breaks;
   zero is in range). Then choose the *statement* to match the linear part — take the public
   `y`-side to be whatever the lifted rows evaluate to on this `w̃`, with the honest quotient
   (Lemma 10 is a statement about arbitrary public inputs; the adversary who controls the
   earlier protocol messages controls the R^lin statement it feeds). Then `H_α ≡ 0`
   identically, and `H_0(t) = P_b(v*) · eq̃(t, (u*, ℓ*)) ≢ 0`.
3. Commit honestly: `t := Com(w̃)`. Note the zero set of `H_0` is the union of hyperplanes
   `⋃_j { t_j = 1 − i*_j }` where `i* ∈ {0,1}^{m_0}` is the bit pattern of `(u*, ℓ*)`.
4. Choose the star center `c ∈ F^{m_0}` with `c_{j_1} = 1 − i*_{j_1}` and
   `c_{j_2} = 1 − i*_{j_2}` for two distinct coordinates `j_1 ≠ j_2` (arbitrary elsewhere).
   Every axis line through `c` fixes all-but-one coordinate, so it retains at least one of the
   two vanishing coordinates — the entire cross lies in the zero set of `H_0`. Populate the
   star with any `D−1` siblings per coordinate; choose `τ_1`-parts arbitrarily.
5. Every transcript in the family is **valid**: `t = Com(w̃)` holds, `H_α(τ_1) = 0` holds
   identically, and `H_0(τ_0) = 0` holds at every star point by step 4.

All transcripts carry the *same* `w̃`, so the extractor's binding branch is unavailable, and its
main branch must output an opening of `t` whose entries are all in range (`H_0 ≡ 0` forces every
entry to be a root of `P_b`, i.e. in `[−(b−1), b−1]`) — any such opening differs from `w̃`
(whose entry `(u*,ℓ*) = b` is out of range), and the difference is entrywise bounded by
`2b−1` — **short**. The pair is therefore exactly a *weak-binding* break in the paper's sense
(a short Module-SIS solution via Lemma 7): the extractor itself would be an efficient
weak-binding breaker. Under the binding assumption, no efficient extractor exists. Lemma 10,
under the coordinate-wise reading, is false — for *every* value of `D`. ∎

Two remarks. (i) The attack lands on the **range check** — the exact-norm-proof feature that is
the paper's headline contribution — so this is not a peripheral technicality. (ii) The attack
does not need `H_α`: it is orthogonal to the Lemma 9 layer, whose own soundness (univariate,
`k = 2d`) is fine.

### 2.3 Diagnostics: where the paper's proof goes wrong

- **Degree confusion.** `H_α` and `H_0` are multilinear *in `t`*. The quantities `2d` and
  `2b−1` are degrees in *other* variables — `2d−1` bounds the `X`-degree of the lifted rows
  (that is Lemma 9's interpolation, over the `α`-challenge), and `2b−1` is the `w̃`-degree of
  the range product (Lemma 11's per-round sumcheck degree is then `2b` — range product times
  the multilinear `eq̃` — with `k = 2b+1` transcripts per round; plan F5/R8). Neither has
  anything to do
  with identity-testing the `t`-polynomials; "`2d` (resp. `2b−1`) distinct roots" for a
  *multivariate multilinear* polynomial implies nothing. Even along a single coordinate line,
  2 points already suffice — and all `m` lines together still do not determine `H` (Lemma A +
  Counterexample B). So `D = max(2d, 2b−1)` is simultaneously wasteful (per line) and
  insufficient (globally).
- **Why the paper's *other* CWSS lemmas are unaffected.** Lemma 8 (QuadEval/folding, formalized
  sorry-free) uses stars *correctly*: its verification equations are affine in each challenge
  coordinate, and extraction subtracts the center transcript from a sibling to *isolate one
  column* — the star is exactly the right shape for folding, and no "vanishing ⇒ zero
  polynomial" step occurs. Lemmas 9 and 11 are single-scalar-challenge rounds — univariate
  interpolation, rigorous. The misuse is specific to Lemma 10's *multivariate zero-check*.
- **What survives.** The *protocol* is almost certainly still knowledge-sound: for uniformly
  random `τ`, a nonzero multilinear `H` in `m` variables vanishes with probability at most
  `m/|F|` (Schwartz–Zippel; total degree ≤ m), and the adversarial cross is a
  measure-`O(m/|F|)` event. What is broken is the *tree-extraction claim* — precisely the
  currency in which the paper (via FMN24 Lemma 4) and the ArkLib formalization (via
  `CWSSStructure` composition) do all their accounting.

## 3. Repair approaches

Summary table; details below.

| # | Approach | Sound? | Verdict |
|---|---|---|---|
| K | **One-round Kronecker-curve challenges, `k = D`** | ✓ | **adopted** (plan F6) |
| 0 | Literal `ℓ = 2` reading, with unrestricted uniform vector blocks | ✗ | fails |
| 1 | Coordinate-zipped sequential CWSS rounds, `k_j = 2` | ✓ | uniform-challenge fallback |
| 2 | Fully sequential scalar rounds, `k_j = 2` | ✓ | sound fallback, but dominated by 1 |
| 3 | One round with a tensor-grid tree shape | ✓ | sound, but needs a new non-CWSS tree predicate |
| 4 | Keep the original one-round star and appeal only to the separation of `H_0` and `H_α` | ✗ | separation helps only after re-scheduling |
| 5 | Keep the original vector-coordinate star and increase `k`/`D` | ✗ | no parameter helps without re-encoding |
| 6 | Rewinding plus Schwartz–Zippel for the original uniform vectors | ✓* | sound, but not deterministic CWSS extraction |
| 7 | Direct scalar power fingerprint `Σ_i c_i T^i` | ✓ | one-round alternative; changes the multiplier |

### 3.K One-round Kronecker-curve CWSS — works (adopted)

The missing ingredient is not another tree shape; it is a challenge encoding on which ordinary
univariate interpolation is information-complete for multilinear polynomials.

#### 3.K.1 The injective pullback

For `m ≥ 1`, define the Kronecker curve

```
κ_m : F → F^m,
κ_m(ρ)_j := ρ^(2^j)                 for j = 0,…,m−1.
```

Write an arbitrary multilinear polynomial in the monomial basis:

```
H(X_0,…,X_{m-1}) = Σ_{e ∈ {0,1}^m} a_e · ∏_j X_j^(e_j).
```

Its pullback is

```
K_H(T) := H(κ_m(T))
        = Σ_{e ∈ {0,1}^m} a_e · T^(Σ_j e_j 2^j).
```

The binary encoding `e ↦ Σ_j e_j 2^j` is a bijection from `{0,1}^m` to
`{0,…,2^m−1}`. Consequently,

```
deg K_H < 2^m,
K_H = 0  ⇔  H = 0.                 (Kronecker injectivity)
```

This is stronger than a Schwartz–Zippel statement: it is a deterministic polynomial identity
equivalence. ArkLib already has the forward map as
`LinearMvExtension.powAlgHom` in
[`LinearMvExtension.lean`](ArkLib/Data/MvPolynomial/LinearMvExtension.lean); its existing
`powAlgHom_of_restrict_degree_natDegree` proves the degree bound. The main generic algebra lemma
still needed for this repair is injectivity of `powAlgHom` on the per-variable-degree-`≤1`
subtype. The file's inverse construction `linearMvExtension` already contains almost all of that
proof.

#### 3.K.2 Protocol rendering

Let

```
N_0 := 2^m_0,
N_α := 2^m_α,
D   := max(N_0,N_α),
```

and assume `D ≤ |F|`. Replace Fig. 5's unrestricted vector sampling by the following single
public-coin round:

```
ρ_0, ρ_α ← F independently
τ_0       := κ_{m_0}(ρ_0)
τ_α       := κ_{m_α}(ρ_α)
send (τ_0,τ_α)                    -- or send the two seeds and derive the vectors
```

The prover response and verifier equations stay exactly as in Fig. 5:

```
t = Com(w̃),
H_0^{w̃}(τ_0) = 0,
H_α^{w̃}(τ_α) = 0.
```

The protocol's challenge type should be modeled as `F²`, with the two vectors derived
deterministically. If the expanded vectors themselves are placed in the semantic transcript,
their types must be the **curve-image subtypes**, not unrestricted `F^m`: injectivity of `κ_m`
(its first coordinate is `ρ`) then gives the required equivalence between each subtype and `F`.
Merely serializing the expanded vectors on the wire is harmless, but ArkLib's `Challenge` type
must retain the on-curve invariant so that every family admitted by the `CWSSStructure` consists
of curve points.

This Lemma 10 block is at a **fixed, previously extracted `α`**, exactly as in the paper's lemma
statement `(t,M̃_α,α)`. The `α` fork from Lemma 9 must remain an earlier/nested extraction node.
Even if an implementation coalesces `α,ρ_0,ρ_α` into one byte message, treating all three as one
flat CWSS star is not justified: the `H_α` check has mixed dependence on `α` and `ρ_α`, recreating
the same missing-corners problem.

#### 3.K.3 Extraction from one CWSS star

An `SS(F,2,D)` family has not `D` but

```
2(D−1)+1 = 2D−1
```

members. Relabel it around its center as

```
(a,b),
(a_1,b), …, (a_{D-1},b),
(a,b_1), …, (a,b_{D-1}),
```

where `a,a_1,…,a_{D-1}` are distinct and so are `b,b_1,…,b_{D-1}`.

If two accepting branches return different admissible openings of `t`, return the same
binding/weak-binding escape as in the paper. Otherwise binding fixes one common `w̃`. The first
arm now gives `D` distinct roots of

```
K_0(T) := H_0^{w̃}(κ_{m_0}(T)),       deg K_0 < N_0 ≤ D,
```

so `K_0 = 0`, and Kronecker injectivity gives `H_0^{w̃} = 0`. The second arm identically gives
`H_α^{w̃} = 0`. The bad axis-cross polynomial from §2 cannot survive this challenge encoding:
its pullback is a nonzero univariate polynomial of degree less than `N_0`, hence it cannot vanish
at all `D` first-arm seeds.

This yields the corrected statement:

**Lemma 10 (corrected: one-round Kronecker CWSS).** Suppose `m_0,m_α ≥ 1`,
`D := max(2^m_0,2^m_α) ≤ |F|`, and the Fig. 5 points are derived from independent scalar seeds
by `κ`. There is an efficient deterministic extractor which, from a family of `2D−1` accepting
transcripts whose seed pairs lie in `SS(F,2,D)`, returns either

1. one opening `w̃` of `t` satisfying `H_0^{w̃} ≡ 0` and `H_α^{w̃} ≡ 0`, or
2. the commitment binding escape used by the surrounding Hachi proof.

Thus the modified zero-check is one-round `(2,D)`-coordinate-wise special sound. The extractor
is polynomial time whenever the checked table sizes `N_0,N_α` are polynomial in the security
parameter, exactly the regime required for the protocol itself to be efficient. For a zero-arity
identity, test the resulting constant directly and take `D := max(2,N_0,N_α)` to meet ArkLib's
nontrivial-parameter convention.

#### 3.K.4 Plain-special-soundness variant

If independence between the two batching points is unnecessary, sample one `ρ ← F` and set

```
τ_0 := κ_{m_0}(ρ),
τ_α := κ_{m_α}(ρ).
```

Then any `D` accepting transcripts with distinct `ρ` give `D` roots of *both* pullbacks. The
protocol is ordinary `D`-special sound (`ℓ=1`) and its extraction input has only `D` leaves. This
is the smallest one-round rendering, but the independent-seed CWSS variant is closer to Fig. 5
and lets the two tests retain cross-block independence.

The independent-seed protocol is not ordinary `D`-special sound merely by treating a pair as
one challenge: `D` distinct pairs need not contain `D` distinct first coordinates or `D`
distinct second coordinates. Its two star arms are exactly what the CWSS hypothesis supplies.

#### 3.K.5 Cost and faithfulness

- **Rounds and payload.** There is one challenge round. Sending seeds costs two field elements;
  sending the derived vectors retains Fig. 5's message shape but spends `m_0+m_α` elements.
- **Downstream sumchecks.** They are unchanged: substitute the derived `τ_s=κ_{m_s}(ρ_s)` into
  the same `eq̃(τ_s,·)` multiplier. Repeated squaring computes each curve point in `O(m_s)` field
  operations.
- **Tree size.** Independent seeds use `2D−1` leaves; a shared seed uses `D`. When
  `N_0=N_α=N`, the zipped fallback uses `3^{log₂ N}=N^{log₂ 3}` leaves, so both curve variants
  asymptotically improve the extraction tree.
- **Error tradeoff.** A false fixed opening makes at least one nonzero pullback of degree at most
  `D−1`, so its relevant uniform seed lands on a root with probability at most
  `(D−1)/|F|`. This is worse than the `O((m_0+m_α)/|F|)` scale of uniform vector evaluation.
  Asymptotically `D=poly(λ)` and `|F|=2^{Ω(λ)}` still give negligible error. Concretely, the
  paper's largest next-witness table has size about `2^26` over a field of size about `2^128`,
  so a single curve test supplies only about 102 bits from this term; a 128-bit target needs a
  larger extension field or parallel repetition. Repeated seeds can still be sent in the same
  verifier message, although the corresponding CWSS coordinate count and star arity grow.
  In particular, do not apply the `2D/|F|²`-shaped expression printed in Hachi's restatement of
  FMN24 literally here: if only `H_0` is invalid while `H_α=0`, acceptance can already have
  probability `(N_0−1)/|F|`. The direct root bound is the safe accounting.
- **Faithfulness.** The verifier no longer samples uniformly from all of `F^{m_0}×F^{m_α}`.
  It samples uniformly from two size-`|F|` Kronecker curves. This is a genuine, localized
  protocol change, though the checked equations and every downstream sumcheck formula are the
  same.
- **Field-size condition.** `D ≤ |F|` is load-bearing: without it an `SS(F,2,D)` family cannot
  exist, and the root argument cannot collect `D` distinct seeds.
- **Scalar-threshold optimality.** For `N` arbitrary residual coefficients, any linear
  one-scalar batching defines a length-`|F|`, dimension-`N` evaluation code. If `k` accepting
  roots always force the coefficient vector to vanish, its distance is at least `|F|−k+1`;
  the Singleton bound gives distance at most `|F|−N+1`, hence `k ≥ N`. Kronecker and direct
  powers attain this bound. The table-sized threshold is therefore inherent in this generic
  scalar-linear model, not slack in the proof.
- **Why the change is necessary.** If the original unrestricted uniform vector challenge is
  retained, the §2.2 range-check counterexample accepts on
  `|F|^m−(|F|−1)^m` distinct points. Plain one-round special soundness would therefore require
  more than that many transcripts, which is not polynomial in the relevant parameters. A
  polynomial-size one-round SS/CWSS repair must restrict or re-encode the challenge space (or
  change the tree predicate).

### 3.0 The literal `ℓ = 2` unrestricted-block reading — fails

Read `SS(F,2,D)` as treating the two *blocks* `τ_0` and `τ_1` as the two coordinates, so a
sibling may replace an entire block by an arbitrary new vector. Then the family merely gives
`D` adversarially chosen multivariate points at which `H_0` vanishes, and `D` such points can
all be placed on a nontrivial zero set. Even random points would supply only `D` linear
conditions for a multilinear polynomial having up to `2^{m_0}` coefficients. This reading is
strictly weaker than the coordinate-wise reading refuted in §2.2. ∎

### 3.1 Coordinate-zipped sequential CWSS rounds — works (uniform-challenge fallback)

The key observation is that the zero-check contains **two separate identities in disjoint
variable sets**:

```
H_0     ∈ F[X_1, …, X_{m_0}],
H_α     ∈ F[Y_1, …, Y_{m_1}].
```

A CWSS star can safely process one fresh variable of each identity in parallel. What it cannot
do is process two fresh variables belonging to the *same* arbitrary multilinear identity in
one node.

#### 3.1.1 Protocol rendering

Write

```
τ_0 = (x_1, …, x_{m_0}),
τ_1 = (y_1, …, y_{m_1}),
r   = max(m_0,m_1),
s   = min(m_0,m_1).
```

Replace the single atomic Fig. 5 challenge by `r` successive public-coin challenge rounds. For
`j ∈ [r]`, send

```
χ_j := (x_j,y_j) ← F²       if j ≤ m_0 and j ≤ m_1,
χ_j := x_j       ← F        if j ≤ m_0 and j > m_1,
χ_j := y_j       ← F        if j > m_0 and j ≤ m_1.
```

Equivalently, define

```
ℓ_j := 1_{j≤m_0} + 1_{j≤m_1} ∈ {1,2},
k_j := 2.
```

At the end of these rounds, reconstruct the same vectors `τ_0,τ_1` and retain the same scalar
claims

```
H_0(τ_0) = 0,
H_α(τ_1) = 0,
```

which seed the unchanged downstream sumchecks.

To fit a strictly alternating transcript syntax, insert a fixed empty prover message between
successive verifier challenges. The rounds must be genuine fork points in the extraction
object; merely sampling one atomic vector and parsing it afterward does not create the nested
CWSS tree used below.

#### 3.1.2 Why the `SS(F,2,2)` star is now sufficient

At a paired round, the three challenges in the CWSS family can be relabeled as

```
(a,b),   (a',b),   (a,b')
```

with `a' ≠ a` and `b' ≠ b`. The geometry is still a star:

```
                 (a,b')
                    |
                    |
          (a,b) ----+---- (a',b)
```

But the two asserted polynomials use different arms:

- `H_0` sees only the first coordinate, so `(a,b)` and `(a',b)` provide two distinct values of
  its current variable;
- `H_α` sees only the second coordinate, so `(a,b)` and `(a,b')` provide two distinct values of
  its current variable.

There is no asserted polynomial in this round containing a mixed term in both `x_j` and `y_j`.
That is exactly what failed in the original rendering, where several coordinates of `H_0`
(and several coordinates of `H_α`) lived in one large star.

The old toy counterexample illustrates why nesting matters. For
`H_0(X_1,X_2) = X_1X_2`, a one-round star at `(0,0)` misses `(1,1)`. In the repaired schedule,
`X_1` and `X_2` occur in different rounds. On the branch `X_1 = 1`, the next round must test two
distinct values of `X_2`, so the formerly missing corner appears and the nonzero polynomial is
caught.

#### 3.1.3 Seam relations and bottom-up extraction

For `0 ≤ j ≤ r`, define the intermediate relation `R_j` for an opening `w̃` of `t` by

```
t = Com(w̃),

H_0^{w̃}(x_1,…,x_{min(j,m_0)}, X_{min(j,m_0)+1},…,X_{m_0}) ≡ 0,

H_α^{w̃}(y_1,…,y_{min(j,m_1)}, Y_{min(j,m_1)+1},…,Y_{m_1}) ≡ 0,
```

where the last two equalities are polynomial identities in the as-yet unchallenged variables.
Then:

- `R_r` is exactly the pair of scalar claims
  `H_0^{w̃}(τ_0)=0 ∧ H_α^{w̃}(τ_1)=0` supplied by an accepting leaf;
- `R_0` is the desired conclusion
  `H_0^{w̃}≡0 ∧ H_α^{w̃}≡0`.

The extraction kernel is the usual two-point step.

**Lemma C (two-point multilinear step).** Let `G ∈ F[U,Z_1,…,Z_h]` have degree at most one in
`U`. If `a ≠ a'` and

```
G(a, Z_1,…,Z_h)  ≡ 0,
G(a',Z_1,…,Z_h)  ≡ 0,
```

then `G ≡ 0`.

*Proof.* Write `G = A + U·B`, with `A,B ∈ F[Z_1,…,Z_h]`. The two identities give
`A+aB≡0` and `A+a'B≡0`; subtraction yields `(a-a')B≡0`. Since `F` is a field and
`a≠a'`, `B≡0`, and then `A≡0`. ∎

Now extract from the transcript tree bottom-up.

- **Paired round.** Recursively extract from the subtrees rooted at `(a,b)`, `(a',b)`, and
  `(a,b')`. If any recursive call already returns a binding/MSIS escape, return it. If the
  resulting openings of `t` differ, return the corresponding binding/MSIS escape. Otherwise
  they are one common opening `w̃`. The center and first-coordinate sibling give two
  identically-zero restrictions of the current variable of `H_0`, so Lemma C removes that
  variable. The center and second-coordinate sibling do the same for `H_α`. Hence `R_j`
  implies the parent relation `R_{j-1}`.

- **Unpaired round.** There are two children with distinct scalar challenges. If their openings
  differ, return the binding/MSIS escape; otherwise apply Lemma C to the one identity that
  still has a fresh variable. The other identity is simply inherited.

Induction to the root produces either the same binding/MSIS escape used elsewhere in Hachi or a
single opening `w̃` satisfying `R_0`.

#### 3.1.4 Zipped fallback theorem

**Fallback Lemma (CWSS of the coordinate-zipped zero-check).** Let
`Π_zc^zip` be the modified zero-check protocol above. For each challenge round `j ∈ [r]`, let
the verifier challenge lie in `F^{ℓ_j}`, where

```
ℓ_j = 1_{j≤m_0} + 1_{j≤m_1},
k_j = 2.
```

There is an efficient deterministic extractor which, given the public statement and a valid
tree of accepting transcripts such that the children at every depth `j` form a family in
`SS(F,ℓ_j,2)`, outputs either

1. an opening `w̃` of `t` satisfying

   ```
   t = Com(w̃),
   H_0^{w̃} ≡ 0,
   H_α^{w̃} ≡ 0,
   ```

   or

2. two distinct admissible openings of `t` giving the same binding/MSIS violation as in the
   paper's commitment analysis.

Consequently, under the stated binding assumption, `Π_zc^zip` is

```
(ℓ_1,…,ℓ_r)-coordinate-wise (2,…,2)-special sound
```

for the zero-check relation. Its transcript tree has

```
K = ∏_{j=1}^r (ℓ_j(2−1)+1)
  = 3^s · 2^{r−s}
  = 3^{min(m_0,m_1)} · 2^{|m_0−m_1|}
```

leaves.

*Proof.* The bottom-up induction through the seam relations `R_j` is given in §3.1.3. ∎

#### 3.1.5 Accounting and faithfulness

- **Challenge payload.** The verifier still samples exactly `m_0+m_1` independent field
  elements, and the final joint distribution of `(τ_0,τ_1)` is unchanged. They are grouped
  into `r=max(m_0,m_1)` rounds instead of one atomic message.

- **Tree size.** The fully scalar repair has `2^{m_0+m_1}` leaves. The zipped repair has
  `3^s·2^{r-s}` leaves and

  ```
  3^s·2^{r-s} ≤ 2^{r+s} = 2^{m_0+m_1}.
  ```

  When `m_0=m_1=m`, this improves `4^m` to `3^m`. Since the challenge arities are logarithmic
  in the relevant table sizes, the tree remains polynomial-size under the same parameter
  regime required by the paper.

- **Knowledge error.** Using the FMN24 per-round term quoted in the formalization notes,
  `ℓ_j(k_j−1)/|F|`, paired rounds contribute `2/|F|` and scalar rounds contribute `1/|F|`.
  The total is therefore

  ```
  (2s + (r−s))/|F| = (m_0+m_1)/|F|,
  ```

  the same intended error as the all-scalar repair and much smaller than the paper's
  `D`-dependent star accounting. The discrepancy between this formula and NOZ26's printed
  restatement of FMN24 remains a separate upstream issue.

- **Degree parameters.** The zero-check rounds use `k_j=2` because each identity is affine in
  its one fresh variable. The values `2d` and `2b−1` concern other variables and other protocol
  stages; `D=max(2d,2b−1)` should not occur in corrected Lemma 10.

- **Downstream protocol.** Figs. 6–7 consume only the completed vectors `τ_0,τ_1` through
  `eq̃(τ_0,·)` and `eq̃(τ_1,·)`. Their arithmetic is unchanged.

- **Fiat–Shamir caveat.** The challenge rounds must become genuine, domain-separated random-
  oracle queries or sequential sponge squeezes at which the extractor can fork. The payload
  size and distribution are unchanged, but byte-for-byte transcript identity with the
  original single-message rendering is not guaranteed and should not be claimed without fixing
  a concrete derivation convention.

### 3.2 Fully sequential scalar rounds — sound, but dominated

A simpler repair sends all `m_0+m_1` coordinates in separate scalar rounds and applies Lemma C
once per round. This is rigorous and uses ordinary `2`-special soundness throughout. Its nested
tree is the full two-point tensor grid, with

```
K_scalar = 2^{m_0+m_1}.
```

The zipped repair performs exactly the same interpolation for each identity, but processes one
coordinate of `H_0` and one coordinate of `H_α` in parallel. It uses fewer rounds, no more
knowledge error, and a strictly smaller tree whenever `s>0`. The all-scalar rendering remains a
valid fallback if an implementation exposes only scalar challenge-round machinery, but it is
not the preferred formulation of Lemma 10.

### 3.3 One round with a tensor-grid tree — sound, but unnecessary

Keep one batched challenge round, but replace the star node predicate by a **grid**: the
children must contain a product set `S_1×⋯×S_m` with `|S_j|≥2` for every coordinate.

**Lemma D (grid interpolation).** A multilinear `H ∈ F[t_1,…,t_m]` vanishing on
`S_1×⋯×S_m`, with every `|S_j|≥2`, is identically zero.

*Proof.* Induct on `m`. Write `H=A+t_mB`. At each point of the first `m−1` coordinates, the
univariate restriction in `t_m` has two roots and degree at most one, so both `A` and `B`
vanish on the smaller grid; induction gives `A≡B≡0`. ∎

This repair is sound, but a two-point grid has `2^{m_0+m_1}` leaves, larger than the zipped
CWSS tree. It also requires a new non-star node predicate, new composition lemmas, and a new
knowledge-error theorem, whereas §3.1 stays inside the existing CWSS definition and its
`seqCompose` machinery. Rejected on cost.

### 3.4 Keeping the original one-round star does not become sound merely because the identities are separate

The disjointness of `H_0(X_1,…,X_{m_0})` and `H_α(Y_1,…,Y_{m_1})` is useful, but it does not
rescue the original one-round star. That star still places *all* `X`-coordinates in one node,
so `H_0` may contain mixed terms such as `X_1X_2`; similarly, `H_α` may contain mixed
`Y_iY_j` terms. The counterexample of §2.2 therefore remains valid.

What the disjointness permits is the more precise scheduling rule used in §3.1:

> A CWSS round may contain several challenge coordinates only if each asserted polynomial
> depends on at most one of those coordinates.

For Hachi's two identities, this allows at most one `X`-coordinate and one `Y`-coordinate per
round — exactly the coordinate-zipped schedule. ∎

### 3.5 Keep the original vector-coordinate star and increase `k`/`D` — fails

Counterexample B vanishes on every relevant axis line *identically*. A star may therefore have
arbitrarily many siblings per vector coordinate and all its transcripts still accept. No larger
value of `k` or `D` recovers the missing mixed-coordinate information *without changing the
challenge encoding*. The Kronecker repair changes it so that each star coordinate is a scalar
seed whose arm traces an information-complete curve. ∎

### 3.6 Rewinding plus Schwartz–Zippel — sound, but not a CWSS extractor

One can prove the zero-check probabilistically: rewind the prover with fresh uniformly random
`(τ_0,τ_1)` and use Schwartz–Zippel to bound the acceptance probability of a nonzero
multilinear polynomial by its total degree divided by `|F|`. This gives a sound standalone
argument, but it replaces deterministic CWSS tree extraction by a different rewinding proof.
Neither the paper's FMN24-based composition nor ArkLib's `CWSSStructure.append/seqCompose`
currently composes that mixed proof style. The Kronecker rendering in §3.K turns the same
root-counting intuition into deterministic one-round CWSS, so there is no need to leave the
framework. ∎

### 3.7 Direct scalar power fingerprint — sound one-round alternative

Instead of retaining `H` and restricting its evaluation point as in §3.K, one can replace the
equality-kernel batching directly by

```
G(τ) := Σ_i τ^{⟨i⟩} c_i.
```

Here `⟨i⟩ = Σ_j i_j2^j`. This is univariate of degree less than the padded constraint-table size,
and it is zero exactly when every coefficient `c_i` is zero. The same independent-seed
`SS(F,2,D)` proof and shared-seed plain-SS proof therefore apply.

Contrary to the earlier version of this note, this choice does **not** destroy the tensor
structure needed by sumcheck. The Boolean weight `τ^{⟨i⟩}` is the evaluation at `i` of the public
multilinear polynomial

```
W_τ(X) := ∏_j ((1-X_j) + X_j · τ^(2^j)),
```

so `W_τ(i)=τ^{⟨i⟩}` and it can replace `eq̃(τ_vector,i)` in the structured multiplier at the same
per-variable degree. Direct power batching makes the coefficient-extraction theorem especially
simple, but it changes Eqs. (22)–(23) and the downstream public multiplier. The Kronecker-curve
rendering is preferred because it obtains the same `D`, tree size, and error while leaving the
paper's `H_0`, `H_α`, and sumcheck formulas intact. Algebraically the two versions are basis
changes of the same degree-`<2^m` Reed–Solomon fingerprint. ∎

## 4. Recommendation and status

- **Adopted rendering (plan F6):** use the one-round independent-seed Kronecker challenge of
  §3.K, with `ℓ=2` and `k=D=max(2^m_0,2^m_α)`. Derive the vector points from the two scalar
  seeds and retain the paper's `H_0`, `H_α`, and downstream sumchecks unchanged. The shared-seed
  plain-SS variant is available if minimizing the extraction tree matters more than preserving
  independence between the two tests.

- **Replace Lemma 10:** use the corrected statement in §3.K.3. The *shape* `SS(F,2,D)` can stay,
  but its coordinates must be scalar curve seeds, its family has `2D−1` transcripts, and
  `D` is the maximum padded constraint-table size. It is not the paper's
  `max(2d,2b−1)`.

- **Fix parameter provenance:** `2d` belongs to the scalar `α` interpolation of Lemma 9;
  `2b+1` belongs to the degree-`2b` range sumcheck rounds of Lemma 11; and corrected Lemma 10
  uses `D=max(N_0,N_α)` because those are the dimensions of the two multilinear coefficient
  spaces.

- **Record the protocol deviation accurately:** round count and checked equations are unchanged,
  but the points are sampled from Kronecker curves rather than uniformly from the full vector
  spaces. Under Fiat–Shamir, squeeze two scalar seeds and expand them by repeated squaring.

- **Formalization impact:** the negative result of §2 remains useful as a regression test. The
  repair requires (i) injectivity of `LinearMvExtension.powAlgHom` on multilinear polynomials,
  (ii) the existing degree bound for that map, (iii) univariate root counting, and (iv) a
  one-round `CWSSStructure` with two scalar coordinates and parameter `D`. No seam-relation
  induction, new grid predicate, or non-CWSS soundness framework is needed. Lemma 8's existing
  star-based folding proof is unaffected.

## Appendix: statements suitable for formalization

**Pseudo-code sketches, not compilable Lean.** In the repo, `MultilinearPoly` is the
degree-restricted subtype `L⦃≤ 1⦄[X Fin ℓ]`; evaluation goes through `.val`; `eqTilde` is the
scalar equality kernel and `eqPolynomial` its polynomial form. The exact names below are
indicative.

```
-- The Kronecker point underlying the one-round challenge.
def kroneckerPoint (m : ℕ) (ρ : F) : Fin m → F :=
  fun j => ρ ^ (2 ^ j.val)

-- The missing companion to the existing
-- `LinearMvExtension.powAlgHom_of_restrict_degree_natDegree` bound.
theorem powAlgHom_injective_on_multilinear {F} [CommRing F] [Nontrivial F] {m : ℕ} :
    Function.Injective (fun H : MultilinearPoly F m =>
      LinearMvExtension.powAlgHom H.val)

-- Evaluation of the univariate pullback agrees with evaluation on the curve.
theorem eval_powAlgHom_eq_eval_kronecker {F} [CommRing F] {m : ℕ}
    (H : MultilinearPoly F m) (ρ : F) :
    Polynomial.eval ρ (LinearMvExtension.powAlgHom H.val) =
      H.val.eval (kroneckerPoint m ρ)

-- One-round, two-seed corrected Lemma 10.
theorem zeroCheck_kronecker_coordinateWiseSpecialSound
    (m0 mα : ℕ) (D : ℕ := max (2 ^ m0) (2 ^ mα))
    (hcard : D ≤ Fintype.card F) :
    CoordinateWiseSpecialSound
      (ell := 2)
      (k := D)
      zeroCheckRelation

-- Optional shared-seed version: ordinary D-special soundness.
theorem zeroCheck_kronecker_specialSound
    (m0 mα : ℕ) (D : ℕ := max (2 ^ m0) (2 ^ mα))
    (hcard : D ≤ Fintype.card F) :
    SpecialSound D zeroCheckRelation

-- The following lemmas support only the uniform-challenge zipped fallback.

-- Lemma C: the one-variable interpolation kernel used by both arms of a zipped node.
theorem multilinear_eq_zero_of_two_instantiations {F} [Field F] {m : ℕ}
    (H : MultilinearPoly F (m + 1)) {u v : F} (huv : u ≠ v)
    (hu : instantiateFirst H u = 0)
    (hv : instantiateFirst H v = 0) : H = 0

-- One paired SS(F,2,2) node removes one variable from each independent identity.
theorem zipped_pair_step {F} [Field F] {m0 m1 : ℕ}
    (H0 : MultilinearPoly F (m0 + 1))
    (H1 : MultilinearPoly F (m1 + 1))
    {a a' b b' : F} (haa' : a ≠ a') (hbb' : b ≠ b')
    (h0_center : instantiateFirst H0 a = 0)
    (h0_xSibling : instantiateFirst H0 a' = 0)
    (h1_center : instantiateFirst H1 b = 0)
    (h1_ySibling : instantiateFirst H1 b' = 0) :
    H0 = 0 ∧ H1 = 0

-- Equality-kernel basis nondegeneracy: the R_0 bridge.
theorem eqTilde_batch_eq_zero_iff {F} [CommRing F] [Nontrivial F] {m : ℕ}
    (c : (Fin m → Fin 2) → F) :
    (∑ i, (eqPolynomial i) * C (c i)) = 0 ↔ ∀ i, c i = 0

-- The fallback zero-check extractor, parameterized by the zipped round schedule.
theorem zeroCheck_zipped_coordinateWiseSpecialSound
    (m0 m1 : ℕ)
    (ell : Fin (max m0 m1) → ℕ := fun j =>
      (if j < m0 then 1 else 0) + (if j < m1 then 1 else 0)) :
    CoordinateWiseSpecialSound
      challengeSets ell
      (fun _ => 2)
      zeroCheckRelation

-- Optional only: grid interpolation, not needed by the adopted repair.
theorem multilinear_eq_zero_of_grid {F} [Field F] {m : ℕ}
    (H : MultilinearPoly F m) (S : Fin m → Finset F)
    (hS : ∀ j, 2 ≤ (S j).card)
    (h : ∀ p ∈ Fintype.piFinset S, eval p H = 0) : H = 0

-- Negative regression example: a one-round star does not identify a 2-variate multilinear polynomial.
example : ∃ (H : MultilinearPoly F 2),
    H ≠ 0 ∧ (∀ p on the axis cross through (a,b), eval p H = 0)
```
