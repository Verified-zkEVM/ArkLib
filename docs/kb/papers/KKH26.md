---
kind: paper
bibkey: KKH26
title: "Failure of Proximity Gaps Close to Capacity"
year: "2026"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2026/782
source_metadata: ../sources/KKH26/metadata.yml
status: seeded
related_modules:
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/KKH26.lean
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/KKH26SumSet.lean
  - ArkLib/Data/CodingTheory/ListDecodability/Bounds/KKH26Asymptotic.lean
  - ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds/NearCapacity.lean
  - ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean
---

# KKH26

## At A Glance

`KKH26` is Krachun–Kazanin–Haböck, *Failure of proximity gaps close to capacity*, ePrint 2026/782 —
for Reed-Solomon codes over smooth multiplicative subgroups of prime fields, both the list size and
the number of close points on a line that is not entirely close reach `n^{τ−o(1)}` at distance
`Θ(1/log n)` below the code distance.

It is the source of [ABF26] Theorem 3.15 (the list-size lower bound; absent from the 2026-04-08
PDF) and Theorem 4.17 (the CA lower bound near capacity; Theorem 4.16 in that PDF), numbered as in
[ABF26](ABF26.md).

## What ArkLib Uses From This Paper

Page numbers are those of the 16-page ePrint PDF.

- **Proposition 3** (p. 15), Appendix A's form of Theorem 1, Item 2: for `τ ≥ 1`, `δ ∈ (0,1)`
  and `β > max{τ+1, 12/5}`, there are infinitely many `n = 2^b` and primes `p ≡ 1 mod n`,
  `p = Θ(n^β)`, with codes `RS[F_p, H, k]` on a multiplicative subgroup `H` of size `n` and of
  distance `δ*`, `|δ* − δ| ≤ 3/(2τ log n)`, and words `u₀, u₁` with
  `|{λ ∈ F_p : Δ(u₀ + λu₁, C) ≤ δ* − 2η}| ≳ n^{τ−o(1)}` and `Δ(u₁, C) ≥ δ* − η`, where
  `η ∼ H₂(ρ)/(τ log n)` and `ρ = 1 − δ`.
- **The Appendix A list** (p. 14): for the centre `u = x^{rm}` and the code `C⁺` of degree at most
  `(r−1)m`, the `r`-subsets of the subgroup `G` of size `s` give
  `|{c ∈ C⁺ : Δ(c, u) ≤ δ⁺ − 1/s}| ≥ C(s, r)`; distinct subsets have distinct vanishing
  polynomials (Remark 5, p. 10).
- **Lemma 1** (p. 6): if `G` is a multiplicative subgroup of `F_p` of power-of-two size `s` and
  `p > s^{s/2}`, then sums of `1 ≤ r ≤ s/2` distinct elements of `G` take at least `2^r · C(s/2, r)`
  values.
- **The Section 2 line** (p. 6): `u₀ = x^{rm}`, `u₁ = x^{(r−1)m}`; `u₀ + c₁u₁` with
  `c₁ = −∑_{x∈S} x` is `(δ* − 2/s)`-close to the code of degree at most `(r−2)m`.

## Main ArkLib Touchpoints

The paper's `r`, `s`, `m` are ArkLib's `k̂`, `h`, `d` (`h = 2^b`, `d = 2^a` in `NearCapacity.lean`);
the paper's `τ` is ArkLib's `c`, and the paper's own `c` is `H₂(ρ)`.

**Proposition 3**, in
[NearCapacity.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds/NearCapacity.lean):

- `rs_epsCa_large_of_smooth`: over any finite field, for a smooth domain of size `n = 2^a · 2^b`
  with `1 ≤ a`, `2 ≤ k̂ ≤ 2^b` and `k = (k̂−1)·2^a`, `ε_ca(RS[F, domain, k], 1 − k̂/2^b) ≥ T/|F|`
  whenever `C(2^b, k̂) ≥ 2T + 1` and `|F| ≥ n + 2kT`. It composes the Appendix A list
  (`choose_le_Lambda_rs_vanilla_of_smooth`) with `le_rs_epsCa_of_le_Lambda` in
  [CS25.lean](../../../ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA/CS25.lean), the
  contrapositive of [CS25] Theorem 2.
- `exists_rs_epsCa_large_near_capacity_of_prime`: for every large `K` and every prime
  `p ≡ 1 (mod 2^K)` with `p ≥ n^{c+2}`, `n = 2^K`, a smooth Reed-Solomon code over `ZMod p` of
  length `n` with `ε_ca(C, 1 − ρ − slack) ≥ n^c / p`.
- `exists_rs_epsCa_large_near_capacity_of_primes`: the family statement
  `NearCapacityCaLowerBound c ρ`, given `NearCapacityPrimeSupply c`.

ArkLib states [ABF26] Theorem 4.17 as `exists_rs_epsCa_large_near_capacity_of_prime`, and as the
family statement `exists_rs_epsCa_large_near_capacity_of_primes` given the prime supply.

| Proposition 3 | `exists_rs_epsCa_large_near_capacity_of_prime` / `NearCapacityCaLowerBound` |
|---|---|
| `τ ≥ 1` | `c : ℝ≥0`; neither statement assumes `0 < c` |
| `ρ = 1 − δ ∈ (0,1)` | `0 < ρ < 1/2` |
| `≳ n^{τ−o(1)}` close points | `ε_ca ≥ n^c / \|F\|`, exactly |
| `β > max{τ+1, 12/5}`, `p = Θ(n^β)` | per prime: `p ≥ n^{c+2}`; family: one `β > max(c+2, 12/5)` with `Kq_lo·n^β ≤ \|F\| ≤ Kq_hi·n^β` |
| `\|δ* − δ\| ≤ 3/(2τ log n)` | `\|k/n − ρ\| ≤ Kρ / log₂ n` |
| radius `δ* − 2η`, `η ∼ H₂(ρ)/(τ log n)` | radius `1 − ρ − slack`, `K₁/log₂ n ≤ slack ≤ K₂/log₂ n` |
| `Δ(u₁, C) ≥ δ* − η` | `epsCa` takes the supremum over pairs that are not jointly close |
| `H` a multiplicative subgroup of size `n` | `[ReedSolomon.Smooth domain]`, `Fintype.card ι = 2^K` |

**The Appendix A list and Theorem 3.15**, in
[KKH26.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/KKH26.lean):
`usefulFamily_list_lower_bound` turns a useful family into a list of its size;
`choose_le_Lambda_rs_vanilla` gives `Λ(C, δ_min(C) − (k̂d − k + 1)/n) ≥ C(h, k̂)` for
`(k̂−1)d < k ≤ k̂d`, which at `k = (k̂−1)d + 1` is the list of p. 14 at radius `δ⁺ − 1/s`.
`Smooth.exists_pow_projection_structure` supplies the projection `x ↦ x^d` for a smooth domain,
and `choose_le_Lambda_rs_vanilla_of_smooth` restates the bound over `[Smooth domain]`. The module
also has antipodal-pair variants (`choose_le_Lambda_rs_antipodal_even`,
`choose_le_Lambda_rs_antipodal_odd`). `exists_rs_asymptotic_Lambda_lower_bound` in
[KKH26Asymptotic.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/KKH26Asymptotic.lean)
is [ABF26] Theorem 3.15, derived from `choose_le_Lambda_rs_vanilla_of_smooth`.

**Lemma 1**: `two_pow_mul_choose_le_card_sumSet` in
[KKH26SumSet.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/KKH26SumSet.lean),
for a subgroup of `(ZMod q)ˣ`, with the sum-set `sumSet`.

**The Section 2 line**: `sumSet_card_div_le_epsCa` in
[KKH26.lean](../../../ArkLib/Data/CodingTheory/ListDecodability/Bounds/KKH26.lean) gives
`ε_ca(RS[F, L, k], 1 − k̂/h) ≥ |Λ_𝒮| / |F|` for `(k̂−2)d < k ≤ (k̂−1)d`, with witness pair
`(x^{k̂d}, −x^{(k̂−1)d})`.

## Version Notes

Theorem 1 (p. 3) states the distance as `δ* = δ + o(1/log n)`; Proposition 3 (p. 15) states
`|δ* − δ| ≤ 3/(2τ log n)`. ArkLib states `|k/n − ρ| ≤ Kρ / log₂ n` for some `Kρ > 0`: the order
of Proposition 3's bound, without its constant.

The module docstring of `CapacityBounds.lean` numbers the near-capacity theorem 4.16, as the
2026-04-08 [ABF26] PDF does; the audit ledger uses 4.17.

## Known Divergences From ArkLib

ArkLib's `ReedSolomon.code domain k` has degree less than `k`; the paper's `RS[F, D, k]` has degree
at most `k` (p. 1).

Proposition 3's line quotients by `X^m − z^m` (p. 15), with `z` chosen through Lemma 3
(pp. 13-14), for the code of degree at most `(r−2)m`. ArkLib reaches the bound through [CS25]
Theorem 2. Appendix A credits [CS25] and [BCHKS25] with building a bad line from a bad
list-decoding centre by quotienting, and roots the technique in [BenSassonGKS20] (p. 13). ArkLib's
CA code is `RS[(k̂−1)·2^a]` (degree less than `(r−1)m`) at the same radius `1 − r/s`, so its gap
to its own rate is `1/s` where the paper's code has about `2/s`.

The bound is exactly `n^c / |F|` in place of `n^{τ−o(1)}`. The per-prime statement asks for
`p ≥ n^{c+2}`, which gives the `|F| ≥ n + 2kT` of `le_rs_epsCa_of_le_Lambda`; the paper uses
`p > n^{τ+1}` (p. 14) for Lemma 3. The rate is restricted to `ρ < 1/2`. The family statement
asserts one `β`, the paper every `β > max{τ+1, 12/5}`. The code is on a smooth domain
(`ReedSolomon.Smooth`, a coset of a power-of-two subgroup), not asserted to be a subgroup.

The list witness is `w_S = f − V_S(x^d)`, the codeword that agrees with the centre `f` on the
fibres over `S`. The paper names the list member as `v_S(X^m)` (p. 14) and as `p_{S'}` (p. 10);
the codewords that agree with the centre there are `u − v_S(X^m)` and `−p_{S'}`.

## Open Formalization Gaps

- The prime supply. `exists_rs_epsCa_large_near_capacity_of_primes` takes `NearCapacityPrimeSupply c`
  as a hypothesis:
  for one `β > max(c+2, 12/5)` and infinitely many `K`, a prime `p ≡ 1 (mod 2^K)` with
  `n^β ≤ p ≤ 2n^β`. The paper takes it from Thorner and Zaman's prime number theorem in
  arithmetic progressions for smooth moduli (p. 3; Appendix A step 2, p. 14). ArkLib does not
  formalize it, since no proof system in ArkLib needs it. The other declarations above are
  proved.
- Theorem 1, Item 1 over prime fields: `exists_rs_asymptotic_Lambda_lower_bound` takes the
  existence of smooth domains of every size `2^K` as its `supply` hypothesis, and its conclusion
  lets the field be any finite field, not only a prime field. Over prime fields, `supply` can be
  discharged with Mathlib's `Nat.exists_prime_gt_modEq_one` and the private
  `exists_smooth_domain_zmod` in `NearCapacity.lean`; ArkLib does not do this.
- Propositions 1, 2 and 4, and Lemmas 2 and 3. `sumSet_card_div_le_epsCa` and
  `two_pow_mul_choose_le_card_sumSet` are not combined into Proposition 1.

## Source Access

- Source metadata: [`../sources/KKH26/metadata.yml`](../sources/KKH26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
