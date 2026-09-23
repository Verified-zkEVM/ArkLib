# BCGM25 MCA generators: paper-to-Lean map

Maps Bordage–Chiesa–Guan–Manzur, *All Polynomial Generators Preserve Distance with Mutual
Correlated Agreement* (`BCGM25`, https://eprint.iacr.org/2025/2051) onto ArkLib's
`ArkLib/Data/CodingTheory/ProximityGenerator/` layer, and records where the formalization
departs from the paper as printed.

Declaration docstrings in those files state what each declaration says; the correspondence to
paper items, and the argument for the departures, live here.

Checked against the ePrint version of 2025 held at `~/abf26-refs/BCGM25.pdf`. Paper items are cited
by number, so re-check them against the version in hand before relying on a row.

## Definitions

| Paper | Lean | Notes |
|---|---|---|
| Def 3.2 (`F`-linear code, `Σ` an `F`-vector space) | `ModuleCode ι F A` | The paper's alphabet generality is why the layer takes a module alphabet `A`, not `F` |
| Def 3.3 (`k`-interleaving) | `Code.ModuleCode.moduleInterleavedCode` | Row-wise; `Code.projectedCodeSubmod_moduleInterleavedCode_iff` projects it; `Code.minRelHammingDistCode_moduleInterleavedCode` shows it preserves `δᵣ` |
| Def 3.7 (projected code) | `LinearCode.projectedCodeSubmod` | |
| Def 3.10 (generator) | `CoreDefinitions.Generator` | |
| Def 3.11 (zero-evading) | `CoreDefinitions.IsZeroEvadingGenerator` | |
| Def 3.12 (MDS generator) | `CoreDefinitions.IsMDSGenerator` | |
| Def 3.14 (MCA event and error) | `CoreDefinitions.IsMCA`, `CoreDefinitions.mcaError`, `CoreDefinitions.IsMCAGenerator` | Event and value are separate; the predicate is the value's bound |
| Def 3.19 (polynomial generator) | `CoreDefinitions.IsPolynomialGenerator`, `CoreDefinitions.IsPolynomialGeneratorOf`, `CoreDefinitions.IsPolynomialGeneratorOfFull` | The `Of` forms carry the polynomial family as data; `Full` fixes each seed set to `F` |
| Def 4.3 (tensor generator) | `CoreDefinitions.TensorGenerator`, `CoreDefinitions.TensorGenerator_Explicit` | Agree under `tensorProductPiFunEquiv`; the `s`-fold iteration is `PolynomialGenIsMCA.tensorGeneratorPi` |
| Error of Thm 6.1 | `mdsMCAError` | Reads the code only through `n` and `δᵣ` (`mdsMCAError_congr`). Its unique-decoding regime is `(⌊n·γ⌋ + 1)·(ℓ - 1) / |S|`, not the printed `max{n·γ, 1}·(ℓ - 1) / |S|`, which is false — see below |
| Def 8.1 (`ξ`, univariate-powers error) | `PolynomialGenIsMCA.powersMCAError` | `mdsMCAError` at output size `d + 1` (`mdsMCAError_eq_powersMCAError`, proved), so it carries the same unique-decoding correction |
| Def 9.1 (`ϵMCA,RS`, Reed–Solomon error) | `RSCode.reedSolomonMCAError` | Free `n` of the paper is `Fintype.card ι`; `[NeZero k]` excludes the `ρ = 0` degeneracy |

The paper types `ϵMCA : [0,1] → [0,1]`; ArkLib types the bound `I → ℝ≥0`. The codomain is widened
because `I` carries no `Add` and no ℕ-`SMul`, so the error arithmetic of Lemma 4.4 and Lemma 10.1
is unstatable in it. Bounds are therefore vacuous once they exceed `1`.

## Results

| Paper | Lean | Status |
|---|---|---|
| Lemma 3.6 (any `k` rows of an MDS generator matrix are independent), one direction | `isUnit_of_isMDSGenerator` | proved, for `k = ℓ` the full dimension of `C_G`: any `ℓ` distinct rows of `M_G` form an invertible matrix |
| Lemma 3.13 (an MDS generator is zero-evading with error `(ℓ - 1) / |S|`) | `card_filter_dotProduct_eq_zero_le_of_isMDSGenerator` (field alphabet), `card_filter_sum_smul_eq_le_of_isMDSGenerator` (module alphabet, two families) | proved as seed counts: at most `ℓ - 1` seeds, rather than as an `IsZeroEvadingGenerator` bound |
| Lemma 3.16 (monotone in the distance) | `CoreDefinitions.mcaError_mono` | proved |
| Lemma 4.1 (right multiplication by a matrix with a left pseudoinverse) | `LinearTransformations.mcaError_generatorByRightMul_le`, `LinearTransformations.pseudoinverseGen` | proved |
| Cor 4.2 (projection onto a subset of outputs) | `LinearTransformations.mcaError_projectedGenerator_le`, `LinearTransformations.generatorSubset` | proved |
| Lemma 4.4 (tensor generator), printed statement | `LinearTransformations.isMCAGenerator_tensorGenerator_tight` | **sorried, open** — see below |
| Lemma 4.4, provable forms | `TensorMCA.isMCAGenerator_tensorGenerator_of_moduleInterleavedCode` (interleaved hypothesis, printed error), `TensorMCA.isMCAGenerator_tensorGenerator` (printed hypothesis, error scaled by `ℓ`) | proved |
| Lemma 4.4, `s`-fold iterations | `PolynomialGenIsMCA.isMCAGenerator_tensorGeneratorPi` (consumes the open form), `PolynomialGenIsMCA.isMCAGenerator_tensorGeneratorPi_tight` (δᵣ-anchored factor hypothesis, routed through the proved interleaved form) | the `tight` variant is sorry-free |
| Remark 3.20 (polynomial ⇒ zero-evading) | `PolynomialGenerator.poly_gen_is_zero_evading` | proved, total-degree variant |
| Lemma 3.22 (MCA implies CA) | — | not formalized; this is what licenses reading an `mcaError` bound as a correlated-agreement threshold statement |
| Lemma 7.1 (affine lines to affine spaces) | `AffineMCAMain.isMCAGenerator_affineSpaceGenerator_of_affineLineGenerator` | proved over module alphabets, at `ℓ ≥ 1` where the paper states `s ≥ 2`. At `ℓ = 1` the affine space generator *is* the affine line generator and the conclusion is immediate, since the scaled error `(1 - 1/|F|)⁻¹ · ϵMCA` only exceeds `ϵMCA`; the proof covers that case uniformly |
| Thm 6.1 (MCA for **MDS** generators) | `isMCAGenerator_of_isMDSGenerator` | **sorried in the list-decoding regime**; the proof splits on the regime and closes the unique-decoding one by Lemma 6.2 below, at the corrected error. Stated over module codes, matching the paper's `Σ`-generality; the error depends on the code only through `n` and `δᵣ`, which is what lets it discharge the interleaved hypotheses of the tight tensor induction. The restricted-seed univariate instance is `PolynomialGenIsMCA.isMCAGenerator_univariatePowersGeneratorOn` |
| Lemma 6.2 (Thm 6.1, unique-decoding regime) | `mcaError_le_mdsMCAError_of_lt`, seed count `card_filter_isMCA_le_of_isMDSGenerator` | proved, at error `(⌊n·γ⌋ + 1)·(ℓ - 1) / |S|`, stated pointwise at every radius below `δ_C / (ℓ + 1)` as the paper does. The printed error `max{n·γ, 1}·(ℓ - 1) / |S|` is false and the paper's own argument gives the corrected one — see below |
| Thm 8.2 (polynomial generators, arbitrary linear codes) | `PolynomialGenIsMCA.isMCAGenerator_of_isPolynomialGeneratorOf` | proved **assuming only Thm 6.1**: the tensor stage is the sorry-free `isMCAGenerator_tensorGeneratorPi_tight`, so the open Lemma 4.4 is not on its path. Strengthenings over the paper: no `ℓ ≥ 2` hypothesis, and the `d = 0` factor case (skipped by the paper's proof) is proved via the vacuous-event argument |
| Lemma 9.3 (`G_d` for Reed–Solomon) | `RSCode.isMCAGenerator_univariatePowersGenerator` | **sorried**; needs the Guruswami–Sudan machinery |
| Thm 9.2 (polynomial generators, Reed–Solomon up to Johnson) | `RSCode.isMCAGenerator_of_isPolynomialGeneratorOfFull` | proved assuming Lemma 9.3 **and** the open printed Lemma 4.4 — the latter dependence mirrors a gap in the paper's own proof, see below |
| Lemma 10.1 (`ϵMCA(C^k) ≤ k · ϵMCA(C)`) | — | not formalized |

## Lemma 6.2: the printed unique-decoding error is off by one

Lemma 6.2 (and so the first regime of Thm 6.1) prints the error `max{n·γ, 1}·(ℓ - 1) / |S|` for
`γ < δ_C / (ℓ + 1)`. Write `e := ⌊n·γ⌋`. The bound holds for `e = 0`, where it is the
zero-evading error `(ℓ - 1) / |S|` of Lemma 3.13, and fails for every `e ≥ 1`:

Take the affine line generator `G(x) = (1, x)` over `F` (so `ℓ = 2`, `S = F`, `C_G = RS[F, F, 2]`
is MDS of dimension `2`), any linear code `C` with `(ℓ + 1)·e < d_C`, a set `E` of `e + 1`
positions, and words `u₁ := η₁`, `u₂ := η₂` supported on `E` with pairwise distinct ratios
`η₁[i] / η₂[i]`, `i ∈ E`. For `x_i := -η₁[i] / η₂[i]` the combination `u₁ + x_i·u₂` vanishes at
`i` and is supported on `E \ {i}`, so it agrees with the codeword `0` on `T := [n] \ (E \ {i})`,
`|T| = n - e ≥ n·(1 - γ)`. But `u₁|_T ∉ C|_T`: a codeword agreeing with `u₁` on `T` would be a
nonzero codeword supported on `E`, of weight `e + 1 < d_C`. So all `e + 1` seeds `x_i` witness
the MCA event, whereas the printed bound allows `n·γ·(ℓ - 1) = e` of them when `n·γ` is an
integer. Concretely, `F = 𝔽₇`, `C = RS[𝔽₇, 𝔽₇, 2]` (`n = 7`, `d_C = 6`), `γ = 1/7`: two bad
seeds against a printed bound of one. A brute-force check of this family at `p ∈ {7, 11}`,
`e ∈ {1, 2}` finds exactly `e + 1` bad seeds each time.

The slip is in the sentence "By Lemma 5.3 and its proof, this implies that the correlated
agreement set `T̃` has size `|T̃| > n·(1 - γ)`". The double counting behind Lemma 5.3 gives
`(n - |T̃|)·(|B| - (ℓ - 1)) ≤ |B|·e`, which under the standing assumption `|B| > (e + 1)(ℓ - 1)`
yields only `n - |T̃| ≤ e`, not `n - |T̃| < n·γ`. Feeding that into the final count
`|B| ≤ (n - |T̃|)·(ℓ - 1)` gives `|B| ≤ e·(ℓ - 1)`, contradicting `|B| > (e + 1)(ℓ - 1)`; so the
argument proves `|B| ≤ (e + 1)·(ℓ - 1)` and no more. The example above attains it, so
`(⌊n·γ⌋ + 1)·(ℓ - 1) / |S|` is the tight unique-decoding error of this argument, and it is what
`mdsMCAError` and (through `mdsMCAError_eq_powersMCAError`) `powersMCAError` carry. Below `1/n` it coincides with the printed value. The formal proof in
`ArkLib/Data/CodingTheory/ProximityGenerator/MDSGenerator.lean` follows the paper's argument
with this correction: it is the seed count `card_filter_isMCA_le_of_isMDSGenerator`, converted to
an `mcaError` bound by `CoreDefinitions.mcaError_le_of_exists_exceptional_set`.

## Lemma 4.4: the printed statement is open

Lemma 4.4 assumes both generators have MCA for `C` and concludes error `ϵMCA + ϵ′MCA`. Its proof
splits the tensor event by the law of total probability and bounds Equation (5), whose clauses are

- `∀ i ∈ [ℓ]`, `(Σ_j G′(x′)_j u_{(i,j)})|_T ∈ C|_T`, and
- `∃ k ∈ [ℓ] × [ℓ′]`, `u_k|_T ∉ C|_T`,

by "ϵ′MCA(γ), the MCA error of G′". A single application of `G′`'s MCA at a fixed family does not
give this. The bad index `k = (i₀, j₀)` is determined by the event and so depends on the outer seed
`x′`, which means the family fed to `G′` is not fixed. Two ways out:

1. Apply `G′`'s MCA to the `ℓ`-fold interleaving `C^ℓ ⊆ (Σ^ℓ)ⁿ` with the family
   `w_j := (u_{(1,j)}, …, u_{(ℓ,j)})`. The `∀ i` clause is exactly membership in the interleaved
   projected code, `w` does not depend on `x′`, and the printed error is reached.
   → `TensorMCA.isMCAGenerator_tensorGenerator_of_moduleInterleavedCode`, hypothesis at the interleaving.
2. Union-bound over the `ℓ` rows, paying a factor `ℓ`.
   → `TensorMCA.isMCAGenerator_tensorGenerator`, hypothesis as printed, error
   `ϵMCA + ℓ · ϵ′MCA`.

`TensorMCA.isMCAGenerator_of_moduleInterleavedCode` shows form 1's hypothesis is a strengthening of
form 2's, so the two do not subsume one another. The printed statement itself is in-tree as the
sorried `LinearTransformations.isMCAGenerator_tensorGenerator_tight`.

That the printed error is *unreachable* from the printed hypothesis is not claimed and is not
known — no separation at equal error is exhibited here or in the paper. What is established is that
the paper's own argument does not reach it.

Closing the gap by this route needs `ϵMCA(C^ℓ) ≤ ϵMCA(C)`. The exact transfer
`CoreDefinitions.mcaError_moduleInterleavedCode_le_of_card_le` supplies it when the inner
generator's seed space has at most `|F|` elements. The printed Lemma 4.4 has no such seed-size
condition, so its full stated hypothesis still needs a stronger interleaving bound or another
argument.

### Where the two headline theorems stand relative to the open lemma

BCGM25 invokes Lemma 4.4 twice, with different outcomes in-tree.

- **Thm 8.2** (polynomial generators) does **not** need it. The base MCA comes from Thm 6.1,
  whose error reads the code only through `n` and `δᵣ` (`mdsMCAError_congr`), both preserved by
  interleaving (`Code.minRelHammingDistCode_moduleInterleavedCode`). The δᵣ-anchored induction
  `isMCAGenerator_tensorGeneratorPi_tight` therefore discharges every interleaved hypothesis
  through the proved form 1, and `isMCAGenerator_of_isPolynomialGeneratorOf` reaches the paper's
  exact error with Thm 6.1 as its only sorried input.
- **Thm 9.2** (Reed–Solomon, list-decoding regime) genuinely needs it. The base MCA comes from
  Lemma 9.3, which is Reed–Solomon-specific: its proof constructs the Guruswami–Sudan polynomial
  `Q(X, Y, Z)` of `BCIKS20` Thm 5.1 and factors `disc*_Y(Q)`. The interleaving `RS^ℓ ⊆ (F^ℓ)ⁿ`
  is not a Reed–Solomon code, so the interleaved hypothesis is not available at error `ϵ′MCA`,
  and `isMCAGenerator_of_isPolynomialGeneratorOfFull` consumes the open
  `isMCAGenerator_tensorGenerator_tight` (via `isMCAGenerator_tensorGeneratorPiUnivariate`).

## A separate gap in the source

The proof of Thm 9.2 writes "By Lemma 9.3, `G_d` has mutual correlated agreement for any linear
code `C` with error `ϵMCA,RS,d`", but Lemma 9.3 is stated only for `RS[F, D, k]`. The parallel
sentence in the proof of Thm 8.2 ("for any `F`-linear code `C`") *is* justified, by Thm 6.1; the
Thm 9.2 one is not justified by the lemma it cites. Thm 9.2's printed error therefore does not
follow from its printed proof, independently of anything in the formalization. Were Lemma 9.3 in
fact alphabet-general, the interleaved hypothesis would be dischargeable there too.
