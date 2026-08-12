/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Folded Reed-Solomon codes (ABF26 §2.4)

ABF26 Definitions 2.14 and 2.15: the folded Reed-Solomon code `FRS[F, L, k, s, ω]`
and the `(L, s)`-admissibility condition on the folding element `ω`.

## Main definitions

- `ReedSolomon.Folded.Admissible` — ABF26 Definition 2.14 (strengthened; see below).
- `ReedSolomon.Folded.frsEvalOnPoints` — F-linear FRS evaluation map.
- `ReedSolomon.Folded.frsCode` — ABF26 Definition 2.15 [GR08].
- `ReedSolomon.Folded.foldedDomain` — the `s · |ι|` folded evaluation points packaged as an
  embedding `ι × Fin s ↪ F`.

## Main lemmas

- `ReedSolomon.Folded.admissible_foldedPoints_injective` — admissibility (plus `ω ≠ 0`) is
  exactly injectivity of `(x, j) ↦ domain x · ω^j`; the workhorse of the file.
- `ReedSolomon.Folded.Admissible.subset` — admissibility restricts along `L' ⊆ L`, so every
  statement below can hypothesise it at the canonical point set `Finset.univ.map domain`.
- `ReedSolomon.Folded.mem_frsCode_iff` / `mem_frsCode_iff_flipped` — paper-style
  membership characterisation.
- `ReedSolomon.Folded.frsCode_eq_map_rsCode` — **GR08 Definition 2.1's own framing**:
  the FRS code is the *plain* Reed-Solomon code on the folded domain, transported along
  the currying equivalence `(ι × Fin s → F) ≃ₗ[F] (ι → Fin s → F)`.
- `ReedSolomon.Folded.frsEvalOnPoints_domRestrict_injective` — the FRS encoder is
  injective on `degreeLT F k` when `ω` is admissible, `ω ≠ 0` and `k ≤ s · |ι|`.
- `ReedSolomon.Folded.dim_frsCode` — `Module.finrank F (frsCode …) = k` under
  admissibility of `ω`, `ω ≠ 0` and `k ≤ s · |ι|` (a 4-line transport of
  `ReedSolomon.dim_eq_deg_of_le` along `frsCode_eq_map_rsCode`).
- `ReedSolomon.Folded.minDist_frsCode` — the file's headline theorem: the minimum
  *block* (per-fold) distance is `|ι| − ⌊(k−1)/s⌋`. This one genuinely cannot be
  transported from `ReedSolomon.minDist_of_le`: the block metric is not the symbol metric.
- `ReedSolomon.Folded.alphabetRate_frsCode` — the [ABF26] Definition 2.5 rate
  `ρ = k / (s · n)`.
- `ReedSolomon.Folded.frs_rate_distance_of_dvd` — under `s ∣ k`, FRS satisfies the
  [ABF26] Lemma 2.6 MDS rate-distance equation `δ_min = 1 - ρ + 1/n`. This is the
  `minDist_frsCode` docstring's "agrees exactly when `s ∣ k`" clause as a theorem, and it is
  the input `JohnsonBound.Family`'s alphabet-generic Corollary 3.3 asks a module-alphabet
  family to supply (consumed by `CodingTheory.frs_lambda_le_johnson_mds`).
- `ReedSolomon.Folded.mem_frsCode_one_iff_mem_rsCode` /
  `frsCode_one_map_eq_rsCode` — sanity checks for `s = 1` collapse to plain RS,
  both instances of the encoder-generic `ReedSolomon.mem_map_degreeLT_one_iff_mem_code`.

## Not the FRI fold

This is GR08 **alphabet-enlarging** folding: each symbol of a codeword packs the `s` values
`(f̂(x), f̂(xω), …, f̂(xω^{s-1}))`, the degree bound is unchanged, and the code lives in
`ι → Fin s → F`. It is a *different construction* from the FRI/STIR-style **split-and-fold**
elsewhere in the tree, where a random challenge contracts `f(X) = ∑ᵢ Xⁱ fᵢ(X^{2ᵏ})` and the
evaluation domain shrinks — see `ProximityGap/Folding.lean` (`foldWord`),
`Data/Polynomial/SplitFold.lean` (`splitNth`), and `Data/Polynomial/FoldingPolynomial.lean`
(`polyFold`); the "folded RS code" appearing there is a plain RS code on the squared subdomain,
not an FRS code in this file's sense.

## Not the WHIR block distance either

`minDist_frsCode` below is stated in the **block** (per-fold) metric: a position `x : ι`
counts as a disagreement when the whole `s`-tuple `(f̂(x), …, f̂(xω^{s-1}))` differs. That is
just `Code.minDist` on `ι → (Fin s → F)`, i.e. the ordinary Hamming metric over the enlarged
alphabet `Fin s → F` — the blocks are the *fold coordinates*, and they are part of the
codeword's type.

It is **not** `BlockRelDistance` (`Basic/BlockRelDistance.lean`, [ACFY24]/WHIR), which
encodes "block" differently: there the word stays flat (`Fin (2^n) → F`), the blocks are
cosets of a `SmoothCosetFftDomain` selected by a subdomain index `k`, and the distance is
`disagreementSet`-based over `φ.subdomain k`.

The two are *mathematically* the same idea — a block metric on a partition of the evaluation
domain — and on a smooth domain whose blocks are the `ω`-orbits they would agree. But they
are **not interchangeable in Lean**: `BlockRelDistance` is hardwired to `SmoothCosetFftDomain`
and `Fin (2^n) → F`, while `frsCode` carries its blocks in the codeword's *type* over an
arbitrary `ι`, so neither development's lemmas apply to the other as stated. No bridge exists
and none is claimed; a reader should not expect the WHIR lemmas to fire on `frsCode`.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26] (§2.4: Definitions 2.14, 2.15)
* [Guruswami, V., and Rudra, A., *Explicit Codes Achieving List Decoding Capacity:
    Error-Correction With Optimal Redundancy*][GR08] (the original FRS paper; Definition 2.1)
-/

namespace ReedSolomon

namespace Folded

/-- **ABF26 Definition 2.14 (strengthened).** An element `ω : F` is `(L, s)`-admissible
if **every evaluation point appears only once across all folds**, i.e. the map
`(α, i) ↦ α · ω^i : L × Fin s → F` is injective.

Split into two conjuncts to keep the predicate `simp`-friendly:

  - **inter-orbit:** for distinct `α ≠ β ∈ L`, `α · ω^i ≠ β` for every `i < s`.
  - **intra-orbit:** for every `α ∈ L`, `α · ω^i ≠ α` for every `i < s` with `0 < i` —
    equivalently, `ω` has multiplicative order at least `s` on the non-zero
    orbit of `α`.

Both conjuncts lead with the bounded quantifier `∀ i, i < s → …` (rather than `0 < i` first)
so that `Nat.decidableBallLT` fires and concrete admissibility claims are closed by
`by decide`.

**Ordered, not unordered, pairs.** The paper quantifies over the *unordered* pairs
`{α, β} ∈ (L choose 2)`; the inter-orbit conjunct here quantifies over *ordered* distinct
pairs, so it asserts both `α · ω^i ≠ β` and `β · ω^i ≠ α`. That is the reading the
construction needs, not a hedge: `admissible_foldedPoints_injective` normalises a collision
to `m ≤ n` by `rcases le_total`, and the two branches consume the two orders. (At `i = 0`
the conjunct degenerates to `α ≠ β`, which the hypothesis already supplies.)

**Deviation from the paper's literal text.** Definition 2.14 of ABF26 states only the
*inter-orbit* clause (it quantifies over unordered pairs `{α, β} ∈ (L choose 2)`, hence
distinct `α ≠ β`). Its literal reading therefore does *not* forbid `ω^j = 1` for some
`0 < j < s`, which would collapse a fold's `s`-tuple to a repeated-entry vector and
silently weaken the FRS distance argument downstream (T2.18, T4.14). We add the
*intra-orbit* conjunct so that, together with the downstream hypothesis `ω ≠ 0`,
`Admissible` is exactly the GR08 injectivity condition the paper's results actually rely on.
This is a deliberate strengthening, not a verbatim
transcription. It is not merely defensible but *necessary*: with `ω = 1` — which the
paper's literal Def 2.14 permits for every `L` and every `s` — the FRS distance claim is
already false (`F = ZMod 11`, `L` the order-5 subgroup, `s = 2`, `k = 2`: the true minimum
block distance is `4`, whereas `minDist_frsCode`'s formula gives `5`).

**Boundary cases to be aware of.** The predicate does not require `ω ≠ 0` (downstream
lemmas take it as a separate hypothesis), and it excludes `0 ∈ L` only *implicitly* and
only for `s ≥ 2` (the intra-orbit clause fails at `α = 0`); for `s ≤ 1` the intra-orbit
range is empty and `0 ∈ L` is admissible, so consumers needing `0 ∉ L` must state it.

**The exclusion of `0 ∈ L` is load-bearing for ABF26 Theorem 2.18**, not merely for the
distance argument: T2.18 (FRS codes are `(s, τ)`-subspace designs) is *false* when
`0 ∈ L`, even in the presence of its own hypothesis that `ω` has large multiplicative
order. Counterexample: `F = ZMod 5`, `domain = (0, 1)` so `L = {0, 1}` and `n = 2`,
`s = 3`, `k = 2`, `ω = 2` (a generator of `F*`, so `orderOf ω = 4 = |F| − 1` and T2.18's
`hω_gen` hypothesis holds). Taking the one-dimensional `A` spanned by the encoding of `X`,
the whole `s`-orbit of the point `0` degenerates to `0`, so that block contributes
dimension `1` and `Σ / n = 1/2`, while T2.18's bound is
`dim A · τ(1) = (k/n)/(s − 1 + 1) = 1/3`. The intra-orbit conjunct (equivalently, `0 ∉ L`
for `s ≥ 2`) is exactly the missing hypothesis; a consumer working at `s ≤ 1` must add
`0 ∉ L` by hand. -/
def Admissible {F : Type*} [Field F]
    (L : Finset F) (s : ℕ) (ω : F) : Prop :=
  (∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β) ∧
  (∀ α ∈ L, ∀ i : ℕ, i < s → 0 < i → α * ω ^ i ≠ α)

/-- `Admissible` is decidable on concrete parameters: both conjuncts are bounded `∀`s over a
`Finset` (`Finset.decidableDforallFinset`) and over `i < s` (`Nat.decidableBallLT`), which is
why the bounded quantifiers are ordered `∀ i, i < s → …` rather than `∀ i, 0 < i → i < s → …`.
Providing the instance means concrete admissibility claims are closed by plain `by decide`,
with no `unfold` needed. -/
instance decidableAdmissible {F : Type*} [Field F] [DecidableEq F]
    (L : Finset F) (s : ℕ) (ω : F) : Decidable (Admissible L s ω) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Admissibility is monotone downwards in the point set.** Both conjuncts are universally
quantified over `L`, so admissibility on a larger set restricts to any subset.

This is what lets every downstream statement hypothesise admissibility at the canonical point
set `Finset.univ.map domain` — the image of the evaluation embedding — while still being usable
by a caller who only knows admissibility on some ambient `L` containing that image. -/
lemma Admissible.subset {F : Type*} [Field F] {L L' : Finset F} {s : ℕ} {ω : F}
    (h : Admissible L s ω) (hsub : L' ⊆ L) : Admissible L' s ω :=
  ⟨fun α hα β hβ => h.1 α (hsub hα) β (hsub hβ), fun α hα => h.2 α (hsub hα)⟩

/-- The FRS evaluation map as an `F`-linear map from polynomials to `ι → Fin s → F`,
mirroring `ReedSolomon.evalOnPoints` (which is the `s = 1` special case). -/
def frsEvalOnPoints {ι : Type*} {F : Type*} [CommSemiring F]
    (domain : ι ↪ F) (s : ℕ) (ω : F) : Polynomial F →ₗ[F] (ι → Fin s → F) where
  toFun p := fun x j ↦ p.eval (domain x * ω ^ (j : ℕ))
  map_add' p q := by ext; simp
  map_smul' c p := by ext; simp

/-- **ABF26 Definition 2.15 [GR08].** The folded Reed-Solomon code:

  `FRS[F, L, k, s, ω] := { f : L → F^s | ∃ f̂ ∈ F^{<k}[X],`
  `                          ∀ x ∈ L, f(x) = (f̂(x), f̂(x·ω), ..., f̂(x·ω^{s-1})) }`

The fold packages `s` consecutive evaluations of a single underlying polynomial into a
length-`s` vector at each evaluation point. We do not bake the `Admissible` hypothesis
into the definition itself — admissibility is left as a side condition for downstream
statements about distance / list decoding. Note that `FRS[F, L, k, 1, ω] = RS[F, L, k]`
for any `ω`.

**Submodule structure.** Defined as `(Polynomial.degreeLT F k).map (frsEvalOnPoints …)`,
exactly mirroring `ReedSolomon.code`. This makes `frsCode` a `Submodule F (ι → Fin s → F)`
directly — `F`-linear by construction — so downstream theorems (e.g. T2.18, T4.14)
consume it as a `ModuleCode ι F (Fin s → F)` without an existential wrap.

**Typeclass assumptions.** As with the sibling `ReedSolomon.code`, only the ambient algebra
is needed: no `Fintype`/`DecidableEq` on `ι` and no `DecidableEq` on `F`. -/
noncomputable def frsCode {ι : Type*} {F : Type*} [CommSemiring F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) : Submodule F (ι → Fin s → F) :=
  (Polynomial.degreeLT F k).map (frsEvalOnPoints domain s ω)

/-- **Membership of `frsCode` in paper-style form.** A vector `f : ι → Fin s → F` is
in `frsCode domain k s ω` iff there is a polynomial of degree `< k` whose folded
evaluations match `f`. This is the original paper-shaped membership predicate, kept
as a `simp`-able iff lemma. -/
lemma mem_frsCode_iff {ι : Type*} {F : Type*} [CommSemiring F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (f : ι → Fin s → F) :
    f ∈ frsCode domain k s ω ↔
      ∃ p ∈ Polynomial.degreeLT F k,
        ∀ x : ι, ∀ j : Fin s, f x j = p.eval (domain x * ω ^ (j : ℕ)) := by
  simp only [frsCode, Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p, hp, ?_⟩
    intro x j
    rfl
  · rintro ⟨p, hp, hf⟩
    refine ⟨p, hp, ?_⟩
    ext x j
    exact (hf x j).symm

/-- **The `s · |ι|` folded evaluation points are pairwise distinct.** This is the
injective-map reformulation of `Admissible` (its docstring's "every evaluation point
appears only once across all folds"): given `(L, s)`-admissibility of `ω` on
`L = image domain` together with `ω ≠ 0`, the map `(x, j) ↦ domain x · ω^j` on
`ι × Fin s` is injective. The two `Admissible` conjuncts (inter-orbit + intra-orbit)
together with cancellation by the unit `ω^m` are exactly what rules out the two ways a
collision could occur (across distinct base points, or within one orbit). -/
lemma admissible_foldedPoints_injective {ι : Type*} [Fintype ι]
    {F : Type*} [Field F] {s : ℕ}
    (domain : ι ↪ F) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0) :
    Function.Injective (fun xi : ι × Fin s => domain xi.1 * ω ^ (xi.2 : ℕ)) := by
  obtain ⟨hinter, hintra⟩ := hadm
  -- The ordered-exponent core: if `m ≤ n < s` and the two folded points agree, then
  -- the base points and exponents agree. Both `Admissible` clauses feed in here.
  have key : ∀ (a b : ι) (m n : ℕ), m ≤ n → n < s →
      domain a * ω ^ m = domain b * ω ^ n → a = b ∧ m = n := by
    intro a b m n hmn hns heq
    have hωm : ω ^ m ≠ 0 := pow_ne_zero _ hω
    have heq' : domain a = domain b * ω ^ (n - m) := by
      have hn : n = (n - m) + m := by omega
      rw [hn, pow_add, ← mul_assoc] at heq
      exact mul_right_cancel₀ hωm heq
    by_cases hab : a = b
    · subst hab
      rcases Nat.eq_zero_or_pos (n - m) with h0 | hpos
      · exact ⟨rfl, by omega⟩
      · exact absurd heq'.symm
          (hintra (domain a) (Finset.mem_map_of_mem _ (Finset.mem_univ _)) (n - m)
            (by omega) hpos)
    · have hdab : domain a ≠ domain b := fun h => hab (domain.injective h)
      exact absurd heq'.symm
        (hinter (domain b) (Finset.mem_map_of_mem _ (Finset.mem_univ _)) (domain a)
          (Finset.mem_map_of_mem _ (Finset.mem_univ _)) (Ne.symm hdab) (n - m) (by omega))
  rintro ⟨x, i⟩ ⟨y, j⟩ heq
  simp only at heq
  rcases le_total (i : ℕ) (j : ℕ) with hij | hji
  · obtain ⟨hxy, hijv⟩ := key x y i j hij j.isLt heq
    exact Prod.ext hxy (Fin.ext hijv)
  · obtain ⟨hyx, hjiv⟩ := key y x j i hji i.isLt heq.symm
    exact Prod.ext hyx.symm (Fin.ext hjiv.symm)

/-- **The folded evaluation domain as an embedding.** Packages the `s · |ι|` folded
evaluation points `(x, j) ↦ domain x · ω^j` into an embedding `ι × Fin s ↪ F`; the
injectivity certificate is `admissible_foldedPoints_injective`. This is GR08 Definition
2.1's evaluation domain, and it is what makes `frsCode` a *plain* Reed-Solomon code
(see `frsCode_eq_map_rsCode`). -/
def foldedDomain {ι : Type*} [Fintype ι] {F : Type*} [Field F] {s : ℕ}
    (domain : ι ↪ F) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0) : ι × Fin s ↪ F :=
  ⟨fun xi => domain xi.1 * ω ^ (xi.2 : ℕ), admissible_foldedPoints_injective domain ω hadm hω⟩

@[simp]
lemma foldedDomain_apply {ι : Type*} [Fintype ι] {F : Type*} [Field F] {s : ℕ}
    (domain : ι ↪ F) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0) (xi : ι × Fin s) :
    foldedDomain domain ω hadm hω xi = domain xi.1 * ω ^ (xi.2 : ℕ) := rfl

/-- **An FRS code is a plain Reed-Solomon code on the folded domain** — GR08 Definition
2.1's own framing of the construction:

> "the codewords of `FRS_{F,γ,m,k}` are in one-one correspondence with those of the RS code
> `C` and are obtained by bundling together consecutive `m`-tuples of symbols in codewords
> of `C`."

Formally: `frsCode domain k s ω` is the image of `ReedSolomon.code (foldedDomain …) k`
under the currying equivalence `(ι × Fin s → F) ≃ₗ[F] (ι → Fin s → F)`. The "bundling"
of GR08 is exactly `LinearEquiv.curry`, and the RS code on the right is taken over the
enlarged domain of all `s · |ι|` folded points — which is a legitimate RS evaluation
domain precisely because `ω` is `(L, s)`-admissible.

This is the structural reason the FRS *dimension* formula needs no new argument:
`dim_frsCode` is a transport of `ReedSolomon.dim_eq_deg_of_le` along this equality.

**What this does *not* give.** The minimum distance does *not* transport: `minDist_frsCode`
is stated in the *block* (per-fold) Hamming metric on `ι → Fin s → F`, whereas
`ReedSolomon.minDist_of_le` is the *symbol* metric on `ι × Fin s → F`. Currying is not an
isometry between those two metrics, so `minDist_frsCode` needs its own argument. -/
theorem frsCode_eq_map_rsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F] {s : ℕ}
    (domain : ι ↪ F) (k : ℕ) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0) :
    frsCode domain k s ω
      = (ReedSolomon.code (foldedDomain domain ω hadm hω) k).map
          (LinearEquiv.curry F F ι (Fin s)).toLinearMap := by
  ext f
  rw [mem_frsCode_iff]
  simp only [Submodule.mem_map, ReedSolomon.code, ReedSolomon.evalOnPoints,
    LinearEquiv.coe_toLinearMap, LinearEquiv.coe_curry, LinearMap.coe_mk, AddHom.coe_mk,
    foldedDomain_apply]
  constructor
  · rintro ⟨p, hp, hf⟩
    refine ⟨fun xi => p.eval (domain xi.1 * ω ^ (xi.2 : ℕ)), ⟨p, hp, rfl⟩, ?_⟩
    ext x j
    exact (hf x j).symm
  · rintro ⟨g, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, fun x j => rfl⟩

/-- **Injectivity of folded RS evaluation on low-degree polynomials** (the folded
analogue of the kernel-triviality argument behind `ReedSolomon.dim_eq_deg_of_le`). When `ω` is
`(L, s)`-admissible (`L = image domain`), `ω ≠ 0`, and there are at least `k` folded
evaluation points (`k ≤ s · |ι|`), the FRS evaluation map restricted to `degreeLT F k`
is injective: a nonzero polynomial of degree `< k ≤ s · |ι|` cannot vanish at all
`s · |ι|` distinct folded points (`admissible_foldedPoints_injective`).

Kept as a standalone lemma because downstream consumers (e.g. the FRS half of ABF26 T2.18)
need the *encoder-level* injectivity, not just the dimension count; `dim_frsCode` itself is
now obtained by transport along `frsCode_eq_map_rsCode` and does not use this lemma.

No `[NeZero k]` is required: at `k = 0` the domain `degreeLT F 0` is the zero submodule,
so injectivity is automatic. -/
lemma frsEvalOnPoints_domRestrict_injective {ι : Type*} [Fintype ι]
    {F : Type*} [Field F] {k s : ℕ}
    (domain : ι ↪ F) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0)
    (hk : k ≤ s * Fintype.card ι) :
    Function.Injective
      ((frsEvalOnPoints domain s ω).domRestrict (Polynomial.degreeLT F k)) := by
  rw [← LinearMap.ker_eq_bot]
  ext p
  simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_bot]
  constructor
  · intro hfp
    apply Subtype.ext
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · -- `degreeLT F 0 = ⊥`: the only member is the zero polynomial.
      have hdeg := Polynomial.mem_degreeLT.mp p.2
      rw [Nat.cast_zero, Nat.WithBot.lt_zero_iff, Polynomial.degree_eq_bot] at hdeg
      exact hdeg
    · haveI : NeZero k := ⟨by omega⟩
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p := p.val)
        (f := fun xi : ι × Fin s => domain xi.1 * ω ^ (xi.2 : ℕ))
        (admissible_foldedPoints_injective domain ω hadm hω) ?_ ?_
      · rintro ⟨x, j⟩
        exact congrFun (congrFun hfp x) j
      · rw [Fintype.card_prod, Fintype.card_fin]
        calc p.val.natDegree < k := natDegree_lt_of_mem_degreeLT p.2
          _ ≤ s * Fintype.card ι := hk
          _ = Fintype.card ι * s := Nat.mul_comm _ _
  · intro hp
    simp [hp]

/-- **Exact dimension of `frsCode`, for every degree bound.** Under `(L, s)`-admissibility
of `ω` (`L = image domain`) and `ω ≠ 0`, the folded code has dimension
`min k (s · |ι|)`: the message dimension grows with `k` until the `s · |ι|` distinct
evaluation points are saturated.

The proof is a *transport*, not a re-derivation: by `frsCode_eq_map_rsCode` the FRS code is
the plain RS code on the folded domain, currying is an `F`-linear isomorphism (so it
preserves `finrank`), and the RS dimension formula is the pre-existing
`ReedSolomon.dim_eq_min_deg_card`. -/
lemma dim_frsCode_eq_min {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0) :
    Module.finrank F (frsCode domain k s ω) = min k (s * Fintype.card ι) := by
  rw [frsCode_eq_map_rsCode domain k ω hadm hω]
  rw [← (Submodule.equivMapOfInjective (LinearEquiv.curry F F ι (Fin s)).toLinearMap
    (LinearEquiv.curry F F ι (Fin s)).injective _).finrank_eq]
  simpa [LinearCode.dim, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using
    (ReedSolomon.dim_eq_min_deg_card (n := k) (α := foldedDomain domain ω hadm hω))

/-- **Full-dimension regime for `frsCode`.** If `k ≤ s · |ι|`, the exact formula
`dim_frsCode_eq_min` simplifies to dimension `k`. This is the rate fact
`ρ = k / (s · n)` for non-saturated FRS codes. -/
lemma dim_frsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0)
    (hk : k ≤ s * Fintype.card ι) :
    Module.finrank F (frsCode domain k s ω) = k := by
  rw [dim_frsCode_eq_min domain k s ω hadm hω, min_eq_left hk]

/-- **Folded-RS minimum (block) distance** — the folded analogue of
`ReedSolomon.minDist_of_le`. Under `(L, s)`-admissibility of `ω` (`L = image domain`),
`ω ≠ 0`, `0 < s`, and `k ≤ s · |ι|`, a nonzero codeword has at most `⌊(k-1)/s⌋` zero folded
symbols, so

  `Code.minDist (frsCode domain k s ω) = |ι| − ⌊(k-1)/s⌋`.

**How tight is this?** For `k ≥ 1` the right-hand side equals `n − ⌈k/s⌉ + 1` with
`n = |ι|`, so the code meets the *integer* Singleton bound `d ≤ n − ⌈log_{|Σ|}|C|⌉ + 1`
with equality. It is **not** unconditionally MDS in ABF26's sense: ABF26 Lemma 2.6 defines
MDS by `ρ(C) = 1 − δ_min(C) + 1/n` with the real rate `ρ = log_{|Σ|}|C| / n = k/(s·n)`
(Definition 2.5), which would force `d = n − k/s + 1`. That agrees with the truth
`n − ⌈k/s⌉ + 1` exactly when `s ∣ k`; for `s ∤ k` the folded code falls short of the real
Singleton bound by the rounding term `⌈k/s⌉ − k/s`.

**Lower bound** (`≥`, mirrors `ReedSolomon.minDist_of_le`'s weight argument): a nonzero
codeword comes from `p ≠ 0` of degree `< k`; each zero fold packs `s` distinct roots of `p`
(distinct across folds too, by `admissible_foldedPoints_injective`), so `s · (#zero folds) ≤
deg p < k`, giving `#zero folds ≤ ⌊(k-1)/s⌋` and weight `≥ |ι| − ⌊(k-1)/s⌋`.

**Upper bound** (`≤`): the codeword of the degree-`s·⌊(k-1)/s⌋ < k` polynomial
`p = ∏_{x ∈ T, j} (X − domain x · ω^j)` for any `T ⊆ ι` with `|T| = ⌊(k-1)/s⌋` vanishes on
exactly the `T`-folds (the `s·|T|` chosen points are roots; no others are, by full
point-distinctness), so it has weight exactly `|ι| − ⌊(k-1)/s⌋`. -/
theorem minDist_frsCode {ι : Type*} [Fintype ι]
    {F : Type*} [Field F] [DecidableEq F] {k s : ℕ} [NeZero k] (hs : 0 < s)
    (domain : ι ↪ F) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0)
    (hk : k ≤ s * Fintype.card ι) :
    Code.minDist ((frsCode domain k s ω) : Set (ι → Fin s → F))
      = Fintype.card ι - (k - 1) / s := by
  classical
  -- Abbreviations.
  set D := Fintype.card ι - (k - 1) / s with hD
  -- The folded evaluation points are pairwise distinct (the workhorse for both bounds).
  have hinj : Function.Injective (fun xi : ι × Fin s => domain xi.1 * ω ^ (xi.2 : ℕ)) :=
    admissible_foldedPoints_injective domain ω hadm hω
  -- `(k - 1) / s < |ι|`, hence `D + (k-1)/s = |ι|` and `Tᶜ` is nonempty for `|T| = (k-1)/s`.
  have hdiv_lt : (k - 1) / s < Fintype.card ι := by
    rw [Nat.div_lt_iff_lt_mul hs]
    have : k - 1 < s * Fintype.card ι := by
      have hk1 : 1 ≤ k := NeZero.one_le
      omega
    calc k - 1 < s * Fintype.card ι := this
      _ = Fintype.card ι * s := Nat.mul_comm _ _
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (lt_of_le_of_lt (Nat.zero_le _) hdiv_lt)
  rw [LinearCode.dist_eq_minWtCodewords, LinearCode.minWtCodewords]
  refine le_antisymm ?upper ?lower
  · -- UPPER BOUND: exhibit a codeword of weight exactly `D`.
    -- Pick `T ⊆ univ` with `|T| = (k-1)/s`.
    obtain ⟨T, -, hTcard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset ι)) (n := (k - 1) / s)
        (by rw [Finset.card_univ]; exact le_of_lt hdiv_lt)
    -- The chosen evaluation points.
    set P : Finset F := (T ×ˢ (Finset.univ : Finset (Fin s))).image
      (fun xi => domain xi.1 * ω ^ (xi.2 : ℕ)) with hP
    have hPcard : P.card = (k - 1) / s * s := by
      rw [hP, Finset.card_image_of_injective _ hinj,
        Finset.card_product, hTcard, Finset.card_univ, Fintype.card_fin]
    have hPcard_lt : P.card < k := by
      rw [hPcard]
      have hk1 : 1 ≤ k := NeZero.one_le
      calc (k - 1) / s * s ≤ k - 1 := Nat.div_mul_le_self _ _
        _ < k := by omega
    -- The vanishing polynomial.
    set p : Polynomial F := ∏ q ∈ P, (Polynomial.X - Polynomial.C q) with hp
    have hp_ne : p ≠ 0 := by
      rw [hp, Finset.prod_ne_zero_iff]
      exact fun q _ => Polynomial.X_sub_C_ne_zero q
    have hp_natDegree : p.natDegree = P.card := by
      rw [hp, Polynomial.natDegree_prod _ _ (fun q _ => Polynomial.X_sub_C_ne_zero q)]
      simp
    have hp_mem : p ∈ Polynomial.degreeLT F k := by
      rw [Polynomial.mem_degreeLT]
      calc p.degree ≤ (p.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
        _ < (k : WithBot ℕ) := by rw [hp_natDegree]; exact_mod_cast hPcard_lt
    -- Evaluation: `p.eval a = ∏ q ∈ P, (a - q)`, which is `0 ↔ a ∈ P`.
    have heval : ∀ a : F, p.eval a = ∏ q ∈ P, (a - q) := by
      intro a; rw [hp, Polynomial.eval_prod]; simp
    have heval_eq_zero_iff : ∀ a : F, p.eval a = 0 ↔ a ∈ P := by
      intro a
      rw [heval, Finset.prod_eq_zero_iff]
      constructor
      · rintro ⟨q, hq, haq⟩; rwa [sub_eq_zero.mp haq]
      · intro ha; exact ⟨a, ha, by simp⟩
    -- A point `domain x * ω^j` lies in `P` iff `x ∈ T`.
    have hpoint_mem : ∀ (x : ι) (j : Fin s), domain x * ω ^ (j : ℕ) ∈ P ↔ x ∈ T := by
      intro x j
      rw [hP, Finset.mem_image]
      constructor
      · rintro ⟨⟨y, i⟩, hyi, heqyi⟩
        rw [Finset.mem_product] at hyi
        have heq2 : (fun xi : ι × Fin s => domain xi.1 * ω ^ (xi.2 : ℕ)) (y, i)
            = (fun xi : ι × Fin s => domain xi.1 * ω ^ (xi.2 : ℕ)) (x, j) := heqyi
        have := hinj heq2
        simp only [Prod.mk.injEq] at this
        rw [← this.1]; exact hyi.1
      · intro hx
        exact ⟨(x, j), Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, rfl⟩
    -- The codeword.
    set c : ι → Fin s → F := frsEvalOnPoints domain s ω p with hc
    have hc_val : ∀ (x : ι) (j : Fin s), c x j = p.eval (domain x * ω ^ (j : ℕ)) := by
      intro x j; rfl
    -- `c x = 0` (the whole fold) iff `x ∈ T`.
    have hfold_zero : ∀ x : ι, c x = 0 ↔ x ∈ T := by
      intro x
      rw [funext_iff]
      constructor
      · intro h
        have h0 := h ⟨0, hs⟩
        rw [hc_val, Pi.zero_apply, heval_eq_zero_iff] at h0
        exact (hpoint_mem x ⟨0, hs⟩).mp h0
      · intro hx j
        rw [hc_val, Pi.zero_apply, heval_eq_zero_iff]
        exact (hpoint_mem x j).mpr hx
    have hc_mem : c ∈ frsCode domain k s ω := by
      rw [mem_frsCode_iff]
      exact ⟨p, hp_mem, fun x j => rfl⟩
    -- `c ≠ 0` since `Tᶜ` is nonempty.
    have hc_ne : c ≠ 0 := by
      intro h
      -- if `c = 0` then every fold is zero, so `T = univ`, contradicting `|T| < |ι|`.
      have hall : ∀ x : ι, x ∈ T := by
        intro x
        rw [← hfold_zero x]
        exact congrFun h x
      have : (Finset.univ : Finset ι).card ≤ T.card :=
        Finset.card_le_card (fun x _ => hall x)
      rw [Finset.card_univ, hTcard] at this
      omega
    -- Weight of `c` is exactly `D`.
    have hwt : Code.wt c = D := by
      rw [Code.wt]
      have hfilter :
          Finset.filter (fun i => c i ≠ 0) Finset.univ = (Finset.univ \ T) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
        rw [← not_iff_not, not_not, hfold_zero x]
        tauto
      rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ, hTcard,
        hD]
    -- Conclude.
    exact Nat.sInf_le ⟨c, hc_mem, hc_ne, hwt⟩
  · -- LOWER BOUND: every nonzero codeword has weight `≥ D`.
    refine le_csInf ⟨Fintype.card ι, ?nonempty⟩ ?bound
    · -- nonemptiness witness: the all-ones constant codeword has weight `|ι|`.
      refine ⟨frsEvalOnPoints domain s ω (Polynomial.C 1), ?_, ?_, ?_⟩
      · rw [mem_frsCode_iff]
        refine ⟨Polynomial.C 1, ?_, fun x j => rfl⟩
        rw [Polynomial.mem_degreeLT]
        calc (Polynomial.C (1 : F)).degree ≤ 0 := Polynomial.degree_C_le
          _ < (k : WithBot ℕ) := by
                have : 0 < k := NeZero.pos k
                exact_mod_cast this
      · -- nonzero: every fold is the all-ones vector.
        intro h
        have := congrFun (congrFun h (Classical.arbitrary ι)) ⟨0, hs⟩
        simp [frsEvalOnPoints] at this
      · -- weight is `|ι|`.
        rw [Code.wt]
        have : Finset.filter (fun i => frsEvalOnPoints domain s ω (Polynomial.C 1) i ≠ 0)
            Finset.univ = Finset.univ := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          intro hzero
          have := congrFun hzero ⟨0, hs⟩
          simp [frsEvalOnPoints] at this
        rw [this, Finset.card_univ]
    · rintro b ⟨c, hc_mem, hc_ne, hwt⟩
      -- Extract the underlying polynomial.
      rw [mem_frsCode_iff] at hc_mem
      obtain ⟨p, hp_mem, hp_eval⟩ := hc_mem
      -- `p ≠ 0`, else `c = 0`.
      have hp_ne : p ≠ 0 := by
        intro hp0
        apply hc_ne
        ext x j
        rw [hp_eval x j, hp0, Polynomial.eval_zero, Pi.zero_apply, Pi.zero_apply]
      -- The set of zero folds.
      set Z : Finset ι := Finset.filter (fun x => c x = 0) Finset.univ with hZ
      -- Each pair `(x, j)` with `x ∈ Z` maps to a root of `p`; injectively.
      have hZcard : (Z ×ˢ (Finset.univ : Finset (Fin s))).card ≤ p.roots.toFinset.card := by
        apply Finset.card_le_card_of_injOn
          (f := fun xi : ι × Fin s => domain xi.1 * ω ^ (xi.2 : ℕ))
        · rintro ⟨x, j⟩ hxj
          rw [Finset.mem_coe, Finset.mem_product] at hxj
          simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp_ne]
          rw [hZ, Finset.mem_filter] at hxj
          have hcxj : c x j = 0 := by rw [hxj.1.2]; rfl
          rw [hp_eval x j] at hcxj
          exact hcxj
        · exact hinj.injOn
      -- Bound: `s * |Z| ≤ p.natDegree < k`.
      have hsZ_lt : s * Z.card < k := by
        have h1 : (Z ×ˢ (Finset.univ : Finset (Fin s))).card = Z.card * s := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
        have h2 : p.roots.toFinset.card ≤ p.natDegree :=
          le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' p)
        have h3 : p.natDegree < k := natDegree_lt_of_mem_degreeLT hp_mem
        rw [h1] at hZcard
        have : Z.card * s ≤ p.natDegree := le_trans hZcard h2
        calc s * Z.card = Z.card * s := Nat.mul_comm _ _
          _ ≤ p.natDegree := this
          _ < k := h3
      -- Hence `|Z| ≤ (k-1)/s`.
      have hZ_le : Z.card ≤ (k - 1) / s := by
        rw [Nat.le_div_iff_mul_le hs]
        have : s * Z.card ≤ k - 1 := by omega
        calc Z.card * s = s * Z.card := Nat.mul_comm _ _
          _ ≤ k - 1 := this
      -- Weight `= |ι| - |Z| ≥ D`.
      have hwt_eq : Code.wt c + Z.card = Fintype.card ι := by
        have hZeq : Z = Finset.filter (fun x => ¬ (c x ≠ 0)) Finset.univ := by
          rw [hZ]; simp only [not_not]
        rw [Code.wt, hZeq, Finset.card_filter_add_card_filter_not, Finset.card_univ]
      rw [← hwt]
      omega

/-- **The [ABF26] Definition 2.5 rate of `FRS[F, L, k, s, ω]` is `k / (s · n)`** in the
non-saturated regime `k ≤ s · |ι|`. The alphabet is `F^s`, so the dimension `k`
(`dim_frsCode`) is normalized by `s · n`, not by `n`. -/
lemma alphabetRate_frsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0)
    (hk : k ≤ s * Fintype.card ι) :
    (LinearCode.alphabetRate (frsCode domain k s ω) : ℝ)
      = (k : ℝ) / (s * Fintype.card ι) := by
  rw [LinearCode.alphabetRate_cast_eq, dim_frsCode domain k s ω hadm hω hk]

/-- **Folded Reed–Solomon is MDS in the sense of [ABF26] Lemma 2.6 exactly when `s ∣ k`.**
At the alphabet-normalized rate `ρ = LinearCode.alphabetRate = k / (s · n)` of Definition 2.5,

  `δ_min(FRS[F, L, k, s, ω]) = 1 - ρ + 1/n`  whenever `s ∣ k`.

`minDist_frsCode`'s docstring states the *biconditional* — the folded code meets the real
Singleton bound "exactly when `s ∣ k`". This theorem formalizes the **sufficient** direction
only. The necessary direction is not vacuous hand-waving either: it is witnessed by a
counterexample checked by machine at `F = ZMod 11`, `L = {1,2,3,4,5}`, `ω = -1`, `s = 2`,
`k = 3`, where `δ_min = 4/5` while `1 - ρ + 1/n = 9/10`. So `s ∣ k` here is load-bearing, not
a convenience hypothesis. The mechanism is the asymmetry recorded in `minDist_frsCode`: the
dimension is `k` on the nose (`dim_frsCode`) while the distance rounds,
`n - ⌊(k-1)/s⌋ = n - ⌈k/s⌉ + 1`. The two agree iff `⌈k/s⌉ = k/s`. Contrast
`ReedSolomon.Interleaved.irs_rate_distance`, which needs no divisibility because interleaving
truncates the dimension and the distance by the same `⌊k/s⌋`.

Supplies the rate-distance hypothesis of the alphabet-generic
`CodingTheory.mds_johnson_lambda_le_of_rate_distance`; `LinearCode.IsMDS` is unavailable
here, being stated only for codes in `ι → F`. -/
theorem frs_rate_distance_of_dvd {ι : Type*} [Fintype ι] [Nonempty ι] {F : Type*} [Field F]
    [DecidableEq F] {k s : ℕ} [NeZero k] (hs : 0 < s) (hdvd : s ∣ k)
    (domain : ι ↪ F) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0)
    (hk : k ≤ s * Fintype.card ι) :
    (Code.minDist ((frsCode domain k s ω : Submodule F (ι → Fin s → F)) :
        Set (ι → Fin s → F)) : ℝ) / Fintype.card ι
      = 1 - (LinearCode.alphabetRate (frsCode domain k s ω) : ℝ) + 1 / Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  obtain ⟨m, rfl⟩ := hdvd
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd (by simp) (NeZero.ne (s * 0))
    · exact h
  have hmle : m ≤ Fintype.card ι := Nat.le_of_mul_le_mul_left hk hs
  -- With `s ∣ k` the distance's floor is exact: `⌊(s·m - 1)/s⌋ = m - 1`.
  have hsm : s ≤ s * m := Nat.le_mul_of_pos_right s hm
  have hlo : (m - 1) * s = s * m - s := by rw [Nat.sub_mul, one_mul, Nat.mul_comm]
  have hhi : (m - 1 + 1) * s = s * m := by rw [Nat.sub_add_cancel hm, Nat.mul_comm]
  have hfloor : (s * m - 1) / s = m - 1 :=
    Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [minDist_frsCode hs domain ω hadm hω hk, hfloor,
    alphabetRate_frsCode domain (s * m) s ω hadm hω hk,
    Nat.cast_sub (by omega : m - 1 ≤ Fintype.card ι), Nat.cast_mul, Nat.cast_sub hm,
    Nat.cast_one]
  field_simp
  ring

/-- Mirror of `mem_frsCode_iff` with the equation oriented `encoder = f` rather than
`f = encoder` — useful for `rw` / `simp` from the encoder side. -/
lemma mem_frsCode_iff_flipped {ι : Type*} {F : Type*} [CommSemiring F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) (f : ι → Fin s → F) :
    f ∈ frsCode domain k s ω ↔
      ∃ p ∈ Polynomial.degreeLT F k,
        ∀ x : ι, ∀ j : Fin s, p.eval (domain x * ω ^ (j : ℕ)) = f x j := by
  rw [mem_frsCode_iff]
  refine exists_congr fun p ↦ and_congr_right fun _ ↦ ?_
  exact ⟨fun h x j ↦ (h x j).symm, fun h x j ↦ (h x j).symm⟩

/-- **Sanity check: `FRS[F, L, k, 1, ω] ≃ RS[F, L, k]`.** With `s = 1` there is exactly
one fold and `Fin 1 → F ≃ F`, so the folded RS code collapses to the standard
Reed-Solomon code. Stated as an iff between memberships to avoid the cross-type
equality issue (the LHS lives in `ι → Fin 1 → F`, the RHS in `ι → F`).

A one-line corollary of the encoder-generic `ReedSolomon.mem_map_degreeLT_one_iff_mem_code`,
which it shares with `ReedSolomon.Multiplicity.mem_umCode_one_iff_mem_rsCode`. -/
lemma mem_frsCode_one_iff_mem_rsCode {ι : Type*} {F : Type*} [CommSemiring F]
    (domain : ι ↪ F) (k : ℕ) (ω : F) (f : ι → Fin 1 → F) :
    f ∈ frsCode domain k 1 ω ↔
      (fun i ↦ f i 0) ∈ ReedSolomon.code domain k :=
  ReedSolomon.mem_map_degreeLT_one_iff_mem_code domain k (frsEvalOnPoints domain 1 ω)
    (fun p x => by simp [frsEvalOnPoints]) f

/-- **Submodule-level form of the `s = 1` collapse.** Under the natural F-linear
isomorphism `flat : (ι → Fin 1 → F) ≃ₗ[F] (ι → F)` (componentwise via
`LinearEquiv.funUnique`), the image of `frsCode domain k 1 ω` is exactly
`ReedSolomon.code domain k`. This is the structural form of `mem_frsCode_one_iff_mem_rsCode`:
the two codes correspond under the canonical "drop the trivial fold" isomorphism. -/
lemma frsCode_one_map_eq_rsCode {ι : Type*} {F : Type*} [CommSemiring F]
    (domain : ι ↪ F) (k : ℕ) (ω : F) :
    (frsCode domain k 1 ω).map
        (LinearEquiv.piCongrRight (fun _ : ι ↦ LinearEquiv.funUnique (Fin 1) F F) :
            (ι → Fin 1 → F) ≃ₗ[F] (ι → F)).toLinearMap =
      ReedSolomon.code domain k := by
  ext g
  simp only [Submodule.mem_map, LinearEquiv.coe_toLinearMap]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [mem_frsCode_one_iff_mem_rsCode] at hf
    convert hf using 1
    rfl
  · intro hg
    refine ⟨fun i _ ↦ g i, ?_, ?_⟩
    · rw [mem_frsCode_one_iff_mem_rsCode]
      convert hg using 1
    · ext i
      simp [LinearEquiv.piCongrRight, LinearEquiv.funUnique]

end Folded
end ReedSolomon
