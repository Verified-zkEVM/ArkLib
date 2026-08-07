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

- `ReedSolomon.Folded.Admissible` — ABF26 Definition 2.14.
- `ReedSolomon.Folded.frsEvalOnPoints` — F-linear FRS evaluation map.
- `ReedSolomon.Folded.frsCode` — ABF26 Definition 2.15 [GR08].

## Main lemmas

- `ReedSolomon.Folded.mem_frsCode_iff` / `mem_frsCode_iff_flipped` — paper-style
  membership characterisation.
- `ReedSolomon.Folded.dim_frsCode` — `Module.finrank F (frsCode …) = k` under FRS
  encoder injectivity.
- `ReedSolomon.Folded.mem_frsCode_one_iff_mem_rsCode` /
  `frsCode_one_map_eq_rsCode` — sanity checks for `s = 1` collapse to plain RS.

## Not the FRI fold

This is GR08 **alphabet-enlarging** folding: each symbol of a codeword packs the `s` values
`(f̂(x), f̂(xω), …, f̂(xω^{s-1}))`, the degree bound is unchanged, and the code lives in
`ι → Fin s → F`. It is a *different construction* from the FRI/STIR-style **split-and-fold**
elsewhere in the tree, where a random challenge contracts `f(X) = ∑ᵢ Xⁱ fᵢ(X^{2ᵏ})` and the
evaluation domain shrinks — see `ProximityGap/Folding.lean` (`foldWord`),
`Data/Polynomial/SplitFold.lean` (`splitNth`), and `Data/Polynomial/FoldingPolynomial.lean`
(`polyFold`); the "folded RS code" appearing there is a plain RS code on the squared subdomain,
not an FRS code in this file's sense.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §2.4 Definitions 2.14, 2.15.
- [GR08] Guruswami-Rudra. (Original FRS paper.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ReedSolomon
namespace Folded

/-- **ABF26 Definition 2.14 (strengthened).** An element `ω : F` is `(L, s)`-admissible
if **every evaluation point appears only once across all folds**, i.e. the map
`(α, i) ↦ α · ω^i : L × Fin s → F` is injective.

Split into two conjuncts to keep the predicate `simp`-friendly:

  - **inter-orbit:** for distinct `α ≠ β ∈ L`, `α · ω^i ≠ β` for every `i < s`.
  - **intra-orbit:** for every `α ∈ L`, `α · ω^i ≠ α` for every `0 < i < s` —
    equivalently, `ω` has multiplicative order at least `s` on the non-zero
    orbit of `α`.

**Deviation from the paper's literal text.** Definition 2.14 of ABF26 states only the
*inter-orbit* clause (it quantifies over unordered pairs `{α, β} ∈ (L choose 2)`, hence
distinct `α ≠ β`). Its literal reading therefore does *not* forbid `ω^j = 1` for some
`0 < j < s`, which would collapse a fold's `s`-tuple to a repeated-entry vector and
silently weaken the FRS distance argument downstream (T2.18, T4.14). We add the
*intra-orbit* conjunct so that `Admissible` is exactly the GR08 injectivity condition
the paper's results actually rely on. This is a deliberate strengthening, not a verbatim
transcription.

**Boundary cases to be aware of.** The predicate does not require `ω ≠ 0` (downstream
lemmas take it as a separate hypothesis), and it excludes `0 ∈ L` only *implicitly* and
only for `s ≥ 2` (the intra-orbit clause fails at `α = 0`); for `s ≤ 1` the intra-orbit
range is empty and `0 ∈ L` is admissible, so consumers needing `0 ∉ L` must state it. -/
def Admissible {F : Type} [Field F] [DecidableEq F]
    (L : Finset F) (s : ℕ) (ω : F) : Prop :=
  (∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β) ∧
  (∀ α ∈ L, ∀ i : ℕ, 0 < i → i < s → α * ω ^ i ≠ α)

/-- The FRS evaluation map as an `F`-linear map from polynomials to `ι → Fin s → F`,
mirroring `ReedSolomon.evalOnPoints` (which is the `s = 1` special case). -/
def frsEvalOnPoints {ι : Type} [Fintype ι]
    {F : Type} [CommSemiring F]
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
consume it as a `ModuleCode ι F (Fin s → F)` without an existential wrap. -/
noncomputable def frsCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) : Submodule F (ι → Fin s → F) :=
  (Polynomial.degreeLT F k).map (frsEvalOnPoints domain s ω)

/-- **Membership of `frsCode` in paper-style form.** A vector `f : ι → Fin s → F` is
in `frsCode domain k s ω` iff there is a polynomial of degree `< k` whose folded
evaluations match `f`. This is the original paper-shaped membership predicate, kept
as a `simp`-able iff lemma. -/
lemma mem_frsCode_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
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
lemma admissible_foldedPoints_injective {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F] {s : ℕ}
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
          (hintra (domain a) (Finset.mem_map_of_mem _ (Finset.mem_univ _)) (n - m) hpos
            (by omega))
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

/-- **Injectivity of folded RS evaluation on low-degree polynomials** (the folded
analogue of the kernel-triviality argument behind `ReedSolomon.dim_eq_deg_of_le`). When `ω` is
`(L, s)`-admissible (`L = image domain`), `ω ≠ 0`, and there are at least `k` folded
evaluation points (`k ≤ s · |ι|`), the FRS evaluation map restricted to `degreeLT F k`
is injective: a nonzero polynomial of degree `< k ≤ s · |ι|` cannot vanish at all
`s · |ι|` distinct folded points (`admissible_foldedPoints_injective`). This is the
kernel-triviality fact underlying the FRS dimension formula `dim_frsCode` below. -/
lemma frsEvalOnPoints_domRestrict_injective {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F] {k s : ℕ} [NeZero k]
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

/-- **Dimension of `frsCode`.** Under `(L, s)`-admissibility of `ω` (`L = image domain`),
`ω ≠ 0`, and enough folded evaluation points (`k ≤ s · |ι|`), the FRS encoder is injective
on `degreeLT F k` (`frsEvalOnPoints_domRestrict_injective`), so the folded code has
dimension exactly `k`. This is the rate fact `ρ = k / (s · n)` for FRS codes, the folded
analogue of `ReedSolomon.dim_eq_deg_of_le`. -/
lemma dim_frsCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) [NeZero k]
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0)
    (hk : k ≤ s * Fintype.card ι) :
    Module.finrank F (frsCode domain k s ω) = k := by
  have h_range : (Polynomial.degreeLT F k).map (frsEvalOnPoints domain s ω) =
      LinearMap.range ((frsEvalOnPoints domain s ω).domRestrict
        (Polynomial.degreeLT F k)) := by
    ext
    simp [Submodule.mem_map]
  rw [frsCode, h_range,
    LinearMap.finrank_range_of_inj
      (frsEvalOnPoints_domRestrict_injective domain ω hadm hω hk),
    Polynomial.finrank_degreeLT_n]

/-- **Folded-RS minimum (block) distance** — the folded analogue of
`ReedSolomon.minDist_of_le`. Under `(L, s)`-admissibility of `ω` (`L = image domain`),
`ω ≠ 0`, `0 < s`, and `k ≤ s · |ι|`, the folded code is MDS in the block (per-fold)
Hamming metric: a nonzero codeword has at most `⌊(k-1)/s⌋` zero folded symbols, so

  `Code.minDist (frsCode domain k s ω) = |ι| − ⌊(k-1)/s⌋`.

**Lower bound** (`≥`, mirrors `ReedSolomon.minDist_of_le`'s weight argument): a nonzero
codeword comes from `p ≠ 0` of degree `< k`; each zero fold packs `s` distinct roots of `p`
(distinct across folds too, by `admissible_foldedPoints_injective`), so `s · (#zero folds) ≤
deg p < k`, giving `#zero folds ≤ ⌊(k-1)/s⌋` and weight `≥ |ι| − ⌊(k-1)/s⌋`.

**Upper bound** (`≤`): the codeword of the degree-`s·⌊(k-1)/s⌋ < k` polynomial
`p = ∏_{x ∈ T, j} (X − domain x · ω^j)` for any `T ⊆ ι` with `|T| = ⌊(k-1)/s⌋` vanishes on
exactly the `T`-folds (the `s·|T|` chosen points are roots; no others are, by full
point-distinctness), so it has weight exactly `|ι| − ⌊(k-1)/s⌋`. -/
theorem minDist_frsCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F] {k s : ℕ} [NeZero k] (hs : 0 < s)
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

/-- Mirror of `mem_frsCode_iff` with the equation oriented `encoder = f` rather than
`f = encoder` — useful for `rw` / `simp` from the encoder side. -/
lemma mem_frsCode_iff_flipped {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
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
equality issue (the LHS lives in `ι → Fin 1 → F`, the RHS in `ι → F`). -/
lemma mem_frsCode_one_iff_mem_rsCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
    (domain : ι ↪ F) (k : ℕ) (ω : F) (f : ι → Fin 1 → F) :
    f ∈ frsCode domain k 1 ω ↔
      (fun i ↦ f i 0) ∈ ReedSolomon.code domain k := by
  simp only [mem_frsCode_iff, ReedSolomon.code, Submodule.mem_map, ReedSolomon.evalOnPoints]
  constructor
  · rintro ⟨p, hp, hf⟩
    refine ⟨p, hp, ?_⟩
    ext i
    simpa using (hf i 0).symm
  · rintro ⟨p, hp, hp_eval⟩
    refine ⟨p, hp, ?_⟩
    intro i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have := congrFun hp_eval i
    simpa using this.symm

/-- **Submodule-level form of the `s = 1` collapse.** Under the natural F-linear
isomorphism `flat : (ι → Fin 1 → F) ≃ₗ[F] (ι → F)` (componentwise via
`LinearEquiv.funUnique`), the image of `frsCode domain k 1 ω` is exactly
`ReedSolomon.code domain k`. This is the structural form of `mem_frsCode_one_iff_mem_rsCode`:
the two codes correspond under the canonical "drop the trivial fold" isomorphism. -/
lemma frsCode_one_map_eq_rsCode {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [DecidableEq F]
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
