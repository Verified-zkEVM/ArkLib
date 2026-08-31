/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Folded Reed-Solomon codes

The *folded* Reed-Solomon code `frsCode domain k s ω` packs `s` consecutive evaluations
`(p x, p (x * ω), …, p (x * ω ^ (s-1)))` of a single polynomial of degree `< k` into one
symbol of the enlarged alphabet `Fin s → F`, at each point `x` of the evaluation domain.

## Main definitions

* `ReedSolomon.Folded.Admissible` — the condition on `ω` that every evaluation point occurs
  in exactly one fold, i.e. that `(α, i) ↦ α * ω ^ i` is injective on `L × Fin s`.
* `ReedSolomon.Folded.frsEvalOnPoints` — the `F`-linear folded evaluation map.
* `ReedSolomon.Folded.frsCode` — the folded Reed-Solomon code, an `F`-submodule of
  `ι → Fin s → F`. At `s = 1` it collapses to `ReedSolomon.code`
  (`mem_frsCode_one_iff_mem_rsCode`, `frsCode_one_map_eq_rsCode`).
* `ReedSolomon.Folded.foldedDomain` — the `s * |ι|` folded evaluation points as an
  embedding `ι × Fin s ↪ F`.

## Main statements

* `ReedSolomon.Folded.admissible_foldedPoints_injective` — admissibility, together with
  `ω ≠ 0`, is exactly injectivity of the folded point map.
* `ReedSolomon.Folded.frsCode_eq_map_rsCode` — a folded Reed-Solomon code is a plain
  Reed-Solomon code on the folded domain, transported along the currying equivalence
  `(ι × Fin s → F) ≃ₗ[F] (ι → Fin s → F)`.
* `ReedSolomon.Folded.dim_frsCode_eq_min`, `ReedSolomon.Folded.dim_frsCode` — the dimension
  is `min k (s * |ι|)`, hence `k` in the non-saturated regime.
* `ReedSolomon.Folded.minDist_frsCode` — the minimum block distance is `|ι| - ⌊(k-1)/s⌋`.
* `ReedSolomon.Folded.alphabetRate_frsCode`,
  `ReedSolomon.Folded.frs_rate_distance_of_dvd` — the alphabet-normalized rate is
  `k / (s * |ι|)`, and the code satisfies the MDS rate-distance equation when `s ∣ k`.

## Relation to other notions of folding

This is *alphabet-enlarging* folding: the degree bound is unchanged and the code lives in
`ι → Fin s → F`. It differs from the split-and-fold operation of FRI and STIR — see
`ArkLib/Data/CodingTheory/ProximityGap/Folding.lean` and
`ArkLib/Data/Polynomial/SplitFold.lean` — where a random challenge contracts
`p X = ∑ i, X ^ i * pᵢ (X ^ 2 ^ k)` and the evaluation domain shrinks, so that the resulting
"folded code" is a plain Reed-Solomon code on a subdomain.

Likewise, the block metric of `minDist_frsCode` is `Code.minDist` over the enlarged alphabet
`Fin s → F`, with the blocks carried in the codeword's type. It is not
`CodingTheory.BlockRelDistance` (`Basic/BlockRelDistance.lean`), whose words stay flat and
whose blocks are cosets of a `SmoothCosetFftDomain`. The two express the same idea — a block
metric on a partition of the evaluation domain — but neither development's lemmas apply to
the other as stated.

## References

* [Guruswami, V., and Rudra, A., *Explicit Codes Achieving List Decoding Capacity:
    Error-Correction With Optimal Redundancy*][GR08]
* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
-/
namespace ReedSolomon

namespace Folded

/-- An element `ω : F` is `(L, s)`-**admissible** when every evaluation point appears in
only one fold, i.e. when `(α, i) ↦ α * ω ^ i` is injective on `L × Fin s` (see
`admissible_foldedPoints_injective`).

The predicate is split into two conjuncts:

* *inter-orbit*: for distinct `α, β ∈ L`, `α * ω ^ i ≠ β` for every `i < s`;
* *intra-orbit*: for every `α ∈ L`, `α * ω ^ i ≠ α` for every `i` with `0 < i < s`.

Both lead with the bounded quantifier `∀ i, i < s → …` so that `Nat.decidableBallLT` fires
and concrete admissibility claims are closed by `decide`. The inter-orbit conjunct
quantifies over ordered distinct pairs, asserting both `α * ω ^ i ≠ β` and `β * ω ^ i ≠ α`;
this is what `admissible_foldedPoints_injective` consumes after normalising a collision by
`rcases le_total`.

The intra-orbit conjunct is not redundant. Without it `ω ^ j = 1` for some `0 < j < s` is
permitted, collapsing each fold to a repeated-entry vector; at `ω = 1` over `ZMod 11` with
`L` the order-5 subgroup, `s = 2` and `k = 2`, the true minimum block distance is `4` while
`minDist_frsCode` would give `5`.

Note that `Admissible` does not require `ω ≠ 0`, which downstream lemmas take separately,
and that it excludes `0 ∈ L` only for `s ≥ 2`, via the intra-orbit clause at `i = 1`; for
`s ≤ 1` that clause is vacuous, so a consumer needing `0 ∉ L` there must state it. -/
def Admissible {F : Type*} [Field F]
    (L : Finset F) (s : ℕ) (ω : F) : Prop :=
  (∀ α ∈ L, ∀ β ∈ L, α ≠ β → ∀ i : ℕ, i < s → α * ω ^ i ≠ β) ∧
  (∀ α ∈ L, ∀ i : ℕ, i < s → 0 < i → α * ω ^ i ≠ α)

/-- `Admissible` is decidable: both conjuncts are bounded quantifiers over a `Finset` and
over `i < s`. -/
instance decidableAdmissible {F : Type*} [Field F] [DecidableEq F]
    (L : Finset F) (s : ℕ) (ω : F) : Decidable (Admissible L s ω) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Admissibility restricts along `L' ⊆ L`. This is what lets the statements below
hypothesise admissibility at the canonical point set `Finset.univ.map domain` while
remaining usable by a caller holding it on a larger ambient set. -/
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

/-- The folded Reed-Solomon code: the words `f : ι → Fin s → F` for which some polynomial
`p` of degree `< k` satisfies `f x j = p.eval (domain x * ω ^ j)` at every point and fold.

Defined as the image of `Polynomial.degreeLT F k` under `frsEvalOnPoints`, mirroring
`ReedSolomon.code`, so it is a `Submodule F (ι → Fin s → F)` by construction. Admissibility
of `ω` is deliberately not baked in; it appears as a side condition on the dimension and
distance statements. At `s = 1` the code is `ReedSolomon.code domain k` for every `ω`. -/
noncomputable def frsCode {ι : Type*} {F : Type*} [CommSemiring F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F) : Submodule F (ι → Fin s → F) :=
  (Polynomial.degreeLT F k).map (frsEvalOnPoints domain s ω)

/-- A word lies in `frsCode domain k s ω` iff some polynomial of degree `< k` has the word
as its folded evaluations. -/
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

/-- The `s * |ι|` folded evaluation points are pairwise distinct: for admissible `ω ≠ 0`,
the map `(x, j) ↦ domain x * ω ^ j` is injective.

The two conjuncts of `Admissible`, together with cancellation by the unit `ω ^ m`, rule out
the two ways a collision could occur: across distinct base points, or within one orbit. -/
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

/-- The `s * |ι|` folded evaluation points as an embedding `ι × Fin s ↪ F`, with
injectivity supplied by `admissible_foldedPoints_injective`. This is the evaluation domain
over which `frsCode` is a plain Reed-Solomon code (`frsCode_eq_map_rsCode`). -/
def foldedDomain {ι : Type*} [Fintype ι] {F : Type*} [Field F] {s : ℕ}
    (domain : ι ↪ F) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0) : ι × Fin s ↪ F :=
  ⟨fun xi => domain xi.1 * ω ^ (xi.2 : ℕ), admissible_foldedPoints_injective domain ω hadm hω⟩

@[simp]
lemma foldedDomain_apply {ι : Type*} [Fintype ι] {F : Type*} [Field F] {s : ℕ}
    (domain : ι ↪ F) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0) (xi : ι × Fin s) :
    foldedDomain domain ω hadm hω xi = domain xi.1 * ω ^ (xi.2 : ℕ) := rfl

/-- A folded Reed-Solomon code is a plain Reed-Solomon code on the folded domain: it is the
image of `ReedSolomon.code (foldedDomain …) k` under the currying equivalence
`(ι × Fin s → F) ≃ₗ[F] (ι → Fin s → F)`. Admissibility of `ω` is what makes the `s * |ι|`
folded points a legitimate Reed-Solomon evaluation domain.

The dimension formulas transport along this equality. The minimum distance does not:
`minDist_frsCode` is stated in the block metric on `ι → Fin s → F`, whereas
`ReedSolomon.minDist_of_le` is the symbol metric on `ι × Fin s → F`, and currying is not an
isometry between the two. -/
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

/-- The folded evaluation map is injective on `Polynomial.degreeLT F k` when `ω` is
admissible, `ω ≠ 0` and `k ≤ s * |ι|`: a nonzero polynomial of degree `< k` cannot vanish at
all `s * |ι|` distinct folded points.

No `[NeZero k]` is needed: at `k = 0` the domain is the zero submodule. -/
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
    · have : NeZero k := ⟨by omega⟩
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

/-- For admissible `ω ≠ 0` the folded code has dimension `min k (s * |ι|)`: the message
dimension grows with `k` until the `s * |ι|` evaluation points are saturated.

Transported from `ReedSolomon.dim_eq_min_deg_card` along `frsCode_eq_map_rsCode`, currying
being an `F`-linear isomorphism. -/
lemma dim_frsCode_eq_min {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0) :
    Module.finrank F (frsCode domain k s ω) = min k (s * Fintype.card ι) := by
  rw [frsCode_eq_map_rsCode domain k ω hadm hω]
  rw [← (Submodule.equivMapOfInjective (LinearEquiv.curry F F ι (Fin s)).toLinearMap
    (LinearEquiv.curry F F ι (Fin s)).injective _).finrank_eq]
  simpa [LinearCode.dim, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using
    (ReedSolomon.dim_eq_min_deg_card (n := k) (α := foldedDomain domain ω hadm hω))

/-- Below saturation, `k ≤ s * |ι|`, the folded code has dimension exactly `k`. -/
lemma dim_frsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0)
    (hk : k ≤ s * Fintype.card ι) :
    Module.finrank F (frsCode domain k s ω) = k := by
  rw [dim_frsCode_eq_min domain k s ω hadm hω, min_eq_left hk]

/-- The minimum block distance of a folded Reed-Solomon code, for admissible `ω ≠ 0`,
`0 < s` and `k ≤ s * |ι|`:

  `Code.minDist (frsCode domain k s ω) = |ι| - ⌊(k-1)/s⌋` .

For `k ≥ 1` the right-hand side is `n - ⌈k/s⌉ + 1` with `n = |ι|`, so the code meets the
integer Singleton bound with equality. It meets the real Singleton bound — equivalently,
satisfies the MDS rate-distance equation at the rate `k / (s * n)` — exactly when `s ∣ k`;
otherwise it falls short by the rounding term `⌈k/s⌉ - k/s`. See
`frs_rate_distance_of_dvd`.

For `≥`: a nonzero codeword comes from some `p ≠ 0` of degree `< k`, and each vanishing
fold contributes `s` roots of `p`, distinct across folds, so `s * #(vanishing folds) < k`.
For `≤`: for any `T ⊆ ι` of size `⌊(k-1)/s⌋`, the polynomial
`∏ x ∈ T, ∏ j, (X - C (domain x * ω ^ j))` has degree `s * ⌊(k-1)/s⌋ < k` and vanishes on
exactly the folds indexed by `T`. -/
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
  have : Nonempty ι := Fintype.card_pos_iff.mp (lt_of_le_of_lt (Nat.zero_le _) hdiv_lt)
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

/-- Below saturation, the alphabet-normalized rate of a folded Reed-Solomon code is
`k / (s * |ι|)`: the alphabet is `Fin s → F`, so the dimension `k` is divided by `s * n`
rather than by `n`. -/
lemma alphabetRate_frsCode {ι : Type*} [Fintype ι] {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hadm : Admissible (Finset.univ.map domain) s ω) (hω : ω ≠ 0)
    (hk : k ≤ s * Fintype.card ι) :
    (LinearCode.alphabetRate (frsCode domain k s ω) : ℝ)
      = (k : ℝ) / (s * Fintype.card ι) := by
  rw [LinearCode.alphabetRate_cast_eq, dim_frsCode domain k s ω hadm hω hk]

/-- When `s ∣ k`, a folded Reed-Solomon code satisfies the MDS rate-distance equation at
its alphabet-normalized rate `ρ = k / (s * n)`:

  `δ_min (frsCode domain k s ω) = 1 - ρ + 1/n` .

The divisibility hypothesis is load-bearing rather than a convenience: the dimension is `k`
exactly (`dim_frsCode`) while the distance rounds, `n - ⌊(k-1)/s⌋ = n - ⌈k/s⌉ + 1`, and the
two agree iff `⌈k/s⌉ = k/s`. Over `ZMod 11` with `L = {1,2,3,4,5}`, `ω = -1`, `s = 2` and
`k = 3` the equation fails, `δ_min = 4/5` against `1 - ρ + 1/n = 9/10`. Contrast
`ReedSolomon.Interleaved.irs_rate_distance`, which needs no divisibility because
interleaving truncates dimension and distance by the same `⌊k/s⌋`. -/
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

/-- At `s = 1` the folded code collapses to the plain Reed-Solomon code. Stated as an
equivalence of memberships, the two codes living in the distinct types `ι → Fin 1 → F` and
`ι → F`; see `frsCode_one_map_eq_rsCode` for the transported equality. -/
lemma mem_frsCode_one_iff_mem_rsCode {ι : Type*} {F : Type*} [CommSemiring F]
    (domain : ι ↪ F) (k : ℕ) (ω : F) (f : ι → Fin 1 → F) :
    f ∈ frsCode domain k 1 ω ↔
      (fun i ↦ f i 0) ∈ ReedSolomon.code domain k :=
  ReedSolomon.mem_map_degreeLT_one_iff_mem_code domain k (frsEvalOnPoints domain 1 ω)
    (fun p x => by simp [frsEvalOnPoints]) f

/-- Submodule form of the `s = 1` collapse: the image of `frsCode domain k 1 ω` under the
componentwise isomorphism `(ι → Fin 1 → F) ≃ₗ[F] (ι → F)` is `ReedSolomon.code domain k`. -/
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
