/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import ArkLib.ProofSystem.ToyProblem.Leaderboard
import ArkLib.ProofSystem.ToyProblem.Spec.General
import ArkLib.ProofSystem.ToyProblem.Spec.SimplifiedIOR

/-!
# Toy problem — folded Reed–Solomon instantiation (ABF26 §6.3.2)

The second concrete leaderboard entry for the §6 toy-problem frontier: take the
underlying code to be a **folded** Reed–Solomon code `FRS[F, L, k, s, ω]` with
folding parameter `s > 1`, so a codeword symbol is a length-`s` tuple
`Fin s → F` rather than a scalar `F` (ABF26 Definition 2.15 [GR08]). This is the
`A = Fin s → F` instantiation of the alphabet-generic toy problem (the `A = F`
scalar case is the interleaved-RS entry `koalaIRS` in `Leaderboard.lean`).

Folding is the lever behind the paper's §6.3.2 *subspace-design* analysis: the
`τ`-subspace-design list-decodability of FRS (`τ(r) = s·ρ/(s − r + 1)`) drives
the list-size term, and the construction's **argument-size at enforced 128-bit
security** improves over interleaved RS for large folding. We record **two**
KoalaBear-sextic FRS leaderboard rows from `tab:subspace-design-security-analysis`
/ `tab:subspace-elias-lowerbound-thresholds` (both at `t = 128`):

* the **`s = 2^5 = 32` row** — the paper's primary fully-worked example
  (`securityGap = 98.91` bits); and
* the **`s = 2^12 = 4096` row** — the large-folding, **gap-closing** row
  (`securityGap = 10.62` bits), demonstrating that
  larger folding pushes the τ-subspace-design operating point toward capacity and
  collapses the fixed-`t` δ-swept gap by `≈ 88` bits.

**Where the pieces live.** This file holds the immutable, axiom-clean side of both
rows: the parameter points (`koalaFRS`, `koalaFRS12`), the folded encoders and
distance lemmas, and the **attack/upper** anchors `frsUpperBound` / `frsUpperBound12`
(which owe nothing). The **provable/lower** anchors `frsLowerBound` /
`frsLowerBound12` and the two `securityGap_koalaFRS*` readoffs are *not* here: their
proofs reduce to the owed τ-subspace-design `ε_mca` bound, which is the ABF26 §1
**Grand MCA Challenge** (the explicit prize). They live as the open contest entries
in the external `proximity-prize` repository (which depends on ArkLib), so that
ArkLib carries only finished/winning proofs. The values quoted above are those
entries' gaps.

## The `s = 32` row at `t = 128` (ABF26 §6.3.2)

* Field `F = KoalaSextic` (`|F| = q^6 ≈ 2^186`), rate `ρ = 1/2`, evaluation
  domain `|L| = 2^16`, message size `k = 2^20`, folding `s = 2^5 = 32`
  (so `k = 2^20 ≤ s·|L| = 2^21`).
* **Provable** RBR knowledge soundness (X side, `tab:subspace-design-security-`
  `analysis`, `r = 8`, at `δ = 7/48`): `bestProvableError ≤ 2^(-29.10)` — the
  convex combination of the spot-check term `(τ(r+1) + 3/(2r))^128 = (41/48)^128
  = 2^(-29.1085)` and the list-size term `≈ 2^(-166.8)`. The certified figure
  rounds the magnitude **down** to `29.10` (the convex combination dominates the
  spot-check term, so `2^(-29.1085)` is a strict ceiling; `29.11` would
  *overstate*, as `2^(-29.1085) > 2^(-29.11)`) — the same round-down discipline
  as the interleaved `koalaIRS` anchor (`64 → 63.99`).
* **Attack** (Y side): `bestProvableError ≥ 2^(-128.01)`. This is the **sweep
  floor** `⨅_δ (1-δ)^t + …`, certified from the **spot-check term alone** — the
  convex combination dominates `(1-δ)^t`, whose infimum over the window
  `(0, δ_min)` is `(1-δ_min)^128 ≈ 2^(-128.006)` because the folded code's MDS
  relative distance `δ_min = D/|L| = 32769/65536 ≈ 0.50002` (a degree-`< k`
  polynomial has `< k` roots, hence `< (k-1)/s = 32767` zero folded-symbols).
  No Elias/list-size lower bound is needed for this ceiling. The paper's
  per-`δ*` Elias value (`tab:subspace-elias-lowerbound-thresholds`, `δ* = 0.499`)
  is the *weaker* point reading `2^(-127.63) = (1-0.499)^128`; it is **not** the
  sweep floor (just above `δ*` the spot-check keeps dropping toward `2^(-128)`,
  so `2^(-127.63)` is not a valid floor unless the list-size term is active
  across the whole `(δ*, δ_min)` sliver — the same sub-band subtlety that bumped
  the interleaved ceiling `116.49 → 117`). The ceiling rounds **up** to `128.01`.
* `securityGap = 128.01 − 29.10 = 98.91` bits.

**Reading the gap honestly.** At a *fixed* `t = 128`, `s = 32` folding gives a
*larger* `bestProvableError` gap than the interleaved entry (`koalaIRS`:
`53.01`). This is faithful, not a defect: folding at fixed `t` does not by
itself improve the δ-swept provable frontier (for `s ≤ 2^4` the paper proves
*no* soundness at all at `t = 128`). The FRS advantage lives on a **different
axis** the toy `bestProvableError` (a fixed-`t` δ-sweep) does not capture:

* **larger folding closes the gap** — at `s = 2^12` the provable side reaches
  `2^(-118.13)` (`r = 108`, honest round-down of `2^(-118.1376)`), a `≈ 10`-bit
  gap to the `≈ 2^(-128)` attack; and
* **argument-size at enforced 128-bit security** — the `s = 2^5` row reaches
  full `2^(-128.03)` provable soundness at repetition `t = 563`, `r = 8` with
  argument size `417.9 KiB` (`tab:subspace-design-128bit-security`), the metric
  on which folding genuinely beats interleaving.

Both rows' anchors are **full reductions** (sorry-free integer spot-check leaves
plus the proven L6.10 bridge), matching the `koalaIRS` anchors. **Track B
(2026-06-23) closed the structural side entirely:** the folded MDS distance
`koalaFRS_minRelDist` (`δ_min = 32769/65536`) and encoder injectivity are now proven
`sorry`-free via the new `ReedSolomon/Folded.lean` bridges
(`frsEvalOnPoints_domRestrict_injective`, `minDist_frsCode`) on a genuine
multiplicative-coset domain, resting on the proven order witness `koalaFRSγ_exists`
— so the **attack ceiling owes nothing** (`frsUpperBound` / `frsUpperBound12` here
are fully axiom-clean). The *only* remaining owed external is the provable bound's
τ-subspace-design `ε_mca` term, the FRS counterpart of the `koalaIRS` owed `ε_mca`
— the Grand MCA Challenge, carried by the provable anchors in the external
`proximity-prize` repository.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§6.3.2, Tables for folded Reed–Solomon).
-/

namespace ToyProblem

namespace Impl.FRS

open scoped NNReal ENNReal
open Polynomial ReedSolomon.Folded Code

/-- **A high-order field element (proven, `sorry`-free).** There exists `γ : KoalaSextic`
with `γ ≠ 0` and multiplicative order at least `2^21`. KoalaBear's prime
`q = 2^31 - 2^24 + 1` has `2^24 | q - 1`, so the multiplicative group of
`KoalaSextic = 𝔽_{q^6}` (cyclic of order `q^6 - 1`, divisible by `q - 1`) contains an
element of order exactly `2^21`. The proof is pure finite-group theory plus `ℕ`
arithmetic: a generator of `KoalaSexticˣ` has order `q^6 - 1`, and the power
`g ^ ((q^6 - 1) / 2^21)` has order `2^21` (`orderOf_pow'` + `Nat.div_div_self`); its unit
coercion is the witness. No computation in the noncomputable field is needed.

**This single fact is the structural keystone behind both genuine multiplicative-coset FRS
rows.** From it, domain injectivity, `(L, s)`-admissibility (`koalaFRSDomain_admissible` /
`koalaFRS12Domain_admissible`), encoder injectivity (`koalaFRSEnc_injective` /
`koalaFRS12Enc_injective`), and the folded minimum distance (`koalaFRS_minRelDist` /
`koalaFRS12_minRelDist`) all derive `sorry`-free. Both `s = 32` and `s = 2^12` use the
*same* `γ` (each needs only order `≥ s · |L| = 2^21`). -/
theorem koalaFRSγ_exists : ∃ γ : KoalaSextic, γ ≠ 0 ∧ 2 ^ 21 ≤ orderOf γ := by
  -- Abstract group theory: the multiplicative group `KoalaSexticˣ` of the finite field
  -- `𝔽_{q^6}` is cyclic of order `q^6 - 1`. Since `q - 1 = 2^24 · 127` and
  -- `(q - 1) ∣ (q^6 - 1)`, we have `2^21 ∣ q^6 - 1`, so a generator's appropriate power
  -- has order exactly `2^21`; its unit coercion is the desired nonzero element.
  classical
  haveI : Fintype KoalaSextic := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := KoalaSexticˣ)
  set n : ℕ := orderOf g with hn_def
  have hcardK : Fintype.card KoalaSextic = KoalaBear.fieldSize ^ 6 := by
    rw [← Nat.card_eq_fintype_card]; exact koalaSextic_card
  -- A generator's order is the cardinality of the unit group, `q^6 - 1`.
  have hg_ord : n = KoalaBear.fieldSize ^ 6 - 1 := by
    have h1 : orderOf g = Nat.card KoalaSexticˣ :=
      orderOf_eq_card_of_forall_mem_zpowers hg
    rw [hn_def, h1, Nat.card_eq_fintype_card, Fintype.card_units, hcardK]
  -- `2^21 ∣ q - 1` (concretely `q - 1 = 2^21 · 1016`) and `(q - 1) ∣ (q^6 - 1)`.
  have hdvd_q : (2 ^ 21 : ℕ) ∣ KoalaBear.fieldSize - 1 := by
    norm_num [KoalaBear.fieldSize]
  have hdvd_pow : (KoalaBear.fieldSize - 1) ∣ (KoalaBear.fieldSize ^ 6 - 1) := by
    simpa using Nat.sub_one_dvd_pow_sub_one KoalaBear.fieldSize 6
  have hdvd : (2 ^ 21 : ℕ) ∣ n := by rw [hg_ord]; exact hdvd_q.trans hdvd_pow
  have hn_pos : n ≠ 0 := by rw [hg_ord]; norm_num [KoalaBear.fieldSize]
  -- `u := g ^ (n / 2^21)` has order `n / gcd(n, n/2^21) = n / (n/2^21) = 2^21`.
  refine ⟨(g ^ (n / 2 ^ 21) : KoalaSexticˣ), Units.ne_zero _, ?_⟩
  rw [orderOf_units]
  have hm_ne : n / 2 ^ 21 ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn_pos) hdvd) (by norm_num)
    omega
  rw [orderOf_pow' g hm_ne, ← hn_def, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdvd),
    Nat.div_div_self hdvd hn_pos]

/-- The shared high-order generator `γ` of `koalaFRSγ_exists`. -/
noncomputable def koalaFRSγ : KoalaSextic := koalaFRSγ_exists.choose

lemma koalaFRSγ_ne_zero : koalaFRSγ ≠ 0 := koalaFRSγ_exists.choose_spec.1

lemma koalaFRSγ_order : 2 ^ 21 ≤ orderOf koalaFRSγ := koalaFRSγ_exists.choose_spec.2

/-- Powers of `γ` below `2^21 ≤ orderOf γ` are pinned by their exponent: this is the
`pow`-injectivity on `Set.Iio (orderOf γ)` that turns every distinctness side condition of
the coset construction into a `ℕ`-arithmetic fact (dischargeable by `omega`). -/
lemma koalaFRSγ_pow_left_inj {a b : ℕ} (ha : a < 2 ^ 21) (hb : b < 2 ^ 21)
    (h : koalaFRSγ ^ a = koalaFRSγ ^ b) : a = b :=
  pow_injOn_Iio_orderOf
    (Set.mem_Iio.mpr (lt_of_lt_of_le ha koalaFRSγ_order))
    (Set.mem_Iio.mpr (lt_of_lt_of_le hb koalaFRSγ_order)) h

/-- The folding multiplier `ω := γ` for the `s = 32` folded RS code — the shared
high-order generator (`koalaFRSγ`). With the multiplicative-coset domain
`koalaFRSDomain j = γ^(32·j)`, the folded points are `γ^(32·j) · γ^i = γ^(32·j + i)`
over `32·j + i < 2^21 ≤ orderOf γ`, so `(L, 32)`-admissibility holds genuinely
(`koalaFRSDomain_admissible`) rather than being a documentary placeholder. -/
noncomputable def koalaFoldω : KoalaSextic := koalaFRSγ

/-- The `2^16`-point folded-RS evaluation domain as a genuine **multiplicative coset**
(here the cyclic subgroup `⟨γ^32⟩`): `j ↦ γ^(32·j) ⊆ KoalaSextic`, the [ABF26] §6.3
"common case" smooth-coset domain. Injectivity is `pow`-injectivity of `γ` below its
order: `32·j < 32·2^16 = 2^21 ≤ orderOf γ` (`koalaFRSγ_pow_left_inj`), replacing the
earlier additive `{1,…,2^16}` placeholder. The coset is zero-free (`γ ≠ 0`, so every
power is a unit), so the admissibility intra-orbit clause `α · ω^i ≠ α` is not
vacuously false at `0`; here it holds outright via the order bound. -/
noncomputable def koalaFRSDomain : Fin (2 ^ 16) ↪ KoalaSextic where
  toFun j := koalaFRSγ ^ (32 * j.val)
  inj' i j hij := by
    have hi : 32 * (i : ℕ) < 2 ^ 21 := by have := i.isLt; omega
    have hj : 32 * (j : ℕ) < 2 ^ 21 := by have := j.isLt; omega
    exact Fin.val_injective (by have := koalaFRSγ_pow_left_inj hi hj hij; omega)

open Classical in
/-- **`(L, 32)`-admissibility of the coset domain.** The `32 · 2^16 = 2^21` folded points
`γ^(32·a) · γ^i = γ^(32·a + i)` are pairwise distinct because all exponents lie below
`2^21 ≤ orderOf γ`: both `Admissible` conjuncts reduce, via `koalaFRSγ_pow_left_inj`, to
`ℕ`-arithmetic facts about `32·a + i` (`omega`). Derives `sorry`-free from the (now-proven)
order bound `koalaFRSγ_order`. -/
lemma koalaFRSDomain_admissible :
    ReedSolomon.Folded.Admissible (Finset.univ.map koalaFRSDomain) 32 koalaFoldω := by
  refine ⟨?_, ?_⟩
  · intro α hα β hβ hαβ i hi hcontra
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hα hβ
    obtain ⟨a, rfl⟩ := hα
    obtain ⟨b, rfl⟩ := hβ
    simp only [koalaFRSDomain, koalaFoldω, Function.Embedding.coeFn_mk, ← pow_add] at hαβ hcontra
    have ha := a.isLt; have hb := b.isLt
    have hab : (a : ℕ) ≠ (b : ℕ) := fun h => hαβ (by rw [h])
    have := koalaFRSγ_pow_left_inj (a := 32 * a.val + i) (b := 32 * b.val) (by omega) (by omega)
      hcontra
    omega
  · intro α hα i hipos hi hcontra
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hα
    obtain ⟨a, rfl⟩ := hα
    simp only [koalaFRSDomain, koalaFoldω, Function.Embedding.coeFn_mk, ← pow_add] at hcontra
    have ha := a.isLt
    have := koalaFRSγ_pow_left_inj (a := 32 * a.val + i) (b := 32 * a.val) (by omega) (by omega)
      hcontra
    omega

/-- The genuine §6.3.2 folded encoder: the degree-`< 2^20` folded Reed–Solomon
evaluation map on the `2^16` points of `koalaFRSDomain` with folding `s = 32`
(`k = 2^20`, `|L| = 2^16`, `s = 2^5`, rate `ρ = 1/2`), as an `F`-linear map
`(Fin 2^20 → F) →ₗ (Fin 2^16 → Fin 32 → F)`. Built as
`frsEvalOnPoints ∘ (degreeLTEquiv).symm`, mirroring `koalaEnc` with
`ReedSolomon.Folded.frsEvalOnPoints` in place of `evalOnPoints` (the scalar
`s = 1` case). The codeword alphabet is `A = Fin 32 → KoalaSextic`. -/
noncomputable def koalaFRSEnc :
    (Fin (2 ^ 20) → KoalaSextic) →ₗ[KoalaSextic] (Fin (2 ^ 16) → Fin 32 → KoalaSextic) :=
  (frsEvalOnPoints koalaFRSDomain 32 koalaFoldω).domRestrict
      (Polynomial.degreeLT KoalaSextic (2 ^ 20))
    ∘ₗ (Polynomial.degreeLTEquiv KoalaSextic (2 ^ 20)).symm.toLinearMap

open Classical in
/-- **Injectivity of the folded encoder** ([ABF26] Definition 6.1's "code as the
injective map"). Mathematically this would follow from `(L, s)`-admissibility of
`koalaFoldω` (`ReedSolomon.Folded.Admissible`, the GR08 condition that the `s·|L|`
folded evaluation points `{α · ω^i}` are pairwise distinct) together with
`k ≤ s·|L|` (here `2^20 ≤ 32·2^16 = 2^21`): a degree-`< k` polynomial vanishing
on `s·|L| ≥ k` distinct points is zero, so the unfolded evaluation — hence
`frsEvalOnPoints` on `degreeLT k` — would be injective. `koalaFRSDomain` is
zero-free precisely so `Admissible koalaFoldω` is not *provably false* (its
intra-orbit clause fails at `0`; see `koalaFRSDomain`).

**Now a full `sorry`-free derivation** through the in-tree bridge
`ReedSolomon.Folded.frsEvalOnPoints_domRestrict_injective` (the `Admissible ω → injective`
bridge that also backs the FRS dimension formula `dim_frsCode`): the encoder is
`(injective domRestrict) ∘ (injective degreeLTEquiv.symm)`. The `domRestrict` injectivity
consumes `koalaFRSDomain_admissible`, `koalaFRSγ_ne_zero`, and `k = 2^20 ≤ 32 · 2^16 =
2^21 = s · |ι|`. **Fully axiom-clean** (`[propext, Classical.choice, Quot.sound]`): the
order witness `koalaFRSγ_exists` it rests on is itself proven (abstract cyclicity). -/
theorem koalaFRSEnc_injective : Function.Injective koalaFRSEnc := by
  haveI : NeZero (2 ^ 20 : ℕ) := ⟨by norm_num⟩
  simp only [koalaFRSEnc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap]
  refine (ReedSolomon.Folded.frsEvalOnPoints_domRestrict_injective (k := 2 ^ 20) (s := 32)
    koalaFRSDomain koalaFoldω koalaFRSDomain_admissible koalaFRSγ_ne_zero ?_).comp
    (LinearEquiv.injective _)
  rw [Fintype.card_fin]; norm_num

/-- The folded-RS Proximity-Prize parameter point: the KoalaBear-sextic regime
with folding `s = 2^5 = 32` (`|F| = q^6 ≈ 2^186`, `ρ = 1/2`, eval domain
`|L| = 2^16`, message `k = 2^20`, `t = 128`). The codeword alphabet is the folded
`A = Fin 32 → KoalaSextic`; the `A = F` scalar case is `koalaIRS`. As with
`koalaIRS`, δ is swept inside `bestProvableError` (no pinned δ). -/
noncomputable def koalaFRS : ToyParams := by
  haveI : Fintype KoalaSextic := Fintype.ofFinite _
  classical
  exact
    { F := KoalaSextic
      ι := Fin (2 ^ 16)
      A := Fin 32 → KoalaSextic
      k := 2 ^ 20
      enc := koalaFRSEnc
      enc_injective := koalaFRSEnc_injective
      t := 128
      q := KoalaBear.fieldSize
      ext := 6
      ρ := 1 / 2
      s := 32
      n := 2 ^ 16 }

/-! ## Folded protocol reductions (Construction 6.2 / 6.9 at `s = 32`)

The genuine `s > 1` folded instantiations of the abstract toy-problem reductions,
obtained by feeding the folded encoder `koalaFRSEnc` (codeword alphabet
`A = Fin 32 → KoalaSextic = F^s`) through the now alphabet-generic
`Spec.reduction` / `Spec.oracleReduction` / `SimplifiedIOR.reduction` (Stage 1 of
the `F → A` generalization). Unlike the `s = 1` `Impl/IRS.lean` reductions
(codewords over the scalar alphabet `A = F`), these carry codewords over the
folded `F`-module `A = F^s`, so the **protocol layer** — not just the soundness
leaderboard — is exercised at a true folding parameter `s = 2^5`.

The `Fintype`/`DecidableEq` instances on the noncomputable `KoalaSextic` (and the
folded alphabet `Fin 32 → KoalaSextic`) are supplied exactly as in `koalaFRS`. -/

/-- Folded §6.3.2 instantiation of Construction 6.2 (`s = 32`, non-oracle
flavour): the abstract `Spec.reduction` with the folded encoder `koalaFRSEnc`. -/
noncomputable def reductionFRS (t : ℕ) :
    Reduction []ₒ
      (ToyProblem.Spec.Statement (F := KoalaSextic) (2 ^ 20) ×
        (∀ i, ToyProblem.Spec.OracleStatement (Fin (2 ^ 16)) (Fin 32 → KoalaSextic) i))
      (ToyProblem.Spec.Witness (F := KoalaSextic) (2 ^ 20))
      ToyProblem.Spec.OutputStatement
      ToyProblem.Spec.OutputWitness
      (ToyProblem.Spec.pSpec (ι := Fin (2 ^ 16)) (F := KoalaSextic) (2 ^ 20) t) := by
  haveI : Fintype KoalaSextic := Fintype.ofFinite _
  classical
  exact ToyProblem.Spec.reduction (ι := Fin (2 ^ 16)) (F := KoalaSextic)
    (A := Fin 32 → KoalaSextic) (k := 2 ^ 20) (t := t)
    (koalaFRSEnc : (Fin (2 ^ 20) → KoalaSextic) → (Fin (2 ^ 16) → Fin 32 → KoalaSextic))

/-- Folded §6.3.2 instantiation of Construction 6.9 (the simplified "attack
target" IOR) at `s = 32`. The encoder is unused by `SimplifiedIOR.reduction`'s
verifier (it only folds the instance), exactly as `Impl.IRS.simplifiedReductionIRS`. -/
noncomputable def simplifiedReductionFRS :
    Reduction []ₒ
      (ToyProblem.Spec.Statement (F := KoalaSextic) (2 ^ 20) ×
        (∀ i, ToyProblem.Spec.OracleStatement (Fin (2 ^ 16)) (Fin 32 → KoalaSextic) i))
      (ToyProblem.Spec.Witness (F := KoalaSextic) (2 ^ 20))
      (ToyProblem.SimplifiedIOR.OutputStatement (F := KoalaSextic) (2 ^ 20) ×
        (∀ i, ToyProblem.SimplifiedIOR.OutputOracleStatement
          (Fin (2 ^ 16)) (Fin 32 → KoalaSextic) i))
      (ToyProblem.SimplifiedIOR.OutputWitness (F := KoalaSextic) (2 ^ 20))
      (ToyProblem.SimplifiedIOR.pSpec (F := KoalaSextic)) := by
  haveI : Fintype KoalaSextic := Fintype.ofFinite _
  classical
  exact ToyProblem.SimplifiedIOR.reduction (ι := Fin (2 ^ 16)) (F := KoalaSextic)
    (A := Fin 32 → KoalaSextic) (k := 2 ^ 20)

/-- Oracle-flavour folded §6.3.2 instantiation of Construction 6.2 (`s = 32`). -/
noncomputable def oracleReductionFRS (t : ℕ) :
    OracleReduction []ₒ
      (ToyProblem.Spec.Statement (F := KoalaSextic) (2 ^ 20))
      (ToyProblem.Spec.OracleStatement (Fin (2 ^ 16)) (Fin 32 → KoalaSextic))
      (ToyProblem.Spec.Witness (F := KoalaSextic) (2 ^ 20))
      ToyProblem.Spec.OutputStatement
      ToyProblem.Spec.OutputOracleStatement
      ToyProblem.Spec.OutputWitness
      (ToyProblem.Spec.pSpec (ι := Fin (2 ^ 16)) (F := KoalaSextic) (2 ^ 20) t) := by
  haveI : Fintype KoalaSextic := Fintype.ofFinite _
  classical
  exact ToyProblem.Spec.oracleReduction (ι := Fin (2 ^ 16)) (F := KoalaSextic)
    (A := Fin 32 → KoalaSextic) (k := 2 ^ 20) (t := t)
    (koalaFRSEnc : (Fin (2 ^ 20) → KoalaSextic) → (Fin (2 ^ 16) → Fin 32 → KoalaSextic))

open Classical in
set_option maxRecDepth 8000 in
/-- **The folded encoder's image is exactly the folded RS code** `FRS[koalaFRSDomain, 2^20,
32, koalaFoldω]`. The FRS counterpart of `koalaEnc_range`: `koalaFRSEnc = frsEvalOnPoints ∘
(degreeLTEquiv).symm`, and as the latter ranges over all degree-`< 2^20` polynomials its
image is `(degreeLT 2^20).map (frsEvalOnPoints …) = frsCode …`. This identifies
`koalaFRS.code` with `frsCode`, unlocking the folded MDS distance below. -/
theorem koalaFRSEnc_range :
    Set.range ⇑koalaFRSEnc =
      (↑(ReedSolomon.Folded.frsCode koalaFRSDomain (2 ^ 20) 32 koalaFoldω) :
        Set (Fin (2 ^ 16) → Fin 32 → KoalaSextic)) := by
  ext y
  rw [SetLike.mem_coe, ReedSolomon.Folded.frsCode, Submodule.mem_map]
  simp only [Set.mem_range]
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨↑((Polynomial.degreeLTEquiv KoalaSextic (2 ^ 20)).symm m), Submodule.coe_mem _, ?_⟩
    simp only [koalaFRSEnc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
      LinearMap.domRestrict_apply]
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Polynomial.degreeLTEquiv KoalaSextic (2 ^ 20) ⟨p, hp⟩, ?_⟩
    simp only [koalaFRSEnc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
      LinearEquiv.symm_apply_apply, LinearMap.domRestrict_apply]

open Classical in
/-- **Folded-RS minimum relative distance** — now a full `sorry`-free derivation through the
new in-tree folded-distance bridge `ReedSolomon.Folded.minDist_frsCode`.
`minRelHammingDistCode koalaFRS.code = 32769/65536`, the folded-Singleton (MDS-type)
distance for `FRS[F, L, 2^20, 32, ω]`: a nonzero degree-`< 2^20` polynomial has `< 2^20`
roots, so it vanishes on `≤ ⌊(2^20-1)/32⌋ = 32767` *whole* folded symbols, hence the folded
Hamming distance is `D = |L| − 32767 = 65536 − 32767 = 32769` and `δ_min = D/|L| =
32769/65536`. Via `koalaFRSEnc_range` (the code *is* `frsCode`), `minDist_frsCode`, and the
absolute→relative bridge `minDist_div_card_eq_minRelHammingDistCode`. **Fully axiom-clean**
(`[propext, Classical.choice, Quot.sound]`): the order witness `koalaFRSγ_exists` reached
through `koalaFRSDomain_admissible` is itself proven (abstract cyclicity). -/
theorem koalaFRS_minRelDist :
    minRelHammingDistCode koalaFRS.code = (32769 / 65536 : ℚ≥0) := by
  haveI : Nonempty koalaFRS.ι := inferInstanceAs (Nonempty (Fin (2 ^ 16)))
  haveI : NeZero (2 ^ 20 : ℕ) := ⟨by norm_num⟩
  have hcode : koalaFRS.code =
      (↑(ReedSolomon.Folded.frsCode koalaFRSDomain (2 ^ 20) 32 koalaFoldω) :
        Set (Fin (2 ^ 16) → Fin 32 → KoalaSextic)) := koalaFRSEnc_range
  have hmin : Code.minDist koalaFRS.code = 32769 := by
    have h := ReedSolomon.Folded.minDist_frsCode (k := 2 ^ 20) (s := 32) (by norm_num)
      koalaFRSDomain koalaFoldω koalaFRSDomain_admissible koalaFRSγ_ne_zero
      (by rw [Fintype.card_fin]; norm_num)
    simp only [Fintype.card_fin] at h
    norm_num at h
    rw [hcode]; exact h
  have hbridge := minDist_div_card_eq_minRelHammingDistCode koalaFRS.code
  have hcardι : Fintype.card koalaFRS.ι = 65536 := by
    change Fintype.card (Fin (2 ^ 16)) = 65536
    rw [Fintype.card_fin]; norm_num
  rw [hmin, hcardι] at hbridge
  have hQ : ((minRelHammingDistCode koalaFRS.code : ℚ≥0) : ℚ) = ((32769 / 65536 : ℚ≥0) : ℚ) := by
    rw [← hbridge]; push_cast; norm_num
  exact_mod_cast hQ

/-- **Attack-side spot-check integer leaf (sorry-free):** `2^(-128.01) ≤
(32767/65536)^128`. The crux of the folded MDS sweep-floor. Split off `2^(-128)`:
since `32767/65536 = (32767/32768)·(1/2)`, this reduces to `2^(-0.01) ≤
(32767/32768)^128`. Bernoulli (`one_add_mul_le_pow`) gives `(32767/32768)^128 =
(1 - 1/32768)^128 ≥ 1 - 128/32768 = 255/256`, and `2^(-0.01) ≤ 255/256` is the
**proven integer inequality** `256^100 ≤ 2·255^100` (`log₁₀`: `100·2.4082 =
240.82 ≤ 0.301 + 240.65`). No float `#eval`. (True value `(32767/65536)^128 ≈
2^(-128.006)`, comfortably above the `2^(-128.01)` ceiling.) -/
theorem koalaFRS_spotcheck_lb :
    (2 : ℝ≥0) ^ (-(128.01 : ℝ)) ≤ ((32767 : ℝ≥0) / 65536) ^ (128 : ℕ) := by
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [show (-128.01 : ℝ) = (-0.01 : ℝ) + (-(128 : ℝ)) by norm_num]
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  rw [show (32767:ℝ)/65536 = (32767/32768) * (1/2) by ring]
  rw [mul_pow]
  rw [show ((1:ℝ)/2)^128 = 2^(-(128:ℝ)) by
    rw [Real.rpow_neg (by norm_num), show (128:ℝ) = ((128:ℕ):ℝ) by norm_num,
        Real.rpow_natCast]; norm_num]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hbern : (255 : ℝ) / 256 ≤ (32767/32768 : ℝ)^128 := by
    have := one_add_mul_le_pow (a := (-1/32768:ℝ)) (by norm_num) 128
    linarith
  have h2neg : (2:ℝ)^(-0.01:ℝ) ≤ 255/256 := by
    apply le_of_pow_le_pow_left₀ (n := 100) (by norm_num) (by positivity)
    rw [← Real.rpow_natCast ((2:ℝ)^(-0.01:ℝ)) 100]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  linarith [hbern, h2neg]

/-- **Folded-RS attack upper bound (`128.01` bits) at the KoalaBear/`s=32`/`t=128`
point — the δ-sweep floor, certified from the spot-check term alone.** As of the
FRS-anchor-reduction session the proof is a **full formalized reduction** (no longer
an opaque `sorry`): `le_bestProvableError` reduces the infimum-`≥` goal to a per-δ
floor over the window `(0, δ_min)`, and at *every* admissible δ the convex
combination dominates its round-2 spot-check term `(1-δ)^t` (drop the nonnegative
`winningSetSoundness` term), which is `≥ (1-δ_min)^128` by monotonicity. The folded
code's **MDS relative distance** `δ_min = 32769/65536` (`koalaFRS_minRelDist`) pins
`1 - δ > 32767/65536`, and `(32767/65536)^128 ≥ 2^(-128.01)` is the sorry-free leaf
`koalaFRS_spotcheck_lb`. The folded distance `koalaFRS_minRelDist` is now itself proven
(via `minDist_frsCode` + the proven `koalaFRSγ_exists`), so this attack anchor is **fully
axiom-clean** (`[propext, Classical.choice, Quot.sound]`, no `sorryAx`) — the whole Y side
owes nothing, and no Elias/list-size lower bound enters (strictly stronger than the
interleaved IRS attack `caUpperBoundAttack`, which owes one CA lower bound).

**Why `128.01`, and stronger than the paper's per-`δ*` reading.** `(1-δ_min)^128 =
(32767/65536)^128 ≈ 2^(-128.006)`, so the ceiling rounds **up** to `128.01`. The
§6.3.2 Elias table (`tab:subspace-elias-lowerbound-thresholds`, `δ* = 0.499`)
reports `2^(-127.63) = (1-0.499)^128`, the *point* soundness at `δ*` — **not** the
sweep floor: just above `δ*` the spot-check keeps dropping toward `2^(-128)` at
`δ_min`, the same sub-band subtlety that forced the interleaved ceiling
`116.49 → 117`. The fact pinning the window here is a *distance* bound (now proven via
`minDist_frsCode`), not a list-size bound — so this anchor is fully axiom-clean. -/
noncomputable def frsUpperBound : SecurityUpperBound koalaFRS where
  bits := 128.01
  proof := by
    -- Sweep floor from the spot-check term alone, fully formalized **down to the
    -- (now-proven) folded distance** `koalaFRS_minRelDist`. `le_bestProvableError` reduces
    -- to a per-δ floor over (0, δ_min = 32769/65536); drop the nonnegative
    -- winningSetSoundness term, then `(1-δ)^128 ≥ (32767/65536)^128 ≥ 2^(-128.01)`
    -- by monotonicity + `koalaFRS_spotcheck_lb`. No Elias/list-size bound needed.
    refine le_bestProvableError koalaFRS (fun δ hδ => ?_)
    have hmin : ((minRelHammingDistCode koalaFRS.code : ℚ≥0) : ℝ≥0) = (32769 / 65536 : ℝ≥0) := by
      rw [koalaFRS_minRelDist]; push_cast; norm_num
    rw [Set.mem_Ioo, hmin] at hδ
    obtain ⟨hδpos, hδlt⟩ := hδ
    rw [ENNReal.coe_le_coe]
    have ht : koalaFRS.t = 128 := rfl
    rw [ht]
    -- Drop the nonnegative winningSetSoundness term, floor by the spot-check term.
    refine le_trans ?_ (le_add_of_nonneg_right zero_le')
    -- ⊢ 2^(-128.01) ≤ (1-δ)^128
    have h1md : (32767 / 65536 : ℝ≥0) ≤ 1 - δ := by
      apply le_tsub_of_add_le_right
      calc (32767 / 65536 : ℝ≥0) + δ ≤ 32767 / 65536 + 32769 / 65536 := by gcongr
        _ = 1 := by norm_num
    exact le_trans koalaFRS_spotcheck_lb (pow_le_pow_left₀ zero_le' h1md 128)

/-! ## The large-folding row `s = 2^12 = 4096` at `t = 128` — gap-closing

The `s = 32` anchors above sit at the τ-subspace-design operating point `r = 8`,
`δ = 7/48 ≈ 0.146`, the *largest* δ that `s = 2^5` admits: `τ(r+1) = s·ρ/(s−r)`
blows past `1` once `r` grows (for `s ≤ 2^4` *no* `r` gives provable soundness at
all). The provable side is therefore pinned at the low `δ = 0.146`, where
`(1−δ)^128 = (41/48)^128 ≈ 2^(-29)` — and the `98.91`-bit gap to the `≈ 2^(-128)`
attack is *irreducible at `s = 32`* (it is a folding-size limit, not a
missing-citation: no sharper coding-theory bound moves it, because the
subspace-design analysis cannot reach a higher δ at this folding).

**Larger folding closes the gap.** At `s = 2^12 = 4096` the minimizing operating
point is `r = 108` (`tab:subspace-design-security-analysis`), where `τ(r+1) =
4096·(1/2)/(4096−108) = 512/997` and the spot-check base is `1−δ = τ(r+1) +
3/(2r) = 512/997 + 1/72 = 37861/71784 ≈ 0.5274` — *close to capacity* `ρ = 1/2`.
The provable side is then `(37861/71784)^128 ≈ 2^(-118.14)`, a `≈ 10`-bit gap to
the attack. This is the **same** τ-subspace-design `ε_mca` admit family as the
`s = 32` anchor (`ε_mca(C, δ) ≤ (r·|L| + 4r³)/|F|`, ABF26 §6.3.2 / `thm:subspace-
design-mca`); folding does **not** swap in a different (capacity-corollary) bound —
it lets the *operating point itself* climb to high δ, which small `s` cannot.

**Construction scaling (held fixed across the `s`-sweep).** The §6.3.2 example
fixes `|F| = q^6 ≈ 2^186`, message `k = 2^20`, rate `ρ = 1/2`, and the *unfolded*
length `s·|L| = 2^21`; folding `s` then sets `|L| = 2^21/s`. (Validated against
the paper's argument-size column: `R·(256·log|L| + 62·s)` reproduces the table's
`3.91 MiB` for `s = 2^12` only with `|L| = 2^21/s = 2^9`, not `|L| = 2^16`.)
So `s = 2^12` ⇒ `|L| = 2^9 = 512`, `k = 2^20`. The folded MDS distance is then
`δ_min = (|L| − ⌊(k−1)/s⌋)/|L| = (512 − 255)/512 = 257/512` (a degree-`< 2^20`
polynomial has `< 2^20` roots, so `< (2^20−1)/2^12 = 256`, i.e. `≤ 255`, *whole*
folded symbols can vanish — the same count that gives the `s = 32` value
`32769/65536`). -/

/-- The `2^9 = 512`-point folded-RS evaluation domain for the `s = 2^12` row, the genuine
multiplicative coset `j ↦ γ^(2^12·j) ⊆ KoalaSextic` (the cyclic subgroup `⟨γ^(2^12)⟩`),
exactly as `koalaFRSDomain` but at folding `2^12`. Injectivity is `pow`-injectivity below
`orderOf γ`: `2^12·j < 2^12·2^9 = 2^21 ≤ orderOf γ` (`koalaFRSγ_pow_left_inj`). -/
noncomputable def koalaFRS12Domain : Fin (2 ^ 9) ↪ KoalaSextic where
  toFun j := koalaFRSγ ^ (2 ^ 12 * j.val)
  inj' i j hij := by
    have hi : 2 ^ 12 * (i : ℕ) < 2 ^ 21 := by have := i.isLt; omega
    have hj : 2 ^ 12 * (j : ℕ) < 2 ^ 21 := by have := j.isLt; omega
    exact Fin.val_injective (by have := koalaFRSγ_pow_left_inj hi hj hij; omega)

open Classical in
/-- **`(L, 2^12)`-admissibility of the `s = 2^12` coset domain.** The `2^12 · 2^9 = 2^21`
folded points `γ^(2^12·a) · γ^i = γ^(2^12·a + i)` are pairwise distinct, all exponents
below `2^21 ≤ orderOf γ`; both `Admissible` conjuncts reduce to `ℕ`-arithmetic via
`koalaFRSγ_pow_left_inj`. Same (now-proven) order bound as `koalaFRSDomain_admissible`. -/
lemma koalaFRS12Domain_admissible :
    ReedSolomon.Folded.Admissible (Finset.univ.map koalaFRS12Domain) (2 ^ 12) koalaFoldω := by
  refine ⟨?_, ?_⟩
  · intro α hα β hβ hαβ i hi hcontra
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hα hβ
    obtain ⟨a, rfl⟩ := hα
    obtain ⟨b, rfl⟩ := hβ
    simp only [koalaFRS12Domain, koalaFoldω, Function.Embedding.coeFn_mk, ← pow_add] at hαβ hcontra
    have ha := a.isLt; have hb := b.isLt
    have hab : (a : ℕ) ≠ (b : ℕ) := fun h => hαβ (by rw [h])
    have := koalaFRSγ_pow_left_inj (a := 2 ^ 12 * a.val + i) (b := 2 ^ 12 * b.val)
      (by omega) (by omega) hcontra
    omega
  · intro α hα i hipos hi hcontra
    simp only [Finset.mem_map, Finset.mem_univ, true_and] at hα
    obtain ⟨a, rfl⟩ := hα
    simp only [koalaFRS12Domain, koalaFoldω, Function.Embedding.coeFn_mk, ← pow_add] at hcontra
    have ha := a.isLt
    have := koalaFRSγ_pow_left_inj (a := 2 ^ 12 * a.val + i) (b := 2 ^ 12 * a.val)
      (by omega) (by omega) hcontra
    omega

/-- The `s = 2^12 = 4096` folded encoder: degree-`< 2^20` folded RS evaluation on
the `2^9` points of `koalaFRS12Domain` with folding `s = 4096` (`k = 2^20`,
`|L| = 2^9`, rate `ρ = 1/2`), as `(Fin 2^20 → F) →ₗ (Fin 2^9 → Fin 4096 → F)`.
Same `frsEvalOnPoints ∘ (degreeLTEquiv).symm` shape as `koalaFRSEnc`, with the
folding parameter `2^12` and the smaller `2^9`-point domain. -/
noncomputable def koalaFRS12Enc :
    (Fin (2 ^ 20) → KoalaSextic) →ₗ[KoalaSextic] (Fin (2 ^ 9) → Fin (2 ^ 12) → KoalaSextic) :=
  (frsEvalOnPoints koalaFRS12Domain (2 ^ 12) koalaFoldω).domRestrict
      (Polynomial.degreeLT KoalaSextic (2 ^ 20))
    ∘ₗ (Polynomial.degreeLTEquiv KoalaSextic (2 ^ 20)).symm.toLinearMap

open Classical in
/-- **Injectivity of the `s = 2^12` folded encoder** — the large-folding counterpart of
`koalaFRSEnc_injective`, now a full `sorry`-free derivation through the in-tree bridge
`ReedSolomon.Folded.frsEvalOnPoints_domRestrict_injective`, consuming
`koalaFRS12Domain_admissible`, `koalaFRSγ_ne_zero`, and `k = 2^20 ≤ s·|L| = 2^12·2^9 =
2^21`. Same (now-proven) shared order witness `koalaFRSγ_exists` as the `s = 32` row;
fully axiom-clean. -/
theorem koalaFRS12Enc_injective : Function.Injective koalaFRS12Enc := by
  haveI : NeZero (2 ^ 20 : ℕ) := ⟨by norm_num⟩
  simp only [koalaFRS12Enc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap]
  refine (ReedSolomon.Folded.frsEvalOnPoints_domRestrict_injective (k := 2 ^ 20) (s := 2 ^ 12)
    koalaFRS12Domain koalaFoldω koalaFRS12Domain_admissible koalaFRSγ_ne_zero ?_).comp
    (LinearEquiv.injective _)
  rw [Fintype.card_fin]; norm_num

/-- The large-folding Proximity-Prize parameter point: KoalaBear-sextic with
folding `s = 2^12 = 4096` (`|F| = q^6 ≈ 2^186`, `ρ = 1/2`, eval domain `|L| = 2^9`,
message `k = 2^20`, `t = 128`). Codeword alphabet `A = Fin 4096 → KoalaSextic`. As
with `koalaFRS`, δ is swept inside `bestProvableError`. -/
noncomputable def koalaFRS12 : ToyParams := by
  haveI : Fintype KoalaSextic := Fintype.ofFinite _
  classical
  exact
    { F := KoalaSextic
      ι := Fin (2 ^ 9)
      A := Fin (2 ^ 12) → KoalaSextic
      k := 2 ^ 20
      enc := koalaFRS12Enc
      enc_injective := koalaFRS12Enc_injective
      t := 128
      q := KoalaBear.fieldSize
      ext := 6
      ρ := 1 / 2
      s := 2 ^ 12
      n := 2 ^ 9 }

open Classical in
set_option maxRecDepth 8000 in
/-- **The `s = 2^12` folded encoder's image is exactly `frsCode`** — the large-folding
counterpart of `koalaFRSEnc_range`. -/
theorem koalaFRS12Enc_range :
    Set.range ⇑koalaFRS12Enc =
      (↑(ReedSolomon.Folded.frsCode koalaFRS12Domain (2 ^ 20) (2 ^ 12) koalaFoldω) :
        Set (Fin (2 ^ 9) → Fin (2 ^ 12) → KoalaSextic)) := by
  ext y
  rw [SetLike.mem_coe, ReedSolomon.Folded.frsCode, Submodule.mem_map]
  simp only [Set.mem_range]
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨↑((Polynomial.degreeLTEquiv KoalaSextic (2 ^ 20)).symm m), Submodule.coe_mem _, ?_⟩
    simp only [koalaFRS12Enc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
      LinearMap.domRestrict_apply]
  · rintro ⟨p, hp, rfl⟩
    refine ⟨Polynomial.degreeLTEquiv KoalaSextic (2 ^ 20) ⟨p, hp⟩, ?_⟩
    simp only [koalaFRS12Enc, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
      LinearEquiv.symm_apply_apply, LinearMap.domRestrict_apply]

open Classical in
set_option maxRecDepth 8000 in
/-- **Folded-RS minimum relative distance at `s = 2^12`** — now a full `sorry`-free
derivation through `ReedSolomon.Folded.minDist_frsCode`, exactly as `koalaFRS_minRelDist`.
`minRelHammingDistCode koalaFRS12.code = 257/512`, the folded-Singleton distance for
`FRS[F, L, 2^20, 4096, ω]`: a nonzero degree-`< 2^20` polynomial vanishes on
`≤ ⌊(2^20−1)/4096⌋ = 255` whole folded symbols, so `D = |L| − 255 = 512 − 255 = 257` and
`δ_min = 257/512`. Same (now-proven) shared order witness `koalaFRSγ_exists` as the
`s = 32` row; fully axiom-clean. -/
theorem koalaFRS12_minRelDist :
    minRelHammingDistCode koalaFRS12.code = (257 / 512 : ℚ≥0) := by
  haveI : Nonempty koalaFRS12.ι := inferInstanceAs (Nonempty (Fin (2 ^ 9)))
  haveI : NeZero (2 ^ 20 : ℕ) := ⟨by norm_num⟩
  have hcode : koalaFRS12.code =
      (↑(ReedSolomon.Folded.frsCode koalaFRS12Domain (2 ^ 20) (2 ^ 12) koalaFoldω) :
        Set (Fin (2 ^ 9) → Fin (2 ^ 12) → KoalaSextic)) := koalaFRS12Enc_range
  have hmin : Code.minDist koalaFRS12.code = 257 := by
    have h := ReedSolomon.Folded.minDist_frsCode (k := 2 ^ 20) (s := 2 ^ 12) (by norm_num)
      koalaFRS12Domain koalaFoldω koalaFRS12Domain_admissible koalaFRSγ_ne_zero
      (by rw [Fintype.card_fin]; norm_num)
    simp only [Fintype.card_fin] at h
    norm_num at h
    rw [hcode]; exact h
  have hbridge := minDist_div_card_eq_minRelHammingDistCode koalaFRS12.code
  have hcardι : Fintype.card koalaFRS12.ι = 512 := by
    change Fintype.card (Fin (2 ^ 9)) = 512
    rw [Fintype.card_fin]; norm_num
  rw [hmin, hcardι] at hbridge
  have hQ : ((minRelHammingDistCode koalaFRS12.code : ℚ≥0) : ℚ) = ((257 / 512 : ℚ≥0) : ℚ) := by
    rw [← hbridge]; push_cast; norm_num
  exact_mod_cast hQ

/-- **Attack-side spot-check integer leaf (sorry-free):** `2^(-128.75) ≤
(255/512)^128`, the folded MDS sweep-floor for `s = 2^12`. Split `255/512 =
(255/256)·(1/2)`, reduce `(1/2)^128 = 2^(-128)` to `2^(-0.75) ≤ (255/256)^128`.
Unlike the `s = 32` leaf (step `1/256` is far coarser than `1/32768`), Bernoulli
is too weak here, so we **sandwich through `3/5`**: `2^(-0.75) ≤ 3/5` (the small
integer fact `(3/5)^4 = 81/625 ≥ 1/8 = 2^(-3)`) and `3/5 ≤ (255/256)^128` (the
integer fact `3·256^128 ≤ 5·255^128`). True value `(255/512)^128 ≈ 2^(-128.723)`,
comfortably above the `2^(-128.75)` ceiling. No float `#eval`. -/
theorem koalaFRS12_spotcheck_lb :
    (2 : ℝ≥0) ^ (-(128.75 : ℝ)) ≤ ((255 : ℝ≥0) / 512) ^ (128 : ℕ) := by
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [show (-128.75 : ℝ) = (-0.75 : ℝ) + (-(128 : ℝ)) by norm_num]
  rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  rw [show (255:ℝ)/512 = (255/256) * (1/2) by ring]
  rw [mul_pow]
  rw [show ((1:ℝ)/2)^128 = 2^(-(128:ℝ)) by
    rw [Real.rpow_neg (by norm_num), show (128:ℝ) = ((128:ℕ):ℝ) by norm_num,
        Real.rpow_natCast]; norm_num]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  -- ⊢ 2^(-0.75) ≤ (255/256)^128, via the rational sandwich 2^(-0.75) ≤ 3/5 ≤ (255/256)^128
  have hsand : (3 : ℝ) / 5 ≤ (255 / 256 : ℝ) ^ 128 := by
    rw [div_pow, div_le_div_iff₀ (by norm_num) (by positivity)]
    exact_mod_cast (by norm_num : (3:ℕ) * 256 ^ 128 ≤ 255 ^ 128 * 5)
  have h2neg : (2:ℝ) ^ (-0.75:ℝ) ≤ 3 / 5 := by
    apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity)
    rw [← Real.rpow_natCast ((2:ℝ)^(-0.75:ℝ)) 4]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  linarith [hsand, h2neg]

/-- **Folded-RS attack upper bound (`128.75` bits) at the KoalaBear/`s=2^12`/
`t=128` point — the δ-sweep floor.** Same full-reduction shape as
`frsUpperBound`: `le_bestProvableError` reduces to a per-δ floor over
`(0, δ_min = 257/512)`; drop the nonnegative `winningSetSoundness` term, then
`(1−δ)^128 ≥ (255/512)^128 ≥ 2^(-128.75)` by monotonicity + `koalaFRS12_spotcheck_lb`.
The folded distance `koalaFRS12_minRelDist` is itself proven, so this anchor is fully
axiom-clean (`[propext, Classical.choice, Quot.sound]`).

`(1−δ_min)^128 = (255/512)^128 ≈ 2^(-128.723)`, so the ceiling rounds **up** to
`128.75` (the `3/4`-granularity needed to keep the sandwich integer-leaf tractable;
a tighter `128.73` would force an intractable `≥ 1234`-digit power). -/
noncomputable def frsUpperBound12 : SecurityUpperBound koalaFRS12 where
  bits := 128.75
  proof := by
    refine le_bestProvableError koalaFRS12 (fun δ hδ => ?_)
    have hmin : ((minRelHammingDistCode koalaFRS12.code : ℚ≥0) : ℝ≥0) = (257 / 512 : ℝ≥0) := by
      rw [koalaFRS12_minRelDist]; push_cast; norm_num
    rw [Set.mem_Ioo, hmin] at hδ
    obtain ⟨hδpos, hδlt⟩ := hδ
    rw [ENNReal.coe_le_coe]
    have ht : koalaFRS12.t = 128 := rfl
    rw [ht]
    refine le_trans ?_ (le_add_of_nonneg_right zero_le')
    have h1md : (255 / 512 : ℝ≥0) ≤ 1 - δ := by
      apply le_tsub_of_add_le_right
      calc (255 / 512 : ℝ≥0) + δ ≤ 255 / 512 + 257 / 512 := by gcongr
        _ = 1 := by norm_num
    exact le_trans koalaFRS12_spotcheck_lb (pow_le_pow_left₀ zero_le' h1md 128)

end Impl.FRS

end ToyProblem
