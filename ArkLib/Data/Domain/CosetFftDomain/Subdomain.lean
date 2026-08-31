/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ArkLib.Data.Domain.CosetFftDomain.Block
import ArkLib.Data.Domain.CosetFftDomain.Ops
import ArkLib.Data.Domain.FftDomain.Ops
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Subdomains of smooth coset FFT domains

This file develops the hierarchy of subdomains of a smooth coset FFT domain.

It also studies roots, cardinalities of fibers of powering maps, and provides
a root-finding procedure.

## Main definitions

- `CosetFftDomainClass.subdomain_embed`:
  Embedding of subdomain indices into the ambient domain.
- `CosetFftDomainClass.subdomain`:
  The `i`th subdomain.
- `CosetFftDomain.twoNthRoot`:
  A constructive `2 ^ i`th-root operation.

## Main results

- `pow_mem_of_mem`:
  Powers move elements down the subdomain tower.
- `card_block_of_mem_subdomain`:
  Exact cardinality of blocks when the block point is a member of a subdomain.
- `root_exists`:
  Existence of roots in higher subdomains.
- `square_roots_explicit`:
  Explicit description of square roots.
- `twoNthRoot_correct`:
  Correctness of the root-finding algorithm.

-/

namespace Domain

variable {F : Type} [Field F]

namespace CosetFftDomainClass

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [CosetFftDomainClass D (Fin (2 ^ n)) F]

/-- Embed the index type of the `i`th subdomain
  into the index type of the ambient smooth coset FFT domain.
  When `i < n`, this sends `k` to `2 ^ i * k`;
  when `i ≥ n`, the subdomain is trivial and everything maps to `0`. -/
protected def subdomain_embed (i : ℕ) (k : Fin (2 ^ (n - i))) : Fin (2 ^ n) :=
  if hi : i ≥ n
  then 0
  else ⟨2 ^ i * k.val, match k with
    | ⟨k, hk⟩ => by
      simp only at hk ⊢
      by_cases hk_zero : k = 0 <;> try (subst hk_zero; simp)
      calc 2 ^ i * k < 2 ^ i * 2 ^ (n - i) :=
              Nat.mul_lt_mul_of_pos_left hk (by positivity)
          _ = 2 ^ n := by rw [←pow_add, Nat.add_sub_of_le (by omega)]⟩

/-- The subdomain embedding preserves addition. -/
protected lemma subdomain_embed_add (i : ℕ) (a b : Fin (2 ^ (n - i))) :
  CosetFftDomainClass.subdomain_embed i (a + b) =
    CosetFftDomainClass.subdomain_embed i a + CosetFftDomainClass.subdomain_embed i b := by
  unfold CosetFftDomainClass.subdomain_embed
  simp +decide [Fin.val_add]
  ring_nf
  norm_num [Fin.ext_iff, Fin.val_add, Fin.val_mul]
  by_cases hi : n ≤ i
  · simp [hi]
  · simp only [hi, ↓reduceDIte]
    rw [←add_mul, ←Nat.mul_mod_mul_right, ←pow_add,
      Nat.sub_add_cancel (by omega)]

/-- The subdomain embedding sends `0` to `0`. -/
protected lemma subdomain_embed_zero (i : ℕ) :
  CosetFftDomainClass.subdomain_embed i 0 = (0 : Fin (2 ^ n)) := by
  aesop (add simp [CosetFftDomainClass.subdomain_embed])

/-- The subdomain embedding is injective. -/
protected lemma subdomain_embed_injective (i : ℕ) :
  Function.Injective (CosetFftDomainClass.subdomain_embed (n := n) i) := fun a b h ↦ by
  by_cases hi : n ≤ i
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    have : n - i = 0 := by omega
    rw [this] at ha
    rw [this] at hb
    simp_all
  · simp_all [Fin.ext_iff, CosetFftDomainClass.subdomain_embed]

/-- Given a smooth coset FFT domain `ω` of log-order `n`, return its subdomain of log-order `n - i`.

The resulting coset generator is `ω 0 ^ 2 ^ i`. -/
def subdomain (ω : D) (i : ℕ) :
  SmoothCosetFftDomain (n - i) F :=
  ⟨{ toFun := fun k ↦
    mkSubgroupUnit ω (CosetFftDomainClass.subdomain_embed i (Multiplicative.toAdd k))
     map_one' := by
      aesop (add simp [CosetFftDomainClass.subdomain_embed_zero, mkSubgroupUnit])
     map_mul' := by
      aesop
        (add simp [toAdd_mul, CosetFftDomainClass.subdomain_embed_add,
                   mkSubgroupUnit, CosetFftDomainClass.map_add])
        (add safe (by field_simp)) },
   by
     intro a b h
     have h2 := CosetFftDomainClass.injective ω (by simpa [mkSubgroupUnit] using h)
     have h3 := Multiplicative.ofAdd.injective h2
     exact Multiplicative.ofAdd.injective (CosetFftDomainClass.subdomain_embed_injective i h3),
  ⟨(ω 0) ^ 2 ^ i, (ω 0)⁻¹ ^ 2 ^ i, by simp, by simp⟩⟩

variable {ω : D} {x : F}

/-- Membership in subdomains is invariant under equal subdomain indices. -/
lemma mem_subdomain_of_eq_vals
  {i j : ℕ}
  (hij : i = j) :
  x ∈ subdomain ω i ↔ x ∈ subdomain ω j := by rw [hij]

/-- The coset generator of the `i`th subdomain is `ω 0 ^ 2 ^ i`. -/
@[simp]
lemma subdomain_generator_pow_generator (i : ℕ) :
  (subdomain ω i).cosetGenerator = ω 0 ^ 2 ^ i := rfl

/-- The normalized subgroup unit of a subdomain is the ambient normalized subgroup unit at the
embedded index. -/
@[simp]
lemma subdomain_subgroupUnit (i : ℕ) (k : Fin (2 ^ (n - i))) :
    (subdomain ω i).subgroupUnit k =
      mkSubgroupUnit ω (CosetFftDomainClass.subdomain_embed i k) := rfl

/-- Evaluation of a subdomain in terms of the ambient domain. -/
lemma subdomain_apply (i : ℕ) (k : Fin (2 ^ (n - i))) :
    subdomain ω i k =
      ω 0 ^ 2 ^ i * mkSubgroupUnit ω (CosetFftDomainClass.subdomain_embed i k) := by
  rw [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain,
    subdomain_generator_pow_generator, subdomain_subgroupUnit]

set_option warning.simp.varHead false in
@[simp]
lemma subdomain_0_apply (i : Fin (2 ^ n)) :
  no_index (subdomain ω 0 i) = ω i := by
  rw [subdomain_apply]
  by_cases hn : n = 0
  · subst n
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [CosetFftDomainClass.subdomain_embed, mkSubgroupUnit]
  · simp [CosetFftDomainClass.subdomain_embed, mkSubgroupUnit, hn]

set_option warning.simp.varHead false in
/-- Membership to the `0`th subdomain is
  the same as membership to the original coset FFT domain. -/
@[simp]
lemma mem_subdomain_0_iff_mem :
  no_index (x ∈ subdomain ω 0) ↔ x ∈ ω := by simp [mem_def]

/-- The `n`th subdomain consists exactly of the single element `ω 0 ^ 2 ^ n`. -/
lemma mem_subdomain_n_iff_eq_pow_generator :
  x ∈ subdomain ω n ↔ x = ω 0 ^ 2 ^ n := by
  rw [mem_def]
  constructor
  · rintro ⟨i, rfl⟩
    simp [subdomain_apply, CosetFftDomainClass.subdomain_embed, mkSubgroupUnit]
  · intro hx
    refine ⟨0, ?_⟩
    simpa [subdomain_apply, CosetFftDomainClass.subdomain_embed, mkSubgroupUnit] using hx.symm

/-- Powers of normalized subgroup units correspond to additive multiples of their indices. -/
private lemma mkSubgroupUnit_pow (ω : D) (a : Fin (2 ^ n)) (k : ℕ) :
  (mkSubgroupUnit ω a : F) ^ k = mkSubgroupUnit ω (k • a) := by
  induction k
  · aesop (add simp [pow_zero, zero_nsmul, mkSubgroupUnit])
  · have := CosetFftDomainClass.map_add ω (‹_› • a) a
    aesop
      (add simp
        [pow_succ',
         add_smul,
         mkSubgroupUnit,
         mul_add,
         add_mul,
         mul_assoc,
         mul_comm,
         mul_left_comm])

private lemma nat_mul_pow_mod {i j m n : ℕ} (hsum : j + i ≤ n) :
  (2 ^ i * (2 ^ j * m)) % 2 ^ n = (2 ^ (j + i) * (m % 2 ^ (n - (j + i)))) % 2 ^ n := by
  rw [←Nat.mod_add_div m (2 ^ (n - (j + i)))]
  ring_nf
  simp [mul_assoc, ←pow_add, add_tsub_cancel_of_le (by linarith : i + j ≤ n)]

private lemma fin_nsmul_val {m : ℕ} (k : ℕ) (a : Fin (2 ^ m)) :
  (k • a).val = (k * a.val) % 2 ^ m := by
  induction k <;> simp [Nat.succ_mul]
  simp_all [add_smul, Fin.val_add]

private lemma subdomain_embed_val {i : ℕ} (hi : i < n) (k : Fin (2 ^ (n - i))) :
  (CosetFftDomainClass.subdomain_embed (n := n) i k).val = 2 ^ i * k.val := by grind +locals

/-- If `x` lies in the `j`th subdomain,
  then `x ^ 2 ^ i` lies in the `(j + i)`th subdomain, provided `j + i ≤ n`. -/
theorem pow_mem_of_mem {i j : ℕ} (hsum : j + i ≤ n) (h : x ∈ subdomain ω j) :
  x ^ 2 ^ i ∈ subdomain ω (j + i) := by
  obtain ⟨k, hk⟩ :
    ∃ k : Fin (2 ^ (n - j)), x =
      (mkSubgroupUnit ω (CosetFftDomainClass.subdomain_embed j k) : F) * (ω 0) ^ 2 ^ j := by
    obtain ⟨k, rfl⟩ := h
    exact ⟨k, mul_comm _ _⟩
  have hx_pow :
    x ^ 2 ^ i =
      ((ω 0) ^ 2 ^ (j + i)) *
        (mkSubgroupUnit ω (2 ^ i • CosetFftDomainClass.subdomain_embed j k) : F) := by
    convert congr_arg (· ^ 2 ^ i) hk using 1
    ring_nf
    simp [←mkSubgroupUnit_pow]
  have h_mod :
    (2 ^ i • CosetFftDomainClass.subdomain_embed j k).val =
      (2 ^ (j + i) *
        (k.val % 2 ^ (n - (j + i)))) % 2 ^ n := by
    have h_mod :
      (2 ^ i • CosetFftDomainClass.subdomain_embed j k).val =
        (2 ^ i *
          (CosetFftDomainClass.subdomain_embed j k).val) % 2 ^ n := by
      convert fin_nsmul_val _ _
    by_cases hj : j < n
    · simp_all only [CosetFftDomainClass.subdomain_embed, ge_iff_le, smul_dite, nsmul_zero]
      split_ifs
      · simp_all only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, mul_zero]
        linarith
      · simp_all only [↓reduceDIte, pow_add, mul_assoc]
        convert nat_mul_pow_mod (show j + i ≤ n from hsum) using 1
        ring_nf
    · have : n = j := by linarith
      aesop
        (add simp [CosetFftDomainClass.subdomain_embed, Nat.mod_one])
  have h_subdomain :
    (CosetFftDomainClass.subdomain_embed
      (n := n) (j + i) ⟨k.val % 2 ^ (n - (j + i)),
    Nat.mod_lt _ (by positivity)⟩).val =
    2 ^ (j + i) * (k.val % 2 ^ (n - (j + i))) := by
    by_cases hi : j + i ≥ n
      <;> aesop
            (add simp [CosetFftDomainClass.subdomain_embed, Nat.mod_one])
            (add safe (by grind))
  generalize_proofs at *
  have h_eq :
    2 ^ i • CosetFftDomainClass.subdomain_embed j k =
      CosetFftDomainClass.subdomain_embed
        (j + i) ⟨k.val % 2 ^ (n - (j + i)), by assumption⟩ := Fin.ext <| by
      simpa [Nat.mod_eq_of_lt (show 2 ^ (j + i) * (k.val % 2 ^ (n - (j + i))) <
        2 ^ n from lt_of_lt_of_le
          (Nat.mul_lt_mul_of_pos_left ‹_› (pow_pos (by decide) _))
          (by rw [← pow_add, Nat.add_sub_of_le hsum]))]
      using h_mod.trans <| h_subdomain.symm ▸
        Nat.mod_eq_of_lt
          (show 2 ^ (j + i) * (k.val % 2 ^ (n - (j + i))) < 2 ^ n from
            lt_of_lt_of_le
              (Nat.mul_lt_mul_of_pos_left ‹_› (pow_pos (by decide) _))
              (by rw [← pow_add, Nat.add_sub_of_le hsum]))
  generalize_proofs at *
  use Multiplicative.ofAdd ⟨k.val % 2 ^ (n - (j + i)), by assumption⟩
  generalize_proofs at *
  convert hx_pow.symm using 1
  exact Eq.symm
    (Mathlib.Tactic.CancelDenoms.derive_trans₂
      rfl (congrArg Units.val (congrArg (mkSubgroupUnit ω) h_eq)) rfl)

/-- If `x` lies in the original domain, then `x ^ 2 ^ i` lies in the `i`th subdomain. -/
lemma pow_mem_subdomain_of_mem_subdomain_0 {i : ℕ} (hi : i ≤ n)
  (h : x ∈ subdomain ω 0) :
  x ^ 2 ^ i ∈ subdomain ω i := by
  have key := pow_mem_of_mem (i := i) (j := 0) (h := h) (by omega)
  rw [mem_subdomain_of_eq_vals (j := 0 + i) (by simp)]
  exact key

/-- `toFinset`-version of `pow_mem_subdomain_of_mem_subdomain_0`. -/
lemma pow_mem_subdomain_of_mem_subdomain_0_toFinset [DecidableEq F] {i : ℕ} (hi : i ≤ n)
  (h : x ∈ (subdomain ω 0).toFinset) :
  x ^ 2 ^ i ∈ (subdomain ω i).toFinset := by
  rw [mem_toFinset_iff_mem]
  exact pow_mem_subdomain_of_mem_subdomain_0 hi (by simpa using h)

private lemma subdomain_embed_of_le (i j : ℕ) (h : j ≤ i)
  (k : Fin (2 ^ (n - i))) :
  ∃ (l : Fin (2 ^ (n - j))),
    CosetFftDomainClass.subdomain_embed i k = CosetFftDomainClass.subdomain_embed j l := by
  by_cases hi : n ≤ i
  · exact ⟨0, by simp [CosetFftDomainClass.subdomain_embed, hi]⟩
  · refine ⟨⟨2 ^ (i - j) * k.val, ?_⟩, ?_⟩
    · calc 2 ^ (i - j) * k.val < 2 ^ (i - j) * 2 ^ (n - i) := by
            apply Nat.mul_lt_mul_of_pos_left k.isLt (by positivity)
          _ = 2 ^ (n - j) := by
            rw [←pow_add, ←Nat.sub_add_comm h, Nat.add_sub_of_le (by omega)]
    · have : ¬n ≤ j := by omega
      simp only [CosetFftDomainClass.subdomain_embed, ge_iff_le, hi, ↓reduceDIte, this, Fin.ext_iff]
      rw [←mul_assoc, ←pow_add, Nat.add_sub_of_le h]

/-- If `j ≤ i`, then we do not have `x ∈ subdomain ω i → x ∈ subdomain ω j`
  in the general case but rescaling `x` as `ω 0 ^ 2 ^ j * (ω 0)⁻¹ ^ 2 ^ i * x`
  gives us a member of `subdomain ω j`. -/
lemma mem_subdomain_of_le_of_mem_subdomain {i j : ℕ} (h : j ≤ i) (hx : x ∈ subdomain ω i) :
  ω 0 ^ 2 ^ j * (ω 0)⁻¹ ^ 2 ^ i * x ∈ subdomain ω j := by
  rw [mem_def] at hx ⊢
  obtain ⟨k, hx⟩ := hx
  have ⟨l, hl⟩ := CosetFftDomainClass.subdomain_embed_of_le _ _ h (Multiplicative.toAdd k)
  refine ⟨l, ?_⟩
  rw [subdomain_apply, ← hl, ← hx, subdomain_apply]
  have hk : Multiplicative.toAdd k = k := rfl
  rw [hk]
  field_simp
  rw [one_div, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero _ (CosetFftDomainClass.ne_zero ω 0))]

/-- Evaluation in the `i`th subdomain, raised to `2 ^ j`,
  is evaluation in the `(i + j)`th subdomain at the reduced index. -/
private lemma subdomain_eval_pow' {i j : ℕ} (hij : i + j ≤ n)
    (k : Fin (2 ^ (n - i))) :
    ((subdomain ω i) k) ^ (2 ^ j) =
      (subdomain ω (i + j)) ⟨k.val % 2 ^ (n - (i + j)), Nat.mod_lt _ (Nat.two_pow_pos _)⟩ := by
  have h_subdomain_embedding :
    2 ^ j • (CosetFftDomainClass.subdomain_embed (n := n) i k) =
      CosetFftDomainClass.subdomain_embed (n := n) (i + j) ⟨k.val % 2 ^ (n - (i + j)),
    Nat.mod_lt _ (by positivity)⟩ := by
    all_goals generalize_proofs at *
    have h_subdomain_embedding :
      (2 ^ j • (CosetFftDomainClass.subdomain_embed (n := n) i k)).val =
        (2 ^ (i + j) * (k.val % 2 ^ (n - (i + j)))) % 2 ^ n := by
      rw [fin_nsmul_val]
      by_cases hi : i < n
      · simp_all only [CosetFftDomainClass.subdomain_embed, ge_iff_le]
        grind +suggestions
      · simp_all only [not_lt, CosetFftDomainClass.subdomain_embed, ge_iff_le, ↓reduceDIte,
        Fin.coe_ofNat_eq_mod, Nat.zero_mod, mul_zero]
        norm_num [show i = n by linarith, show j = 0 by linarith]
    rw [←Fin.val_inj]
    simp_all only
      [CosetFftDomainClass.subdomain_embed, ge_iff_le, smul_dite, nsmul_zero]
    split_ifs <;> simp_all +decide only [Nat.sub_eq_zero_of_le, pow_zero, Order.lt_one_iff,
      mul_zero, Order.lt_two_iff, pow_pos, Nat.mod_eq_of_lt, Fin.val_eq_zero_iff, dite_eq_left_iff,
      not_le, Fin.coe_ofNat_eq_mod]
    rw [Nat.mod_eq_of_lt]
    exact lt_of_lt_of_le
      (Nat.mul_lt_mul_of_pos_left ‹_› (pow_pos (by decide) _))
      (by rw [←pow_add, Nat.add_sub_of_le (by linarith)])
  rw [subdomain_apply, subdomain_apply, mul_pow, mkSubgroupUnit_pow,
    h_subdomain_embedding]
  congr 1
  rw [← pow_mul, ← pow_add]

private lemma card_fin_filter_mod_eq {a j : ℕ} (hj : j ≤ a) (c : ℕ) (hc : c < 2 ^ (a - j)) :
  (Finset.univ.filter (fun k : Fin (2 ^ a) => k.val % 2 ^ (a - j) = c)).card = 2 ^ j := by
  have h_bijection :
    Finset.filter (fun k : ℕ ↦ k % 2 ^ (a - j) = c) (Finset.range (2 ^ a)) =
      Finset.image (fun m ↦ c + m * 2 ^ (a - j)) (Finset.range (2 ^ j)) := by
    ext x
    constructor
    · simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, and_imp] at *
      exact fun hx hx' => ⟨x / 2 ^ ( a - j),
        by nlinarith [Nat.mod_add_div x (2 ^ (a - j)),
          pow_pos (zero_lt_two' ℕ) j, pow_pos (zero_lt_two' ℕ) (a - j),
          show 2 ^ a = 2 ^ (a - j) * 2 ^ j by
            rw [← pow_add, Nat.sub_add_cancel hj]], by linarith [Nat.mod_add_div x (2 ^ (a - j))]⟩
    · simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, forall_exists_index,
      and_imp] at *
      rintro k hk rfl
      refine ⟨?_, ?_⟩
      · rw [←Nat.sub_add_cancel hj] at *
        simp_all only [le_add_iff_nonneg_left, zero_le, add_tsub_cancel_right, pow_add]
        nlinarith
      · rw [←Nat.sub_add_cancel hj] at *
        simp_all +decide only [le_add_iff_nonneg_left, zero_le, add_tsub_cancel_right,
          Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt hc
  convert congr_arg Finset.card h_bijection using 1
  · rw [Finset.card_filter, Finset.card_filter]
    rw [Finset.sum_range]
  · rw [Finset.card_image_of_injective] <;> norm_num [Function.Injective, hc.ne']

/-- If `x` lies in the `(i + j)`th subdomain,
  then it has exactly `2 ^ j` preimages under `y ↦ y ^ 2 ^ j` from the `i`th subdomain. -/
lemma card_block_of_mem_subdomain [DecidableEq F] {i j : ℕ} (hij : i + j ≤ n)
  (h : x ∈ subdomain ω (i + j)) :
  Finset.card (block (subdomain ω i) j x) = 2 ^ j := by
  have hinj : Function.Injective (subdomain ω i) := CosetFftDomainClass.injective _
  unfold block
  obtain ⟨m, hm⟩ := h
  have hinj2 : Function.Injective (subdomain ω (i + j)) := CosetFftDomainClass.injective _
  have hfilter_eq : (Finset.univ.filter (fun k : Fin (2 ^ (n - i)) =>
      ((subdomain ω i) k) ^ 2 ^ j = x)) =
        Finset.univ.filter (fun k : Fin (2 ^ (n - i)) =>
        k.val % 2 ^ (n - (i + j)) = m.val) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [subdomain_eval_pow' hij k, ← hm]
    constructor
    · intro heq
      have := hinj2 heq
      simp only [Fin.ext_iff] at this
      exact this
    · intro heq
      congr 1
      exact Fin.ext heq
  have :
    {y ∈ toFinset (subdomain ω i) | y ^ 2 ^ j = x} =
      Finset.image (subdomain ω i) (Finset.univ.filter (fun k : Fin (2 ^ (n - i)) =>
      ((subdomain ω i) k) ^ 2 ^ j = x)) := by
    ext u
    simp
    aesop (add simp [mem_def])
  rw [this, Finset.card_image_of_injective _ hinj, hfilter_eq]
  simp only [show n - (i + j) = n - i - j from by omega]
  have hsub : n - (i + j) = n - i - j := by omega
  exact card_fin_filter_mod_eq (by omega) m.val (hsub ▸ m.isLt)

set_option linter.unusedDecidableInType false in -- false alert
/-- Every element of the `(i + j)`th subdomain has a `2 ^ j`th root in the `i`th subdomain. -/
lemma root_exists [DecidableEq F] {i j : ℕ} (hij : i + j ≤ n) (h : x ∈ subdomain ω (i + j)) :
  ∃ y ∈ subdomain ω i, y ^ 2 ^ j = x := by
  have h' : Finset.Nonempty {y ∈ (subdomain ω i).toFinset | y ^ 2 ^ j = x} := by
    have := card_block_of_mem_subdomain hij h
    aesop
      (add simp [block])
      (add unsafe (by rw [←Finset.card_ne_zero]))
  simpa [Finset.Nonempty] using h'

set_option linter.unusedDecidableInType false in -- false alert
/-- Any square root of an element of the `(i + 1)`th subdomain lies in the `i`th subdomain. -/
lemma sq_root_mem_subdomain [DecidableEq F] {i : ℕ} (hi : i < n) {y : F}
  (hx : x ∈ subdomain ω (i + 1))
  (hy : y ^ 2 = x) :
  y ∈ subdomain ω i := by
  have : NeZero (n - i) := ⟨by omega⟩
  obtain ⟨y', hy'_mem, hy'_pow⟩ := root_exists (by omega) hx
  rw [pow_one] at hy'_pow
  have hsq : y ^ 2 = y' ^ 2 := by rw [hy, hy'_pow]
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with rfl | rfl
  · exact hy'_mem
  · simpa using hy'_mem

/-- The square roots of `x` inside the `i`th subdomain are exactly `y` and `-y`,
  for any square root `y` of `x`. -/
lemma square_roots_explicit [DecidableEq F] {i : ℕ} (hi : i < n) {y : F}
  (hx : x ∈ subdomain ω (i + 1)) (hy : y ^ 2 = x) :
  {y ∈ (subdomain ω i).toFinset | y ^ 2 = x} = {y, -y} := by
  have : NeZero (n - i) := ⟨by omega⟩
  apply Finset.Subset.antisymm
  · intro z hz
    simp_all only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    exact eq_or_eq_neg_of_sq_eq_sq _ _ <| by rw [hz.2, hy]
  · have hy_mem : y ∈ subdomain ω i := sq_root_mem_subdomain hi hx hy
    simp_all [Finset.subset_iff]

lemma card_block_of_mem_subdomain' [DecidableEq F] {k : ℕ} (hk : k ≤ n) (hx : x ∈ subdomain ω k) :
  Finset.card (block ω k x) = 2 ^ k := by
  have h := card_block_of_mem_subdomain (ω := ω)
          (j := k) (i := 0) (x := x)
          (by simp [hk])
          (by aesop (add simp [mem_subdomain_of_eq_vals]))
  conv_rhs =>
    rw [←h]
  apply congrArg
  aesop

/-- The generalized modular reduction map from `Fin (2^n)` to `Fin (2^(n-i))`,
sending `u` to `u % 2^(n-i)`. Can be used to compute indices of powers of subdomain memebers. -/
def sqFoldMapGen {i : ℕ} (u : Fin (2 ^ n)) : Fin (2 ^ (n - i)) :=
  ⟨u.val % 2 ^ (n - i), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

private lemma two_pow_mul_mod_two_pow (i n v : ℕ) (h : i ≤ n) :
  2 ^ i * v % 2 ^ n = 2 ^ i * (v % 2 ^ (n - i)) := by
  conv_lhs => rw [show (2 : ℕ) ^ n = 2 ^ i * 2 ^ (n - i) by
    rw [←pow_add, Nat.add_sub_of_le h]]
  exact Nat.mul_mod_mul_left _ _ _

/-- Multiplying an index of the ambient domain by `2 ^ i` is the same as embedding
  its `sqFoldMapGen`-reduction back from the `i`th subdomain. -/
private lemma nsmul_eq_subdomain_embed_sqFoldMapGen {i : ℕ} (u : Fin (2 ^ n)) :
  2 ^ i • u = CosetFftDomainClass.subdomain_embed i (sqFoldMapGen (i := i) u) := by
  rw [←Fin.val_inj, fin_nsmul_val]
  by_cases hi : n ≤ i
  · obtain ⟨c, hc⟩ : (2 : ℕ) ^ n ∣ 2 ^ i := pow_dvd_pow 2 hi
    aesop
      (add simp [CosetFftDomainClass.subdomain_embed, mul_assoc, Nat.mul_mod_right])
  · rw [subdomain_embed_val (by omega)]
    exact two_pow_mul_mod_two_pow i n u.val (by omega)

/-- The `2 ^ i`th power of a point of the domain is the point of the `i`th subdomain
  indexed by the `sqFoldMapGen`-reduction of its index. -/
@[simp]
lemma pow_eq_subdomain_sqFoldMapGen {i : ℕ} (u : Fin (2 ^ n)) :
  subdomain ω i (sqFoldMapGen (i := i) u) = ω u ^ 2 ^ i := by
  have h0 : ω 0 ≠ 0 := CosetFftDomainClass.ne_zero ω 0
  have hu : ω u = ω 0 * (mkSubgroupUnit ω u : F) := by
    rw [show ω u = ω 0 * ((ω 0)⁻¹ * ω u) by field_simp]
    rfl
  rw [hu, mul_pow, mkSubgroupUnit_pow, nsmul_eq_subdomain_embed_sqFoldMapGen]
  rfl

/-- `ReedSolomon.evalOnPoints` related on the domain and a subdomain. -/
lemma evalOnPoints_pow_of_two_eq_evalOnPoints_subdomain
  [NeZero n] {p : Polynomial F} {i : ℕ} :
  ReedSolomon.evalOnPoints (ω : Fin (2 ^ n) ↪ F) (p.comp (Polynomial.X ^ (2 ^ i))) =
    (ReedSolomon.evalOnPoints (subdomain ω i : Fin (2 ^ (n - i)) ↪ F) p) ∘
      sqFoldMapGen := by
  funext u
  simp only [ReedSolomon.evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
    Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
  exact congrArg (fun z => Polynomial.eval z p) (pow_eq_subdomain_sqFoldMapGen (ω := ω) u).symm

/-- A particularly useful special case of `evalOnPoints_pow_of_two_eq_evalOnPoints_subdomain`
  when `i = 1`. -/
lemma evalOnPoints_sq_eq_evalOnPoints_subdomain [NeZero n] {p : Polynomial F} :
  ReedSolomon.evalOnPoints (ω : Fin (2 ^ n) ↪ F) (p.comp (Polynomial.X ^ 2)) =
    (ReedSolomon.evalOnPoints (subdomain ω 1 : Fin (2 ^ (n - 1)) ↪ F) p) ∘
      sqFoldMapGen := by
  rw [show Polynomial.X ^ 2 = Polynomial.X ^ (2 ^ 1) by rfl,
      evalOnPoints_pow_of_two_eq_evalOnPoints_subdomain]

/-- Powers of domain values in terms of subdomain values. -/
lemma subdomain_sqFoldMapGen_eq_pow_domain [NeZero n] {i : ℕ} {j : Fin (2 ^ n)} :
  subdomain ω i (sqFoldMapGen j) = ω j ^ 2 ^ i := by
  have := @evalOnPoints_pow_of_two_eq_evalOnPoints_subdomain
  specialize @this F _ n D _ _ ω _ (Polynomial.X) i
  simp_all [funext_iff, ReedSolomon.evalOnPoints]

/-- `sqFoldMapGen j` equals `sqFoldMapGen j'`
  if `ω j ^ 2 ^ j` equals `ω j ^ 2 ^ j'`. -/
lemma sqFoldMapGen_eq_sqFoldMapGen_of_pow_apply_eq_pow_apply [NeZero n] {i : ℕ} {j j' : Fin (2 ^ n)}
  (h : ω j ^ 2 ^ i = ω j' ^ 2 ^ i) :
  sqFoldMapGen (i := i) j = sqFoldMapGen j' :=
  CosetFftDomainClass.injective (subdomain ω i) <| by simp_all

private lemma subdomain_embed_comp {k : ℕ} (hk : k + 1 ≤ n)
    (a : Fin (2 ^ (n - k - 1)))
    (i : Fin (2 ^ (n - (k + 1)))) (hai : (a : ℕ) = (i : ℕ)) :
    CosetFftDomainClass.subdomain_embed (n := n) k
        (CosetFftDomainClass.subdomain_embed (n := n - k) 1 a) =
        CosetFftDomainClass.subdomain_embed (n := n) (k + 1) i := by
  ext
  by_cases hk1 : k + 1 = n
  · have hnk : n - k = 1 := by omega
    simp only [CosetFftDomainClass.subdomain_embed, hnk, ge_iff_le,
      show ¬n ≤ k by omega, show n ≤ k + 1 by omega, le_refl,
      ↓reduceDIte, Fin.val_zero, mul_zero]
  · have hk1' : k + 1 < n := by omega
    simp only [CosetFftDomainClass.subdomain_embed, ge_iff_le,
      show ¬n ≤ k by omega, show ¬n ≤ k + 1 by omega, show ¬n - k ≤ 1 by omega,
      ↓reduceDIte, Fin.val_mk, pow_one]
    rw [hai, pow_succ]
    ring

/-- Composing the `k`th subdomain with one more folding step gives the `(k+1)`th subdomain
  (pointwise, under the index identification `n - k - 1 = n - (k + 1)`). -/
lemma subdomain_comp
  {k j : ℕ} (hk : k + j ≤ n)
  {a : Fin (2 ^ (n - k - j))} {i : Fin (2 ^ (n - (k + j)))}
  (hai : a.val = i.val) :
  subdomain (subdomain ω k) j a = subdomain ω (k + j) i := by
  by_cases h : n ≤ k <;> by_cases h' : n - k ≤ j
  · have hk : k = n := by omega
    have hj : j = 0 := by omega
    simp_all [subdomain_apply, mkSubgroupUnit, CosetFftDomainClass.subdomain_embed]
  · simp_all
  · have : n = k + j := by omega
    simp_all [subdomain_apply, mkSubgroupUnit, CosetFftDomainClass.subdomain_embed,
      pow_add, pow_mul]
  · aesop
      (add simp [subdomain_apply, mkSubgroupUnit, CosetFftDomainClass.subdomain_embed])
      (add unsafe (by ring_nf))
      (add safe [(by omega), (by grind)])

@[simp, grind =]
theorem mem_subdomain_comp_iff_mem
  {k j : ℕ} (hk : k + j ≤ n) {x : F} :
  x ∈ subdomain (subdomain ω k) j ↔ x ∈ subdomain ω (k + j) := by
  constructor <;> rintro ⟨i, hi⟩
  · have := subdomain_comp (ω := ω) (a := i) (i := ⟨i.val, by grind⟩)
    aesop (add simp [mem_def])
  · have := subdomain_comp (ω := ω) (a := ⟨i.val, by grind⟩) (i := i)
    aesop (add simp [mem_def])

end CosetFftDomainClass

namespace CosetFftDomain

variable [DecidableEq F]

/-- Concrete notation for taking the `i`th subdomain of a smooth coset FFT domain. -/
abbrev subdomain {n : ℕ} (ω : SmoothCosetFftDomain n F) (i : ℕ) :
  SmoothCosetFftDomain (n - i) F := CosetFftDomainClass.subdomain ω i

omit [DecidableEq F] in
/-- The zeroth subdomain of a `SmoothCosetFftDomain`
  is itself on the nose. -/
@[simp]
lemma subdomain_zero_eq_self {n : ℕ} {ω : SmoothCosetFftDomain n F} :
  ω.subdomain 0 = ω := by
  apply DFunLike.coe_injective
  funext i
  exact CosetFftDomainClass.subdomain_0_apply i

omit [DecidableEq F] in
lemma subdomain_subdomain_one {n k : ℕ} (hkn : k < n)
  {ω : SmoothCosetFftDomain n F} :
    (ω.subdomain k).subdomain 1 = ω.subdomain (k + 1) := by
  ext ⟨i, hi⟩
  rw [CosetFftDomainClass.subdomain_comp (i := ⟨i, by omega⟩)] <;> grind

/-- Search through a smooth coset FFT domain for an element whose `2 ^ i`th power is `x`,
  using `fuel` as the remaining search bound. -/
def twoNthRootAux (n i : ℕ) (ω : SmoothCosetFftDomain n F) (x : F) (fuel : ℕ) : ω :=
  match fuel with
  | 0 => default
  | fuel + 1 =>
    if h : fuel < 2 ^ n then
      if (ω ⟨fuel, h⟩) ^ 2 ^ i = x then ⟨ω ⟨fuel, h⟩, by simp⟩ else twoNthRootAux n i ω x fuel
    else default

/-- Finds a `2 ^ n`th root of `x`. -/
def twoNthRoot {n i : ℕ} {ω : SmoothCosetFftDomain n F} (x : ω.subdomain i) : ω :=
  twoNthRootAux n i ω x.1 (2 ^ n)

private lemma twoNthRootAux_correct {n i : ℕ} {ω : SmoothCosetFftDomain n F}
  (x : F) (fuel : ℕ) (hfuel : fuel ≤ 2 ^ n)
  (hexists : ∃ j : Fin (2 ^ n), j.val < fuel ∧ (ω j) ^ 2 ^ i = x) :
  (twoNthRootAux n i ω x fuel).val ^ 2 ^ i = x := by
  obtain ⟨j, hj₁, hj₂⟩ := hexists
  induction fuel generalizing j with
  | zero => contradiction
  | succ fuel ih =>
    aesop
      (add simp [twoNthRootAux])
      (add safe (by grind))

open CosetFftDomainClass

/-- The value returned by `twoNthRoot` is a `2 ^ i`th root of its input. -/
lemma twoNthRoot_correct {n i : ℕ} {ω : SmoothCosetFftDomain n F}
  (hi : i ≤ n)
  {x : ω.subdomain i} :
  (twoNthRoot x).val ^ 2 ^ i = x := by
  unfold twoNthRoot
  have hx_mem : x.val ∈ ω.subdomain (0 + i) := by
    rw [Nat.zero_add, ←mem_toFinset_iff_mem]
    exact x.property
  have hex := root_exists (by omega) hx_mem
  obtain ⟨y, hy_mem, hy_pow⟩ := hex
  rw [mem_subdomain_0_iff_mem, mem_def] at hy_mem
  obtain ⟨j, rfl⟩ := hy_mem
  exact twoNthRootAux_correct _ _ le_rfl ⟨j, j.isLt, hy_pow⟩

/-- Specialized correctness statement for square roots from the first subdomain. -/
@[simp]
lemma twoNthRoot_correct_one {n : ℕ} {ω : SmoothCosetFftDomain n F}
  [nz : NeZero n]
  {x : ω.subdomain 1} :
  (twoNthRoot x).val ^ 2 = x := by
  have hi : 1 ≤ n := by
    have hn : n ≠ 0 := NeZero.ne _
    omega
  conv_lhs =>
    rhs
    rw [←pow_one 2]
  rw [twoNthRoot_correct hi]

end CosetFftDomain

end Domain
