/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
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
- `card_roots`:
  Exact cardinality of fibers of powering maps.
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

/-- Membership to the `0`th subdomain is
  the same as membership to the original coset FFT domain. -/
@[simp]
lemma mem_subdomain_0_iff_mem :
  x ∈ subdomain ω 0 ↔ x ∈ ω := by
  by_cases hn : n = 0
    <;> aesop
          (add simp
            [subdomain,
             CosetFftDomainClass.subdomain_embed,
             mkSubgroupUnit,
             mem_def,
             CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])

/-- The `n`th subdomain consists exactly of the single element `ω 0 ^ 2 ^ n`. -/
lemma mem_subdomain_n_iff_eq_pow_generator :
  x ∈ subdomain ω n ↔ x = ω 0 ^ 2 ^ n := by
  aesop
    (add simp [subdomain
    , CosetFftDomainClass.subdomain_embed
    , mkSubgroupUnit
    , mem_def
    , CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])

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
  x ^ (2 ^ i) ∈ (subdomain ω i).toFinset := by
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
  simp only [subdomain, inv_pow, mem_def] at hx
  obtain ⟨k, hx⟩ := hx
  simp only [mkSubgroupUnit, CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain,
    MonoidHom.coe_mk, OneHom.coe_mk] at hx
  have ⟨l, hl⟩ := CosetFftDomainClass.subdomain_embed_of_le _ _ h (Multiplicative.toAdd k)
  rw [hl] at hx
  rw [←hx, ←mul_assoc, mul_assoc (ω 0 ^ 2 ^ j)]
  aesop (add simp [CosetFftDomain.mem_iff_exists_mul])

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
  generalize_proofs at *;
  unfold subdomain
  simp_all only [inv_pow, pow_add]
  convert congr_arg
    (fun x : Fin (2 ^ n) => mkSubgroupUnit ω x)
    h_subdomain_embedding using 1
  simp only [CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain, MonoidHom.coe_mk,
    OneHom.coe_mk, mul_pow, mkSubgroupUnit_pow, pow_mul, mul_eq_mul_left_iff, ne_eq,
    Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true, pow_eq_zero_iff, ne_zero,
    or_false, ← Units.val_inj]
  convert Iff.rfl

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
lemma card_roots [DecidableEq F] {i j : ℕ} (hij : i + j ≤ n) (h : x ∈ subdomain ω (i + j)) :
  Finset.card {y ∈ (subdomain ω i).toFinset | y ^ (2 ^ j) = x} = 2 ^ j := by
  have hinj : Function.Injective (subdomain ω i) := CosetFftDomainClass.injective _
  simp only [CosetFftDomain.toFinset]
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
  ∃ y ∈ subdomain ω i, y ^ (2 ^ j) = x := by
  have h' : Finset.Nonempty {y ∈ (subdomain ω i).toFinset | y ^ 2 ^ j = x} := by
    have := card_roots hij h
    aesop (add unsafe (by rw [←Finset.card_ne_zero]))
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

/-- The generalized modular reduction map from `Fin (2^n)` to `Fin (2^(n-i))`,
sending `u` to `u % 2^(n-i)`. Can be used to compute indices of powers of subdomain memebers. -/
def sqFoldMapGen {i : ℕ} (u : Fin (2 ^ n)) : Fin (2 ^ (n - i)) :=
  ⟨u.val % 2 ^ (n - i), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

omit [DecidableEq F] in
/-- `ReedSolomon.evalOnPoints` related on the domain and a subdomain. -/
lemma evalOnPoints_pow_of_two_eq_evalOnPoints_subdomain
  [NeZero n] {p : Polynomial F} {i : ℕ} :
  ReedSolomon.evalOnPoints (ω : Fin (2 ^ n) ↪ F) (p.comp (Polynomial.X ^ (2 ^ i))) =
    (ReedSolomon.evalOnPoints (subdomain ω i : Fin (2 ^ (n - i)) ↪ F) p) ∘
      sqFoldMapGen := by
  ext u
  simp only [ReedSolomon.evalOnPoints, Function.Embedding.coeFn_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X, subdomain, inv_pow,
    Function.comp_apply]
  congr 1
  -- By definition of exponentiation in the field F, we can rewrite the right-hand side.
  have h_exp :
    ω u ^ (2 ^ i) =
      (ω 0) ^ (2 ^ i - 1) *
        ω (CosetFftDomainClass.subdomain_embed
            i (Fin.mk
                (u.val % 2 ^ (n - i))
                (Nat.mod_lt _ (Nat.two_pow_pos _)))) := by
    have h_exp :
      ∀ i : ℕ, ∀ u : Fin (2 ^ n),
        ω u ^ 2 ^ i = ω 0 ^ (2 ^ i - 1) *
          ω (Fin.mk
              (2 ^ i * u.val % 2 ^ n)
              (Nat.mod_lt _ (Nat.two_pow_pos _))) := by
      intro i u
      induction i generalizing u with
      | zero =>
        simp_all only [pow_zero, pow_one, tsub_self, one_mul]
        norm_num [Nat.mod_eq_of_lt]
      | succ i ih =>
        simp_all only [pow_succ, pow_mul, pow_zero, one_mul]
        have h_exp :
          ω (Fin.mk
              (2 ^ i * u.val % 2 ^ n)
              (Nat.mod_lt _ (Nat.two_pow_pos _))) ^ 2 =
                ω 0 *
                  ω (Fin.mk
                      (2 ^ (i + 1) * u.val % 2 ^ n)
                      (Nat.mod_lt _ (Nat.two_pow_pos _))) := by
          have h_exp : ∀ u v : Fin (2 ^ n), ω u * ω v = ω 0 * ω (u + v) := by
            intro u v
            have := ‹CosetFftDomainClass D (Fin (2 ^ n)) F›.map_add ω u v
            simp_all [mul_comm, mul_left_comm]
          convert h_exp _ _ using 2
          · ring_nf
            rw [sq]
          · congr 1
            norm_num [Fin.add_def, Nat.mod_eq_of_lt]
            ring_nf
        convert congr_arg (· * (ω 0 ^ (2 ^ i - 1)) ^ 2) h_exp using 1
          <;> ring_nf
        rw [show 2 ^ i * 2 - 1 = (2 ^ i - 1) * 2 + 1 by zify; norm_num; ring]
        ring_nf
    by_cases hi : i ≥ n
    · simp_all only [ge_iff_le, CosetFftDomainClass.subdomain_embed, ↓reduceDIte,
      mul_eq_mul_left_iff, pow_eq_zero_iff', ne_zero, ne_eq, false_and, or_false]
      norm_num [Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left (pow_dvd_pow _ hi) _)]
    · convert h_exp i u using 3
      simp only [CosetFftDomainClass.subdomain_embed, ge_iff_le]
      split_ifs
      · simp_all
      · simp_all only [ge_iff_le, not_false_eq_true, Fin.mk.injEq]
        rw [←Nat.mul_mod_mul_left,
            ←pow_add,
            Nat.add_sub_of_le (le_of_not_ge ‹¬n ≤ i›)]
  convert h_exp using 1
  convert congr_arg
    (fun x : Fˣ => x.val)
    (show
      ({ val := ω 0 ^ 2 ^ i, inv := (ω 0 ^ 2 ^ i) ⁻¹, val_inv := _, inv_val := _ } : Fˣ) *
      ({ val := (ω 0) ⁻¹ *
           ω (CosetFftDomainClass.subdomain_embed i ⟨u.val % 2 ^ (n - i),
            Nat.mod_lt _ (Nat.two_pow_pos _)⟩),
         inv := ω 0 *
           (ω (CosetFftDomainClass.subdomain_embed i
              ⟨u.val % 2 ^ (n - i), Nat.mod_lt _ (Nat.two_pow_pos _)⟩)) ⁻¹,
         val_inv := _,
         inv_val := _} : Fˣ) =
          { val := ω 0 ^ (2 ^ i - 1) *
              ω (CosetFftDomainClass.subdomain_embed i ⟨u.val % 2 ^ (n - i),
                  Nat.mod_lt _ (Nat.two_pow_pos _) ⟩),
            inv := _,
            val_inv := _,
            inv_val := _} from ?_) using 1
  · exact (ω 0 ^ (2 ^ i - 1) *
      ω (CosetFftDomainClass.subdomain_embed i ⟨u.val % 2 ^ ( n - i ),
          Nat.mod_lt _ (Nat.two_pow_pos _)⟩))⁻¹
  all_goals norm_num [Units.ext_iff]
  · field_simp
  · field_simp
  · cases k : 2 ^ i <;> simp_all [pow_succ, mul_assoc]

omit [DecidableEq F] in
/-- A particularly useful special case of `evalOnPoints_pow_of_two_eq_evalOnPoints_subdomain`
  when `i = 1`. -/
lemma evalOnPoints_sq_eq_evalOnPoints_subdomain [NeZero n] {p : Polynomial F} :
  ReedSolomon.evalOnPoints (ω : Fin (2 ^ n) ↪ F) (p.comp (Polynomial.X ^ 2)) =
    (ReedSolomon.evalOnPoints (subdomain ω 1 : Fin (2 ^ (n - 1)) ↪ F) p) ∘
      sqFoldMapGen := by
  rw [show Polynomial.X ^ 2 = Polynomial.X ^ (2 ^ 1) by rfl,
      evalOnPoints_pow_of_two_eq_evalOnPoints_subdomain]

omit [DecidableEq F] in
/-- Powers of domain values in terms of subdomain values. -/
lemma subdomain_sqFoldMapGen_eq_pow_domain [NeZero n] {i : ℕ} {j : Fin (2 ^ n)} :
  subdomain ω i (sqFoldMapGen j) = ω j ^ 2 ^ i := by
  have := @evalOnPoints_pow_of_two_eq_evalOnPoints_subdomain
  specialize @this F _ n D _ _ ω _ (Polynomial.X) i
  simp_all [funext_iff, ReedSolomon.evalOnPoints]

omit [DecidableEq F] in
/-- `sqFoldMapGen j` equals `sqFoldMapGen j'`
  if `ω j ^ 2 ^ j` equals `ω j ^ 2 ^ j'`. -/
lemma sqFoldMapGen_eq_sqFoldMapGen_of_pow_apply_eq_pow_apply
  [NeZero n] {i : ℕ} {j j' : Fin (2 ^ n)}
  (h : ω j ^ 2 ^ i = ω j' ^ 2 ^ i) :
  sqFoldMapGen (i := i) j = sqFoldMapGen j' := by
    contrapose! h with h_contra
    have h_key_id :
      ∀ i u, ω u ^ 2 ^ i =
          ω 0 ^ (2 ^ i - 1) *
            ω (Fin.mk (2 ^ i * u.val % 2 ^ n) (Nat.mod_lt _ (Nat.two_pow_pos _))) := by
      intro i u
      induction i generalizing u with
      | zero =>
        simp_all only [ne_eq, pow_zero, pow_one, tsub_self, one_mul]
        norm_num [Nat.mod_eq_of_lt]
      | succ i ih =>
        simp_all only [ne_eq, pow_succ, pow_mul, pow_zero, one_mul]
        have h_sq :
          ∀ u : Fin (2 ^ n), ω u ^ 2 =
            ω 0 * ω (Fin.mk (2 * u.val % 2 ^ n) (Nat.mod_lt _ (Nat.two_pow_pos _))) := by
          intro u
          have := ‹CosetFftDomainClass D (Fin ( 2 ^ n )) F›.map_add ω u u
          simp_all only [mul_assoc, sq]
          simp_all only [Fin.add_def, two_mul, ne_eq, ne_zero, not_false_eq_true,
            mul_inv_cancel_left₀]
        convert congr_arg (· ^ 2) (ih u) using 1 <;> ring_nf
        · convert congr_arg (· ^ 2) (ih u) |> Eq.symm using 1
          · ring_nf
          · norm_num [pow_mul]
        · rw [h_sq]
          ring_nf
          rw [show (2 ^ i * 2 - 1 : ℕ) = (2 ^ i - 1) * 2 + 1
                by zify; norm_num; ring]
          ring_nf
          norm_num [mul_assoc, Nat.mul_mod_mul_right]
    have h_cancel :
      ω (Fin.mk
          (2 ^ i * j.val % 2 ^ n)
          (Nat.mod_lt _ (Nat.two_pow_pos _))) ≠
            ω (Fin.mk
                (2 ^ i * j'.val % 2 ^ n)
                (Nat.mod_lt _ (Nat.two_pow_pos _))) := by
      intro h_eq
      have := (‹CosetFftDomainClass D (Fin (2 ^ n)) F›.injective ω) h_eq
      simp_all only [ne_eq, Fin.ext_iff]
      -- Since $2^i * j \equiv 2^i * j' \pmod{2^n}$,
      -- we can divide both sides by $2^i$ (which is valid since $2^i$ is coprime to $2^n$).
      have h_div : j.val % 2 ^ (n - i) = j'.val % 2 ^ (n - i) := by
        by_cases hi : i ≤ n;
        · have h_div : 2 ^ i * (j.val - j'.val) ≡ 0 [ZMOD 2 ^ n] := by
            exact Int.modEq_zero_iff_dvd.mpr
              ⟨2 ^ i * j / 2 ^ n - 2 ^ i * j' / 2 ^ n,
                by linarith
                      [Int.emod_add_mul_ediv (2 ^ i * j) (2 ^ n),
                       Int.emod_add_mul_ediv (2 ^ i * j') (2 ^ n)]⟩
          have h_div : (j.val - j'.val : ℤ) ≡ 0 [ZMOD 2 ^ (n - i)] := by
            rw [Int.modEq_zero_iff_dvd] at *
            exact Exists.elim h_div fun k hk ↦
              ⟨k, by
                    rw [show ( 2 ^ n : ℤ ) = 2 ^ i * 2 ^ (n - i) by
                      rw [←pow_add, Nat.add_sub_of_le hi]] at hk;
                      nlinarith [pow_pos (zero_lt_two' ℤ) i]⟩
          exact Nat.ModEq.symm
            (Nat.modEq_of_dvd <| by simpa [←Int.natCast_dvd_natCast] using h_div.symm.dvd)
        · grind
      exact h_contra h_div
    simp_all [mul_comm]

omit [DecidableEq F] in
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

omit [DecidableEq F] in
private lemma subdomain_eval (ω : D) (j : ℕ)
    (b : Fin (2 ^ (n - j))) :
    (subdomain ω j) b =
      ω 0 ^ 2 ^ j * ((ω 0)⁻¹ * ω (CosetFftDomainClass.subdomain_embed j b)) := rfl

omit [DecidableEq F] in
/-- Composing the `k`th subdomain with one more folding step gives the `(k+1)`th subdomain
  (pointwise, under the index identification `n - k - 1 = n - (k + 1)`). -/
lemma subdomain_one_comp
    {k : ℕ} (hk : k + 1 ≤ n)
    (a : Fin (2 ^ (n - k - 1))) (i : Fin (2 ^ (n - (k + 1)))) (hai : (a : ℕ) = (i : ℕ)) :
    subdomain (subdomain ω k) 1 a = subdomain ω (k + 1) i := by
  have hw0 : (subdomain ω k) 0 = ω 0 ^ 2 ^ k := by
    rw [subdomain_eval ω k 0, CosetFftDomainClass.subdomain_embed_zero,
        inv_mul_cancel₀ (CosetFftDomainClass.ne_zero ω 0), mul_one]
  have hwe : (subdomain ω k) (CosetFftDomainClass.subdomain_embed 1 a)
      = ω 0 ^ 2 ^ k
          * ((ω 0)⁻¹ * ω (CosetFftDomainClass.subdomain_embed (k + 1) i)) := by
    rw [subdomain_eval ω k (CosetFftDomainClass.subdomain_embed 1 a),
        subdomain_embed_comp hk a i hai]
  rw [subdomain_eval (subdomain ω k) 1 a, hw0, hwe, subdomain_eval ω (k + 1) i]
  have hg0 : ω 0 ≠ 0 := CosetFftDomainClass.ne_zero ω 0
  have hgk : ω 0 ^ 2 ^ k ≠ 0 := pow_ne_zero _ hg0
  rw [show (ω 0 ^ 2 ^ k) ^ 2 ^ 1 = ω 0 ^ 2 ^ (k + 1) from by
        rw [←pow_mul, pow_one, ←pow_succ]]
  field_simp

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
  aesop
    (add simp
      [subdomain,
       CosetFftDomainClass.subdomain,
       CosetFftDomainClass.mkSubgroupUnit,
       CosetFftDomainClass.subdomain_embed])
    (add safe cases Fin)
    (add safe (by grind))
    (add unsafe (by rw [eval_coset_fft_domain_eq_eval_generator_mul_domain]))

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
