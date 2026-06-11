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

variable {F : Type} [Field F] [DecidableEq F]

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

omit [DecidableEq F] in
/-- Membership in subdomains is invariant under equal subdomain indices. -/
lemma mem_subdomain_of_eq_vals
  {i j : ℕ}
  (hij : i = j) :
  x ∈ subdomain ω i ↔ x ∈ subdomain ω j := by rw [hij]

omit [DecidableEq F] in
/-- The coset generator of the `i`th subdomain is `ω 0 ^ 2 ^ i`. -/
@[simp]
lemma subdomain_generator_pow_generator (i : ℕ) :
  (subdomain ω i).cosetGenerator = ω 0 ^ 2 ^ i := rfl

omit [DecidableEq F] in
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

omit [DecidableEq F] in
/-- The `n`th subdomain consists exactly of the single element `ω 0 ^ 2 ^ n`. -/
lemma mem_subdomain_n_iff_eq_pow_generator :
  x ∈ subdomain ω n ↔ x = ω 0 ^ 2 ^ n := by
  aesop
    (add simp [subdomain
    , CosetFftDomainClass.subdomain_embed
    , mkSubgroupUnit
    , mem_def
    , CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])

omit [DecidableEq F] in
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

omit [DecidableEq F] in
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

omit [DecidableEq F] in
/-- If `x` lies in the original domain, then `x ^ 2 ^ i` lies in the `i`th subdomain. -/
lemma pow_mem_subdomain_of_mem_subdomain_0 {i : ℕ} (hi : i ≤ n)
  (h : x ∈ subdomain ω 0) :
  x ^ 2 ^ i ∈ subdomain ω i := by
  have key := pow_mem_of_mem (i := i) (j := 0) (h := h) (by omega)
  rw [mem_subdomain_of_eq_vals (j := 0 + i) (by simp)]
  exact key

/-- `toFinset`-version of `pow_mem_subdomain_of_mem_subdomain_0`. -/
lemma pow_mem_subdomain_of_mem_subdomain_0_toFinset {i : ℕ} (hi : i ≤ n)
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

omit [DecidableEq F] in
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

omit [DecidableEq F] in
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
lemma card_roots {i j : ℕ} (hij : i + j ≤ n) (h : x ∈ subdomain ω (i + j)) :
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
lemma root_exists {i j : ℕ} (hij : i + j ≤ n) (h : x ∈ subdomain ω (i + j)) :
  ∃ y ∈ subdomain ω i, y ^ (2 ^ j) = x := by
  have h' : Finset.Nonempty {y ∈ (subdomain ω i).toFinset | y ^ 2 ^ j = x} := by
    have := card_roots hij h
    aesop (add unsafe (by rw [←Finset.card_ne_zero]))
  simpa [Finset.Nonempty] using h'

set_option linter.unusedDecidableInType false in -- false alert
/-- Any square root of an element of the `(i + 1)`th subdomain lies in the `i`th subdomain. -/
lemma sq_root_mem_subdomain {i : ℕ} (hi : i < n) {y : F}
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
lemma square_roots_explicit {i : ℕ} (hi : i < n) {y : F}
  (hx : x ∈ subdomain ω (i + 1)) (hy : y ^ 2 = x) :
  {y ∈ (subdomain ω i).toFinset | y ^ 2 = x} = {y, -y} := by
  have : NeZero (n - i) := ⟨by omega⟩
  apply Finset.Subset.antisymm
  · intro z hz
    simp_all only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    exact eq_or_eq_neg_of_sq_eq_sq _ _ <| by rw [hz.2, hy]
  · have hy_mem : y ∈ subdomain ω i := sq_root_mem_subdomain hi hx hy
    simp_all [Finset.subset_iff]

end CosetFftDomainClass

namespace CosetFftDomain

/-- Concrete notation for taking the `i`th subdomain of a smooth coset FFT domain. -/
abbrev subdomain {n : ℕ} (ω : SmoothCosetFftDomain n F) (i : ℕ) :
  SmoothCosetFftDomain (n - i) F := CosetFftDomainClass.subdomain ω i

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
