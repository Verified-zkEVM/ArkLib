/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Galois.Automorphism
import ArkLib.Data.Lattices.CyclotomicRing.Galois.Order

/-!
# The Galois Group and the Subgroup `H = ⟨σ_{-1}, σ_{4k+1}⟩`

The Galois automorphisms `σ_i` of `R_q = Z_q[X] / (X^{2^α} + 1)` form a group isomorphic to
`(Z / 2^{α+1})ˣ` via `σ_i ∘ σ_j = σ_{ij}` and `σ_1 = id`. Hachi [NOZ26, §3] works with the
subgroup `H := ⟨σ_{-1}, σ_{4k+1}⟩`, whose fixed subring is the subfield `≅ F_{q^k}`.

This file pins the two generators (`σ_{-1}` with exponent `2^{α+1}-1 ≡ -1`, and `σ_{4k+1}`),
records their oddness (so they are genuine automorphisms), and provides the explicit exponent
set `Hexp` enumerating `H` for use by the trace map. The composition law `σ_i ∘ σ_j = σ_{ij}`
(for odd `i, j`) and `σ_1 = id` are proven via the soundness bridge; the order computation
`|⟨4k+1⟩| = d/(2k)` (Hachi [NOZ26, §3, Claim 1] / [LS18, Lem 2.4]) is proven in
`CyclotomicRing/Galois/Order.lean` via 2-adic lifting-the-exponent.

## Main definitions

* `conjExp α` / `genExp k` — the exponents `2^{α+1}-1` (`σ_{-1}`) and `4k+1` (`σ_{4k+1}`).
* `conjAut α` / `genAut α k` — the two generating automorphisms as `RingHom`s.
* `Hexp α k` — the exponent set enumerating `H = ⟨σ_{-1}, σ_{4k+1}⟩`.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements …*][LS18]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

open Polynomial CompPoly Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]

/-! ## Generators of `H` and their exponents -/

/-- The exponent of the conjugation automorphism `σ_{-1}`: `2^{α+1} - 1 ≡ -1 (mod 2^{α+1})`. -/
def conjExp (α : ℕ) : ℕ := 2 ^ (α + 1) - 1

/-- The exponent of the second generator `σ_{4k+1}`. -/
def genExp (k : ℕ) : ℕ := 4 * k + 1

theorem genExp_odd (k : ℕ) : Odd (genExp k) := ⟨2 * k, by unfold genExp; ring⟩

theorem conjExp_odd (α : ℕ) : Odd (conjExp α) := by
  have h : 1 ≤ 2 ^ α := Nat.one_le_two_pow
  refine ⟨2 ^ α - 1, ?_⟩
  unfold conjExp
  rw [pow_succ]; omega

/-- The conjugation automorphism `σ_{-1} : X ↦ X^{-1}`, as a `RingHom`. -/
noncomputable def conjAut (α : ℕ) :
    Rq (powTwoCyclotomic (R := R) α) →+* Rq (powTwoCyclotomic (R := R) α) :=
  galoisRingHom α (conjExp α) (conjExp_odd α)

/-- The second generator `σ_{4k+1}`, as a `RingHom`. -/
noncomputable def genAut (α k : ℕ) :
    Rq (powTwoCyclotomic (R := R) α) →+* Rq (powTwoCyclotomic (R := R) α) :=
  galoisRingHom α (genExp k) (genExp_odd k)

/-! ## Group laws -/

/-- `σ_1 = id`: substituting `X ↦ X^1` is the identity. Proven via the soundness bridge, since
`aeval X` is the identity on `Polynomial R`. -/
theorem galoisAut_one_eq (α : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    galoisAut (powTwoCyclotomic α) 1 a = a := by
  apply Rq.toQuotient_injective (powTwoCyclotomic α)
  rw [galoisAut_toQuotient α 1 odd_one, galoisAutₛ_toQuotient α 1 odd_one, pow_one,
    Polynomial.aeval_X_left_apply, Rq.toQuotient, quotientHom_apply]

/-- Composition law `σ_i ∘ σ_j = σ_{ij}` (for `i, j` odd, so the maps are genuine
automorphisms). Proven on the semantic `aeval` side via the soundness bridge
`galoisAut_toQuotient` and `aeval_X_pow_aeval_X_pow`. -/
theorem galoisAut_comp (α i j : ℕ) (hi : Odd i) (hj : Odd j)
    (a : Rq (powTwoCyclotomic (R := R) α)) :
    galoisAut (powTwoCyclotomic α) i (galoisAut (powTwoCyclotomic α) j a)
      = galoisAut (powTwoCyclotomic α) (i * j) a := by
  apply Rq.toQuotient_injective (powTwoCyclotomic α)
  rw [galoisAut_toQuotient α i hi, galoisAut_toQuotient α j hj,
    galoisAut_toQuotient α (i * j) (hi.mul hj), galoisAutₛ_toQuotient α j hj, galoisAutₛ_mk,
    galoisAutₛ_toQuotient α (i * j) (hi.mul hj), aeval_X_pow_aeval_X_pow]

/-! ## The subgroup `H` as an exponent set -/

/-- The exponent set enumerating `H = ⟨σ_{-1}, σ_{4k+1}⟩` inside `(Z / 2^{α+1})ˣ`:
`{ ±(4k+1)^a mod 2^{α+1} : 0 ≤ a < d/(2k) }`. The trace map sums the automorphisms over this
set. -/
def Hexp (α k : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ α / (2 * k))).biUnion fun a =>
    {(4 * k + 1) ^ a % 2 ^ (α + 1),
      (2 ^ (α + 1) - (4 * k + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)}

/-- `|H| = d/k = 2^α / k` (Hachi [NOZ26, §3], from `|⟨4k+1⟩| = d/(2k)` and the `±` factor).

The hypotheses match Hachi [NOZ26, §3, Claim 1] / [LS18, Lem 2.4]: `k` is a power of two
(`hk2pow`) and divides `d/2`, i.e. `2k ∣ d = 2^α` (`hk`). Both are needed for `4k+1` to have
order exactly `d/(2k)` in `(Z/2^{α+1})ˣ`; the weaker `k ∣ 2^α` (= `k ∣ d`) does not suffice
(e.g. `k = 2^α` gives `2k ∤ d`, so `2^α/(2k)` is not the true order).

Proof: the number-theoretic core `two_pow_dvd_four_pow_sub_one_iff` gives
`2^{α+1} ∣ (4k+1)ⁿ − 1 ↔ 2^{α-κ-1} ∣ n`, from which `a ↦ (4k+1)^a mod 2^{α+1}` is injective on
`range (2^{α-κ-1})` (`four_pow_injOn`). The Finset count then follows: the `±`-reflection is
disjoint (mod-4 parity) and the two halves each have `2^{α-κ-1}` elements, giving
`2·2^{α-κ-1} = 2^α/k`. -/
theorem Hexp_card (α k : ℕ) (hk2pow : ∃ κ, k = 2 ^ κ) (hk : 2 * k ∣ 2 ^ α) :
    (Hexp α k).card = 2 ^ α / k := by
  obtain ⟨κ, rfl⟩ := hk2pow
  have hκ : κ + 1 ≤ α :=
    (Nat.pow_dvd_pow_iff_le_right (by norm_num : (1 : ℕ) < 2)).mp
      (by rw [pow_succ, mul_comm]; exact hk)
  have hm4 : (4 : ℕ) ∣ 2 ^ (α + 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl]; exact pow_dvd_pow 2 (by omega)
  have hm40 : 2 ^ (α + 1) % 4 = 0 := by obtain ⟨c, hc⟩ := hm4; omega
  have hmpos : 0 < 2 ^ (α + 1) := by positivity
  have hp4 : ∀ a, (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) % 4 = 1 := fun a => by
    rw [Nat.mod_mod_of_dvd _ hm4, Nat.pow_mod]
    norm_num [show (4 * 2 ^ κ + 1) % 4 = 1 from by omega]
  have hplt : ∀ a, (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) < 2 ^ (α + 1) := fun a => Nat.mod_lt _ hmpos
  have hrange : 2 ^ α / (2 * 2 ^ κ) = 2 ^ (α - κ - 1) := by
    rw [show 2 * 2 ^ κ = 2 ^ (κ + 1) from by rw [pow_succ]; ring, Nat.pow_div hκ (by norm_num),
      Nat.sub_sub]
  have hpinj : Set.InjOn (fun a => (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1))
      ↑(Finset.range (2 ^ (α - κ - 1))) := four_pow_injOn κ α hκ
  have hqeq : ∀ a, (2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)
      = 2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) := fun a =>
    Nat.mod_eq_of_lt (by have := hplt a; have := hp4 a; omega)
  rw [Hexp, hrange, Finset.card_biUnion]
  · have hc2 : ∀ a ∈ Finset.range (2 ^ (α - κ - 1)),
        ({(4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1),
          (2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)} : Finset ℕ).card = 2 :=
      fun a _ => Finset.card_pair (by rw [hqeq a]; have := hp4 a; have := hplt a; omega)
    have hmul : 2 ^ (α - κ - 1) * 2 = 2 ^ (α - κ) := by
      rw [← pow_succ, show α - κ - 1 + 1 = α - κ from by omega]
    rw [Finset.sum_congr rfl hc2, Finset.sum_const, Finset.card_range, smul_eq_mul, hmul,
      Nat.pow_div (by omega) (by norm_num)]
  · intro a ha b hb hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    have hla := hplt a; have hlb := hplt b; have h1a := hp4 a; have h1b := hp4 b
    have hpab : (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) ≠ (4 * 2 ^ κ + 1) ^ b % 2 ^ (α + 1) := fun h =>
      hab (hpinj ha hb h)
    intro x hx hx'
    rw [hqeq a] at hx; rw [hqeq b] at hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with h' | h' <;> omega

/-- Every exponent enumerated by `Hexp` is odd (so the corresponding `σ_i` is a genuine
automorphism). The base `4k+1` is odd; reduction mod the even conductor `2^{α+1}` and the
`(m − ·)` reflection both preserve oddness. -/
theorem Hexp_odd_mem (α k : ℕ) : ∀ i ∈ Hexp α k, Odd i := by
  intro i hi
  have hm : (2 : ℕ) ∣ 2 ^ (α + 1) := dvd_pow_self 2 (Nat.succ_ne_zero α)
  have hmpos : 0 < 2 ^ (α + 1) := pow_pos (by norm_num) _
  have hmeven : Even (2 ^ (α + 1)) := ⟨2 ^ α, by rw [pow_succ]; ring⟩
  have hbase : Odd (4 * k + 1) := ⟨2 * k, by ring⟩
  rw [Hexp, Finset.mem_biUnion] at hi
  obtain ⟨a, _, hi⟩ := hi
  rw [Finset.mem_insert, Finset.mem_singleton] at hi
  have hxodd : Odd ((4 * k + 1) ^ a % 2 ^ (α + 1)) := by
    rw [Nat.odd_iff, Nat.mod_mod_of_dvd _ hm, ← Nat.odd_iff]; exact hbase.pow
  rcases hi with h | h
  · exact h ▸ hxodd
  · rw [h, Nat.odd_iff, Nat.mod_mod_of_dvd _ hm, ← Nat.odd_iff]
    exact Nat.Even.sub_odd (Nat.le_of_lt (Nat.mod_lt _ hmpos)) hmeven hxodd

/-- Multiplication by a generator permutes `Hexp` (as a `Finset`), i.e. the image under
`i ↦ (g·i) mod 2^{α+1}` is `Hexp` itself, for `g` a generator of `H = ⟨σ_{-1}, σ_{4k+1}⟩`.
This is the group-translation fact `g • H = H` transported through the `Hexp ↔ H` bridge.

Proof: the number-theoretic input (`two_pow_dvd_four_pow_sub_one_iff` ⟹
`(4k+1)^{2^{α-κ-1}} ≡ 1` and injectivity of the power enumeration) drives the Finset
permutation. For `g = 4k+1`, multiplication cyclically shifts the `(4k+1)^a` enumeration
(`a ↦ a+1 mod 2^{α-κ-1}`) and the `±` part in tandem; for `g = conjExp` it swaps the two halves.
Closed via injectivity + a subset/cardinality argument. -/
theorem Hexp_generator_smul (α k g : ℕ) (hk2pow : ∃ κ, k = 2 ^ κ) (hk : 2 * k ∣ 2 ^ α)
    (hg : g = conjExp α ∨ g = genExp k) :
    (Hexp α k).image (fun i => (g * i) % 2 ^ (α + 1)) = Hexp α k := by
  obtain ⟨κ, rfl⟩ := hk2pow
  have hκ : κ + 1 ≤ α := (Nat.pow_dvd_pow_iff_le_right (by norm_num : (1 : ℕ) < 2)).mp
    (by rw [pow_succ, mul_comm]; exact hk)
  have hmpos : 0 < 2 ^ (α + 1) := by positivity
  have hopos : 0 < 2 ^ (α - κ - 1) := by positivity
  have hm2 : 2 ≤ 2 ^ (α + 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (α + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrange : 2 ^ α / (2 * 2 ^ κ) = 2 ^ (α - κ - 1) := by
    rw [show 2 * 2 ^ κ = 2 ^ (κ + 1) from by rw [pow_succ]; ring, Nat.pow_div hκ (by norm_num),
      Nat.sub_sub]
  have hplt : ∀ a, (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) < 2 ^ (α + 1) := fun a => Nat.mod_lt _ hmpos
  have hcop1 : Nat.Coprime (4 * 2 ^ κ + 1) (2 ^ (α + 1)) :=
    (Nat.coprime_two_right.mpr ⟨2 * 2 ^ κ, by ring⟩).pow_right _
  have hp1 : ∀ a, 1 ≤ (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) := fun a => by
    rcases Nat.eq_zero_or_pos ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) with h | h
    · have hco : Nat.Coprime (2 ^ (α + 1)) ((4 * 2 ^ κ + 1) ^ a) := (hcop1.pow_left _).symm
      rw [Nat.Coprime, Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero h)] at hco; omega
    · exact h
  -- general modular negation: `c·y ≡ -(c·z)` when `y + z = 2^{α+1}`
  have hgen_neg : ∀ c y z : ℕ, y + z = 2 ^ (α + 1) →
      (c * y) % 2 ^ (α + 1) = (2 ^ (α + 1) - (c * z) % 2 ^ (α + 1)) % 2 ^ (α + 1) := by
    intro c y z hyz
    have h1 : c * y + (c * z) % 2 ^ (α + 1) ≡ 0 [MOD 2 ^ (α + 1)] :=
      calc c * y + (c * z) % 2 ^ (α + 1) ≡ c * y + c * z [MOD 2 ^ (α + 1)] :=
            Nat.ModEq.add_left _ (Nat.mod_modEq _ _)
        _ = c * 2 ^ (α + 1) := by rw [← Nat.mul_add, hyz]
        _ ≡ 0 [MOD 2 ^ (α + 1)] := (Nat.modEq_zero_iff_dvd).mpr ⟨c, by ring⟩
    have h2 : (2 ^ (α + 1) - (c * z) % 2 ^ (α + 1)) % 2 ^ (α + 1) + (c * z) % 2 ^ (α + 1)
        ≡ 0 [MOD 2 ^ (α + 1)] :=
      calc (2 ^ (α + 1) - (c * z) % 2 ^ (α + 1)) % 2 ^ (α + 1) + (c * z) % 2 ^ (α + 1)
            ≡ (2 ^ (α + 1) - (c * z) % 2 ^ (α + 1)) + (c * z) % 2 ^ (α + 1) [MOD 2 ^ (α + 1)] :=
            Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
        _ = 2 ^ (α + 1) := Nat.sub_add_cancel (Nat.le_of_lt (Nat.mod_lt _ hmpos))
        _ ≡ 0 [MOD 2 ^ (α + 1)] := (Nat.modEq_zero_iff_dvd).mpr (dvd_refl _)
    have key := Nat.ModEq.add_right_cancel' ((c * z) % 2 ^ (α + 1)) (h1.trans h2.symm)
    rw [Nat.ModEq, Nat.mod_mod] at key; exact key
  -- `genExp · pₐ ≡ p_{(a+1) mod o}` (cyclic shift via the order)
  have hmulP : ∀ a, (genExp (2 ^ κ) * ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1))) % 2 ^ (α + 1)
      = (4 * 2 ^ κ + 1) ^ ((a + 1) % 2 ^ (α - κ - 1)) % 2 ^ (α + 1) := fun a => by
    change (4 * 2 ^ κ + 1) * ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1) = _
    calc (4 * 2 ^ κ + 1) * ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1))
          ≡ (4 * 2 ^ κ + 1) * (4 * 2 ^ κ + 1) ^ a [MOD 2 ^ (α + 1)] :=
          Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
      _ = (4 * 2 ^ κ + 1) ^ (a + 1) := (pow_succ' _ _).symm
      _ ≡ (4 * 2 ^ κ + 1) ^ ((a + 1) % 2 ^ (α - κ - 1)) [MOD 2 ^ (α + 1)] :=
          four_pow_mod_period κ α (a + 1) hκ
  have hHlt : ∀ i ∈ Hexp α (2 ^ κ), i < 2 ^ (α + 1) := by
    intro i hi
    rw [Hexp, Finset.mem_biUnion] at hi
    obtain ⟨a, _, hia⟩ := hi
    rw [Finset.mem_insert, Finset.mem_singleton] at hia
    rcases hia with rfl | rfl <;> exact Nat.mod_lt _ hmpos
  have hcop : Nat.Coprime g (2 ^ (α + 1)) := by
    rcases hg with rfl | rfl
    · refine (Nat.coprime_two_right.mpr ?_).pow_right _
      rw [conjExp]
      exact Nat.Even.sub_odd Nat.one_le_two_pow ⟨2 ^ α, by rw [pow_succ]; ring⟩ odd_one
    · exact (Nat.coprime_two_right.mpr ⟨2 * 2 ^ κ, by rw [genExp]; ring⟩).pow_right _
  have hinj : Set.InjOn (fun i => (g * i) % 2 ^ (α + 1)) ↑(Hexp α (2 ^ κ)) := by
    intro i hi j hj hij
    rw [Finset.mem_coe] at hi hj
    have h := Nat.ModEq.cancel_left_of_coprime hcop.symm
      (hij : g * i ≡ g * j [MOD 2 ^ (α + 1)])
    rwa [Nat.ModEq, Nat.mod_eq_of_lt (hHlt i hi), Nat.mod_eq_of_lt (hHlt j hj)] at h
  have hsub : (Hexp α (2 ^ κ)).image (fun i => (g * i) % 2 ^ (α + 1)) ⊆ Hexp α (2 ^ κ) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Hexp, hrange, Finset.mem_biUnion] at hi
    rw [Hexp, hrange, Finset.mem_biUnion]
    obtain ⟨a, ha, hia⟩ := hi
    rw [Finset.mem_range] at ha
    rw [Finset.mem_insert, Finset.mem_singleton] at hia
    rcases hg with rfl | rfl
    · rcases hia with rfl | rfl
      · refine ⟨a, Finset.mem_range.mpr ha, ?_⟩
        rw [Finset.mem_insert, Finset.mem_singleton]; right
        rw [conjExp, mul_comm (2 ^ (α + 1) - 1) ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)),
          hgen_neg _ (2 ^ (α + 1) - 1) 1 (by omega), mul_one, Nat.mod_mod]
      · refine ⟨a, Finset.mem_range.mpr ha, ?_⟩
        rw [Finset.mem_insert]; left
        have hpm := hplt a; have hp1a := hp1 a
        have hqv : (2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)
            = 2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) := Nat.mod_eq_of_lt (by omega)
        rw [hqv, conjExp, mul_comm (2 ^ (α + 1) - 1) _,
          hgen_neg _ (2 ^ (α + 1) - 1) 1 (by omega), mul_one, hqv,
          Nat.sub_sub_self (by omega), Nat.mod_eq_of_lt hpm]
    · rcases hia with rfl | rfl
      · refine ⟨(a + 1) % 2 ^ (α - κ - 1), Finset.mem_range.mpr (Nat.mod_lt _ hopos), ?_⟩
        rw [Finset.mem_insert]; left; exact hmulP a
      · refine ⟨(a + 1) % 2 ^ (α - κ - 1), Finset.mem_range.mpr (Nat.mod_lt _ hopos), ?_⟩
        rw [Finset.mem_insert, Finset.mem_singleton]; right
        have hpm := hplt a; have hp1a := hp1 a
        have hsum : (2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)
            + (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) = 2 ^ (α + 1) := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        rw [hgen_neg (genExp (2 ^ κ)) _ ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) hsum, hmulP a]
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq (Finset.card_image_of_injOn hinj).symm)

end ArkLib.Lattices.CyclotomicModulus
