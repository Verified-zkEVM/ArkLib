/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Basis

/-!
# Trace of a Monomial: the Off-Diagonal Vanishing (Hachi §3, Claims 2 & 3)

The trace-of-monomial identities that drive the Theorem 2 kernel. Writing `H = ⟨σ_{-1}, σ_{4k+1}⟩`
and `d = 2^α`, `k = 2^κ`:

* `traceH_Xpow` — `Tr_H(X^i) = Σ_{m∈H} X^{i·m}` (reduces the trace to a monomial sum);
* `traceH_one` — `Tr_H(1) = (d/k)·1`;
* `traceH_Xpow_eq_zero` (**Claim 2**) — `Tr_H(X^i) = 0` when `d/2k ∤ i`;
* `traceH_Xpow_half` (**Claim 3**) — `Tr_H(X^{d/2}) = 0`.

The algebraic core of Claim 2 is the geometric-sum vanishing `Σ_{j<d/2k}(X^{4ki})^j = 0`
(`four_pow_i_geom_zero`), via `X^{4ki} − 1` being a *unit* (`Xpow_sub_one_isUnit`).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open CompPoly Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]

/-! ## Reducing the trace to a monomial sum -/

/-- **`Tr_H(X^i) = Σ_{m∈H} X^{i·m}`** (for `i` below the modulus degree): the trace of a
monomial is the sum of its images under all of `H`, each a single (reduced) monomial. -/
theorem traceH_Xpow (α k : ℕ) {i : ℕ} (hi : i < 2 ^ α) :
    traceH α k (Xpow (powTwoCyclotomic (R := R) α) i)
      = ∑ m ∈ Hexp α k, Xpow (powTwoCyclotomic (R := R) α) (i * m) := by
  unfold traceH traceOver
  exact Finset.sum_congr rfl (fun m _ => galoisAut_Xpow α m hi)

/-- **`Tr_H(X^j) = Σ_{m∈H} X^{j·m}` for any exponent `j`** (no `j < d` bound), via the general
`galoisAut_Xpow'` and oddness of the `Hexp` exponents. Needed for the Theorem 2 kernel, where the
exponents `e_p + e_q·σ_{-1}` are large. -/
theorem traceH_Xpow' (α k j : ℕ) :
    traceH α k (Xpow (powTwoCyclotomic (R := R) α) j)
      = ∑ m ∈ Hexp α k, Xpow (powTwoCyclotomic (R := R) α) (j * m) := by
  unfold traceH traceOver
  exact Finset.sum_congr rfl (fun m hm => galoisAut_Xpow' α m j (Hexp_odd_mem α k m hm))

/-- **`Tr_H(1) = (d/k)·1`** (Hachi [NOZ26, §3], `Tr_H(X^0)`): each `σ_m` fixes `1`, so the trace
is `|H| = d/k` copies of `1`. -/
theorem traceH_one (α k : ℕ) (hk2pow : ∃ κ, k = 2 ^ κ) (hk : 2 * k ∣ 2 ^ α) :
    traceH α k (1 : Rq (powTwoCyclotomic (R := R) α))
      = (2 ^ α / k) • (1 : Rq (powTwoCyclotomic (R := R) α)) := by
  unfold traceH traceOver
  rw [Finset.sum_congr rfl (fun m _ => galoisAut_map_one α m), Finset.sum_const,
    Hexp_card α k hk2pow hk]

/-! ## Geometric-sum vanishing (the algebraic core of Claim 2) -/

/-- **Geometric sum vanishes when `r-1` is a unit**: if `r^n = 1` and `r - 1` is a unit (no
domain needed), then `∑_{i<n} r^i = 0`. Follows from `(∑ r^i)(r-1) = r^n - 1 = 0` and cancelling
the unit `r - 1`. This is what closes Claim 2 once `X^{4ki} - 1` is shown to be a unit. -/
theorem geom_sum_eq_zero_of_isUnit {A : Type*} [CommRing A] {r : A} {n : ℕ}
    (hr : r ^ n = 1) (hu : IsUnit (r - 1)) : ∑ i ∈ Finset.range n, r ^ i = 0 := by
  have h : (∑ i ∈ Finset.range n, r ^ i) * (r - 1) = 0 := by rw [geom_sum_mul, hr, sub_self]
  exact (IsUnit.mul_left_eq_zero hu).mp h

/-- The geometric sum `∑_{j<d/2k} (X^{4ki})^j = 0` when `d/2k ∤ i`. The ratio `r = X^{4ki}`
satisfies `r^{d/2k} = X^{2di} = 1`, and `r - 1` is a unit (`Xpow_sub_one_isUnit`, since
`X^{4ki·2^t} = -1` for a suitable `t` extracted from the `2`-adic valuation of `i`). -/
theorem four_pow_i_geom_zero (α κ i : ℕ) (h2 : (2 : R) ≠ 0) (hκ : κ + 1 ≤ α)
    (hi0 : ¬ 2 ^ (α - κ - 1) ∣ i) :
    ∑ j ∈ Finset.range (2 ^ (α - κ - 1)),
      (Xpow (powTwoCyclotomic (R := R) α) (4 * 2 ^ κ * i)) ^ j = 0 := by
  apply geom_sum_eq_zero_of_isUnit
  · rw [← Xpow_mul]
    have he : 4 * 2 ^ κ * i * 2 ^ (α - κ - 1) = 2 ^ (α + 1) * i := by
      have h4 : (4 : ℕ) * 2 ^ κ * 2 ^ (α - κ - 1) = 2 ^ (α + 1) := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, mul_assoc, ← pow_add, ← pow_add]; congr 1; omega
      calc 4 * 2 ^ κ * i * 2 ^ (α - κ - 1) = (4 * 2 ^ κ * 2 ^ (α - κ - 1)) * i := by ring
        _ = 2 ^ (α + 1) * i := by rw [h4]
    rw [he, Xpow_mul, Xpow_conductor, one_pow]
  · have hine : i ≠ 0 := by rintro rfl; exact hi0 (dvd_zero _)
    have hα2 : κ + 2 ≤ α := by
      rcases Nat.lt_or_ge α (κ + 2) with h | h
      · exact absurd (show 2 ^ (α - κ - 1) ∣ i from by
          rw [show α - κ - 1 = 0 from by omega, pow_zero]; exact one_dvd i) hi0
      · exact h
    obtain ⟨w, i', hi'odd, hieq⟩ := Nat.exists_eq_two_pow_mul_odd hine
    have hw : w ≤ α - κ - 2 := by
      by_contra hge
      exact hi0 (hieq ▸ Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega : α - κ - 1 ≤ w)) i')
    apply Xpow_sub_one_isUnit α h2 (t := α - κ - 2 - w)
    have he2 : 4 * 2 ^ κ * i * 2 ^ (α - κ - 2 - w) = 2 ^ α * i' := by
      rw [hieq, show 4 * 2 ^ κ * (2 ^ w * i') * 2 ^ (α - κ - 2 - w)
          = (4 * 2 ^ κ * 2 ^ w * 2 ^ (α - κ - 2 - w)) * i' from by ring]
      congr 1
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add, ← pow_add, ← pow_add]; congr 1; omega
    rw [he2, Xpow_mul, Xpow_natDegree, hi'odd.neg_one_pow]

/-- **Claim 1 reindex**: `∑_{a<n} X^{i·((4k+1)^a mod 2d)} = X^i·∑_{j<n} (X^{4ki})^j`. The subgroup
`⟨4k+1⟩ = {(4k+1)^a mod 2d}` equals the arithmetic progression `{4k·j+1 : j<n}` (both have `n`
distinct elements, and `(4k+1)^a ≡ 1 mod 4k`), which linearizes the exponent and exposes the
geometric series. -/
theorem four_pow_i_reindex (α κ i : ℕ) (hκ : κ + 1 ≤ α) :
    ∑ a ∈ Finset.range (2 ^ (α - κ - 1)),
        Xpow (powTwoCyclotomic (R := R) α) (i * ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)))
      = Xpow (powTwoCyclotomic (R := R) α) i
        * ∑ j ∈ Finset.range (2 ^ (α - κ - 1)),
            (Xpow (powTwoCyclotomic (R := R) α) (4 * 2 ^ κ * i)) ^ j := by
  have h2κ : 1 ≤ 2 ^ κ := Nat.one_le_two_pow
  have hgM : (4 * 2 ^ κ : ℕ) ∣ 2 ^ (α + 1) := by
    rw [show (4 * 2 ^ κ : ℕ) = 2 ^ (2 + κ) from by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]]
    exact pow_dvd_pow 2 (by omega)
  have hMn : 4 * 2 ^ κ * 2 ^ (α - κ - 1) = 2 ^ (α + 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, mul_assoc, ← pow_add, ← pow_add]; congr 1; omega
  have hφinj : Set.InjOn (fun a => (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1))
      ↑(Finset.range (2 ^ (α - κ - 1))) := four_pow_injOn κ α hκ
  have hψinj : Set.InjOn (fun j => 4 * 2 ^ κ * j + 1)
      ↑(Finset.range (2 ^ (α - κ - 1))) := by
    intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (Nat.add_right_cancel h)
  have himg : (Finset.range (2 ^ (α - κ - 1))).image
        (fun a => (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1))
      = (Finset.range (2 ^ (α - κ - 1))).image (fun j => 4 * 2 ^ κ * j + 1) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_image] at hx ⊢
      obtain ⟨a, _, rfl⟩ := hx
      have hlt : (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) < 2 ^ (α + 1) := Nat.mod_lt _ (by positivity)
      have hmod1 : (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) % (4 * 2 ^ κ) = 1 := by
        rw [Nat.mod_mod_of_dvd _ hgM, Nat.pow_mod,
          show (4 * 2 ^ κ + 1) % (4 * 2 ^ κ) = 1 from by
            rw [Nat.add_mod_left]; exact Nat.mod_eq_of_lt (by omega),
          one_pow, Nat.mod_eq_of_lt (by omega)]
      have hge1 : 1 ≤ (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) := by
        rcases Nat.eq_zero_or_pos ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) with h | h
        · rw [h, Nat.zero_mod] at hmod1; exact absurd hmod1 (by norm_num)
        · exact h
      have hdvd : (4 * 2 ^ κ) ∣ ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) - 1) :=
        (Nat.modEq_iff_dvd' hge1).mp (by rw [Nat.ModEq, hmod1, Nat.mod_eq_of_lt (by omega)])
      refine ⟨((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) - 1) / (4 * 2 ^ κ), ?_, ?_⟩
      · rw [Finset.mem_range]
        have hbound : (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) - 1 < 4 * 2 ^ κ * 2 ^ (α - κ - 1) := by
          rw [hMn]; omega
        exact Nat.div_lt_of_lt_mul hbound
      · rw [Nat.mul_div_cancel' hdvd]; omega
    · rw [Finset.card_image_of_injOn hφinj, Finset.card_image_of_injOn hψinj]
  have e1 : ∑ a ∈ Finset.range (2 ^ (α - κ - 1)),
        Xpow (powTwoCyclotomic (R := R) α) (i * ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)))
      = ∑ x ∈ (Finset.range (2 ^ (α - κ - 1))).image
          (fun a => (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)),
          Xpow (powTwoCyclotomic (R := R) α) (i * x) :=
    (Finset.sum_image (f := fun x => Xpow (powTwoCyclotomic (R := R) α) (i * x)) hφinj).symm
  have e2 : ∑ x ∈ (Finset.range (2 ^ (α - κ - 1))).image (fun j => 4 * 2 ^ κ * j + 1),
        Xpow (powTwoCyclotomic (R := R) α) (i * x)
      = ∑ j ∈ Finset.range (2 ^ (α - κ - 1)),
          Xpow (powTwoCyclotomic (R := R) α) (i * (4 * 2 ^ κ * j + 1)) :=
    Finset.sum_image (f := fun x => Xpow (powTwoCyclotomic (R := R) α) (i * x)) hψinj
  rw [e1, himg, e2, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [show i * (4 * 2 ^ κ * j + 1) = i + 4 * 2 ^ κ * i * j from by ring, Xpow_add, Xpow_mul]

/-! ## Trace of a monomial vanishes off the diagonal (Claims 2, 3) -/

/-- **(Claim 2)** `Tr_H(X^i) = 0` whenever `d/2k ∤ i`. Splitting `H = ⟨σ_{-1}, σ_{4k+1}⟩` into the
`⟨4k+1⟩`-orbit `{p_a}` and its conjugate `{q_a = -p_a}`, the orbit sum is `X^i·∑_{j}(X^{4ki})^j`
(`four_pow_i_reindex`), which vanishes (`four_pow_i_geom_zero`); the conjugate sum is its image
under `σ_{-1}`, hence also `0`. -/
theorem traceH_Xpow_eq_zero (α k : ℕ) (h2 : (2 : R) ≠ 0) (hk2pow : ∃ κ, k = 2 ^ κ)
    (hk : 2 * k ∣ 2 ^ α) {i : ℕ} (hi0 : ¬ (2 ^ α / (2 * k)) ∣ i) :
    traceH α k (Xpow (powTwoCyclotomic (R := R) α) i) = 0 := by
  obtain ⟨κ, rfl⟩ := hk2pow
  have hκ : κ + 1 ≤ α := succ_le_of_two_mul_two_pow_dvd hk
  have hrange : 2 ^ α / (2 * 2 ^ κ) = 2 ^ (α - κ - 1) := by
    rw [show 2 * 2 ^ κ = 2 ^ (κ + 1) from by rw [pow_succ]; ring, Nat.pow_div hκ (by norm_num),
      Nat.sub_sub]
  have hi0' : ¬ 2 ^ (α - κ - 1) ∣ i := by rwa [hrange] at hi0
  have hmpos : 0 < 2 ^ (α + 1) := by positivity
  have hm4 : (4 : ℕ) ∣ 2 ^ (α + 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl]; exact pow_dvd_pow 2 (by omega)
  have hm40 : 2 ^ (α + 1) % 4 = 0 := by obtain ⟨c, hc⟩ := hm4; omega
  have hp4 : ∀ a, (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) % 4 = 1 := fun a => by
    rw [Nat.mod_mod_of_dvd _ hm4, Nat.pow_mod]
    norm_num [show (4 * 2 ^ κ + 1) % 4 = 1 from by omega]
  have hplt : ∀ a, (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) < 2 ^ (α + 1) := fun a => Nat.mod_lt _ hmpos
  have hqeq : ∀ a, (2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)
      = 2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) := fun a =>
    Nat.mod_eq_of_lt (by have := hplt a; have := hp4 a; omega)
  have hpinj : Set.InjOn (fun a => (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1))
      ↑(Finset.range (2 ^ (α - κ - 1))) := four_pow_injOn κ α hκ
  -- the orbit sum and conjugate sum both vanish
  have hTp : ∑ a ∈ Finset.range (2 ^ (α - κ - 1)),
      Xpow (powTwoCyclotomic (R := R) α) (i * ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1))) = 0 := by
    rw [four_pow_i_reindex α κ i hκ, four_pow_i_geom_zero α κ i h2 hκ hi0', mul_zero]
  have hTq : ∑ a ∈ Finset.range (2 ^ (α - κ - 1)),
      Xpow (powTwoCyclotomic (R := R) α)
        (i * ((2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1))) = 0 := by
    have hconj : ∀ a ∈ Finset.range (2 ^ (α - κ - 1)),
        Xpow (powTwoCyclotomic (R := R) α)
          (i * ((2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)))
        = conjAut α (Xpow (powTwoCyclotomic (R := R) α)
            (i * ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)))) := by
      intro a _
      rw [conjAut, galoisRingHom_apply, galoisAut_Xpow' α (conjExp α) _ (conjExp_odd α)]
      apply Xpow_congr_mod
      have hpa := hplt a
      have key : i * (2 ^ (α + 1) - (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1))
          ≡ i * ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) * conjExp α [MOD 2 ^ (α + 1)] := by
        apply Nat.ModEq.add_right_cancel' (i * ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)))
        have hc1 : conjExp α + 1 = 2 ^ (α + 1) := by
          rw [conjExp]; have : 1 ≤ 2 ^ (α + 1) := Nat.one_le_two_pow; omega
        rw [← Nat.mul_add,
          Nat.sub_add_cancel (le_of_lt hpa),
          show i * ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) * conjExp α
              + i * ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1))
            = i * ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)) * 2 ^ (α + 1) from by
            rw [← hc1]; ring]
        exact (Nat.modEq_zero_iff_dvd.mpr ⟨i, by ring⟩).trans
          (Nat.modEq_zero_iff_dvd.mpr ⟨i * ((4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1)), by ring⟩).symm
      exact (Nat.ModEq.mul_left i (Nat.mod_modEq _ _)).trans key
    rw [Finset.sum_congr rfl hconj, ← map_sum, hTp, map_zero]
  -- assemble
  rw [traceH_Xpow' α (2 ^ κ)]
  unfold Hexp
  rw [hrange, Finset.sum_biUnion (by
    intro a ha b hb hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    have hpab : (4 * 2 ^ κ + 1) ^ a % 2 ^ (α + 1) ≠ (4 * 2 ^ κ + 1) ^ b % 2 ^ (α + 1) :=
      fun h => hab (hpinj ha hb h)
    intro x hx hx'
    rw [hqeq a] at hx; rw [hqeq b] at hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
    have := hp4 a; have := hp4 b; have := hplt a; have := hplt b
    rcases hx with rfl | rfl <;> rcases hx' with h' | h' <;> omega)]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_pair (by
    rw [hqeq a]; have := hp4 a; have := hplt a; omega)),
    Finset.sum_add_distrib, hTp, hTq, add_zero]

/-- **Generalized Claim 3**: `Tr_H(X^j) = 0` for any `j` with `X^{2j} = -1` (equivalently
`2j ≡ d mod 2d`, i.e. `j` an odd multiple of `d/2`). Proven by a fixed-point-free involution on
`H`: conjugation `m ↦ -m` sends `X^{j·m}` to its negation, since `(X^{j·m})² = (X^{2j})^m =
(-1)^m = -1` (`m` odd) and conjugation inverts a square-root of `-1`. -/
theorem traceH_Xpow_neg_one_sq (α k j : ℕ) (hk2pow : ∃ κ, k = 2 ^ κ) (hk : 2 * k ∣ 2 ^ α)
    (hsq : Xpow (powTwoCyclotomic (R := R) α) (2 * j) = -1) :
    traceH α k (Xpow (powTwoCyclotomic (R := R) α) j) = 0 := by
  have hHlt : ∀ m, m ∈ Hexp α k → m < 2 ^ (α + 1) := by
    intro m hmem
    rw [Hexp, Finset.mem_biUnion] at hmem
    obtain ⟨a, _, hma⟩ := hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hma
    rcases hma with rfl | rfl <;> exact Nat.mod_lt _ (by positivity)
  have hmem : ∀ m, m ∈ Hexp α k → (conjExp α * m) % 2 ^ (α + 1) ∈ Hexp α k := by
    intro m hm
    rw [← Hexp_generator_smul α k (conjExp α) hk2pow hk (Or.inl rfl)]
    exact Finset.mem_image_of_mem _ hm
  rw [traceH_Xpow' α k j]
  refine Finset.sum_involution (fun m _ => (conjExp α * m) % 2 ^ (α + 1)) ?_ ?_ hmem ?_
  · intro m hm
    have hmodd : Odd m := Hexp_odd_mem α k m hm
    have hstep : Xpow (powTwoCyclotomic (R := R) α) (j * ((conjExp α * m) % 2 ^ (α + 1)))
        = Xpow (powTwoCyclotomic (R := R) α) ((j * m) * conjExp α) := by
      apply Xpow_congr_mod
      exact calc j * ((conjExp α * m) % 2 ^ (α + 1))
            ≡ j * (conjExp α * m) [MOD 2 ^ (α + 1)] := Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
        _ = (j * m) * conjExp α := by ring
    have hsqm : Xpow (powTwoCyclotomic (R := R) α) (2 * (j * m)) = -1 := by
      rw [show 2 * (j * m) = (2 * j) * m from by ring, Xpow_mul, hsq, hmodd.neg_one_pow]
    rw [hstep, Xpow_mul_conjExp α (j * m) hsqm, add_neg_cancel]
  · intro m hm _ hgm
    have hmodd : Odd m := Hexp_odd_mem α k m hm
    have hmlt : m < 2 ^ (α + 1) := hHlt m hm
    have hα : 1 ≤ α := by
      obtain ⟨κ, rfl⟩ := hk2pow
      have := succ_le_of_two_mul_two_pow_dvd hk; omega
    have hcong : conjExp α * m ≡ m [MOD 2 ^ (α + 1)] := by
      rw [Nat.ModEq, hgm, Nat.mod_eq_of_lt hmlt]
    have hdvd : 2 ^ (α + 1) ∣ 2 * m := by
      have e1 : conjExp α * m + m = 2 ^ (α + 1) * m := by
        have hc : conjExp α + 1 = 2 ^ (α + 1) := by
          have h1 : 1 ≤ 2 ^ (α + 1) := Nat.one_le_two_pow
          rw [conjExp]; omega
        calc conjExp α * m + m = (conjExp α + 1) * m := by ring
          _ = 2 ^ (α + 1) * m := by rw [hc]
      have h2m : 2 * m ≡ 0 [MOD 2 ^ (α + 1)] :=
        calc 2 * m = m + m := by ring
          _ ≡ conjExp α * m + m [MOD 2 ^ (α + 1)] := Nat.ModEq.add_right m hcong.symm
          _ = 2 ^ (α + 1) * m := e1
          _ ≡ 0 [MOD 2 ^ (α + 1)] := (Nat.modEq_zero_iff_dvd).mpr ⟨m, rfl⟩
      exact (Nat.modEq_zero_iff_dvd).mp h2m
    have hdvd2 : 2 ^ α ∣ m := by
      have he : 2 ^ (α + 1) = 2 * 2 ^ α := by rw [pow_succ]; ring
      rw [he] at hdvd
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp hdvd
    have h2m : 2 ∣ m := dvd_trans (dvd_pow_self 2 (by omega : α ≠ 0)) hdvd2
    obtain ⟨t, ht⟩ := hmodd
    omega
  · intro m hm
    have hmlt : m < 2 ^ (α + 1) := hHlt m hm
    have hcsq : conjExp α * conjExp α ≡ 1 [MOD 2 ^ (α + 1)] := by
      have hid : conjExp α * conjExp α = 2 ^ (α + 1) * (2 ^ (α + 1) - 2) + 1 := by
        have hM2 : 2 ≤ 2 ^ (α + 1) := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ (α + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hM2
        rw [conjExp, ht]
        simp only [show 2 + t - 1 = t + 1 from by omega, show 2 + t - 2 = t from by omega]
        ring
      rw [Nat.ModEq, hid, Nat.mul_add_mod]
    have key : conjExp α * ((conjExp α * m) % 2 ^ (α + 1)) ≡ m [MOD 2 ^ (α + 1)] :=
      calc conjExp α * ((conjExp α * m) % 2 ^ (α + 1))
            ≡ conjExp α * (conjExp α * m) [MOD 2 ^ (α + 1)] :=
              Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
        _ = (conjExp α * conjExp α) * m := by ring
        _ ≡ 1 * m [MOD 2 ^ (α + 1)] := Nat.ModEq.mul_right m hcsq
        _ = m := one_mul m
    have heq : (conjExp α * ((conjExp α * m) % 2 ^ (α + 1))) % 2 ^ (α + 1) = m % 2 ^ (α + 1) := key
    rw [heq, Nat.mod_eq_of_lt hmlt]

/-- **(Claim 3)** `Tr_H(X^{d/2}) = 0` — the `j = d/2` instance of `traceH_Xpow_neg_one_sq`
(`X^{2·d/2} = X^d = -1`). -/
theorem traceH_Xpow_half (α k : ℕ) (hk2pow : ∃ κ, k = 2 ^ κ) (hk : 2 * k ∣ 2 ^ α) :
    traceH α k (Xpow (powTwoCyclotomic (R := R) α) (2 ^ (α - 1))) = 0 := by
  have hα : 1 ≤ α := by
    obtain ⟨κ, rfl⟩ := hk2pow
    have := succ_le_of_two_mul_two_pow_dvd hk; omega
  refine traceH_Xpow_neg_one_sq α k (2 ^ (α - 1)) hk2pow hk ?_
  rw [show 2 * 2 ^ (α - 1) = 2 ^ α from by rw [← pow_succ']; congr 1; omega, Xpow_natDegree]

end ArkLib.Lattices.CyclotomicModulus
