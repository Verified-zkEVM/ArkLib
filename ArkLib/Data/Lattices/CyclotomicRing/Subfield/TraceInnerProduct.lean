/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Packing
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.TraceVanishing

/-!
# The Trace Formula `Tr_H(ψ(a)·σ_{-1}(ψ(b))) = (d/k)·⟨a,b⟩` (Hachi §3, Theorem 2)

The second half of Hachi [NOZ26, §3, Theorem 2]: the relative trace of `ψ(a)·σ_{-1}(ψ(b))`
recovers the inner product `⟨a,b⟩` (scaled by `d/k = |H|`). It builds on the trace-of-monomial
vanishing identities of `Subfield/TraceVanishing.lean` (Claims 2, 3):

* `Tr_H(X^0) = Tr_H(1) = |H| = d/k`  (`traceH_one`);
* `Tr_H(X^i) = 0` for `d/2k ∤ i`     (`traceH_Xpow_eq_zero`, Claim 2);
* `Tr_H(X^{d/2}) = 0`                 (`traceH_Xpow_half`, Claim 3).

Combined with the double-sum expansion of `ψ(a)·σ_{-1}(ψ(b))`, only the diagonal `i = j` terms
survive (giving `Tr_H(X^0) = d/k`), all others vanish, yielding `(d/k)·Σ_i a_i b_i`.

## Main results

* `traceH_smul_fixed` — `Tr_H` is `R_q^H`-linear.
* `traceH_kernel` — `Tr_H(X^{e_p + e_q·σ_{-1}}) = (d/k)·[p=q]`.
* `traceH_psi_mul_conj` — **the Theorem 2 trace formula** `Tr_H(ψ(a)·σ_{-1}(ψ(b))) = (d/k)·⟨a,b⟩`.
* `psi_injective` — `ψ` is injective (from the non-degenerate trace pairing).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

open CompPoly Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]

/-! ## `Tr_H` is `R_q^H`-linear -/

/-- Every `σ_m` with `m ∈ Hexp` fixes `R_q^H`: modulo `2d`, `m` is `±(4k+1)^a`, and the two
generators `σ_{4k+1}`, `σ_{-1}` fix `R_q^H` (so does any composite). -/
theorem galoisAut_fixed_of_mem (α k : ℕ) {c : Rq (powTwoCyclotomic (R := R) α)}
    (hc : c ∈ fixedSubring α k) :
    ∀ m ∈ Hexp α k, galoisAut (powTwoCyclotomic α) m c = c := by
  obtain ⟨hconjc, hgenc⟩ := (mem_fixedSubring_iff α k c).mp hc
  have hodd1 : Odd (4 * k + 1) := ⟨2 * k, by ring⟩
  have hgen' : galoisAut (powTwoCyclotomic α) (4 * k + 1) c = c := by
    rw [genAut, galoisRingHom_apply] at hgenc; exact hgenc
  have hconj' : galoisAut (powTwoCyclotomic α) (conjExp α) c = c := by
    rw [conjAut, galoisRingHom_apply] at hconjc; exact hconjc
  have hgen_pow : ∀ a, galoisAut (powTwoCyclotomic α) ((4 * k + 1) ^ a) c = c := by
    intro a
    induction a with
    | zero => rw [pow_zero, galoisAut_one_eq]
    | succ a ih =>
      rw [pow_succ', ← galoisAut_comp α (4 * k + 1) ((4 * k + 1) ^ a) hodd1 hodd1.pow, ih, hgen']
  have hmpos : 0 < 2 ^ (α + 1) := by positivity
  have h2d : (2 : ℕ) ∣ 2 ^ (α + 1) := dvd_pow_self 2 (Nat.succ_ne_zero α)
  intro m hm
  rw [Hexp, Finset.mem_biUnion] at hm
  obtain ⟨a, _, hma⟩ := hm
  have hpa : (4 * k + 1) ^ a % 2 ^ (α + 1) < 2 ^ (α + 1) := Nat.mod_lt _ hmpos
  have hpa_odd : Odd ((4 * k + 1) ^ a % 2 ^ (α + 1)) := by
    rw [Nat.odd_iff, Nat.mod_mod_of_dvd _ h2d]; exact Nat.odd_iff.mp hodd1.pow
  rw [Finset.mem_insert, Finset.mem_singleton] at hma
  rcases hma with rfl | rfl
  · rw [← galoisAut_periodic, hgen_pow]
  · have hmodneg : (2 ^ (α + 1) - (4 * k + 1) ^ a % 2 ^ (α + 1)) % 2 ^ (α + 1)
        = (conjExp α * ((4 * k + 1) ^ a % 2 ^ (α + 1))) % 2 ^ (α + 1) := by
      have hc1 : conjExp α + 1 = 2 ^ (α + 1) := by
        rw [conjExp]; have : 1 ≤ 2 ^ (α + 1) := Nat.one_le_two_pow; omega
      have hmodeq : conjExp α * ((4 * k + 1) ^ a % 2 ^ (α + 1))
          ≡ 2 ^ (α + 1) - (4 * k + 1) ^ a % 2 ^ (α + 1) [MOD 2 ^ (α + 1)] := by
        apply Nat.ModEq.add_right_cancel' ((4 * k + 1) ^ a % 2 ^ (α + 1))
        rw [Nat.sub_add_cancel (le_of_lt hpa),
          show conjExp α * ((4 * k + 1) ^ a % 2 ^ (α + 1)) + (4 * k + 1) ^ a % 2 ^ (α + 1)
            = ((4 * k + 1) ^ a % 2 ^ (α + 1)) * 2 ^ (α + 1) from by
            rw [conjExp, Nat.sub_mul, one_mul, mul_comm,
              Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by positivity))]]
        exact (Nat.modEq_zero_iff_dvd.mpr ⟨(4 * k + 1) ^ a % 2 ^ (α + 1), mul_comm _ _⟩).trans
          (Nat.modEq_zero_iff_dvd.mpr ⟨1, (mul_one _).symm⟩).symm
      exact hmodeq.symm
    rw [hmodneg, ← galoisAut_periodic,
      ← galoisAut_comp α (conjExp α) ((4 * k + 1) ^ a % 2 ^ (α + 1)) (conjExp_odd α) hpa_odd,
      ← galoisAut_periodic, hgen_pow, hconj']

/-- **`Tr_H` is `R_q^H`-linear**: `Tr_H(c·y) = c·Tr_H(y)` for `c ∈ R_q^H`, since each `σ_m`
(`m ∈ Hexp`) fixes `c` and is multiplicative. -/
theorem traceH_smul_fixed (α k : ℕ) {c : Rq (powTwoCyclotomic (R := R) α)}
    (hc : c ∈ fixedSubring α k) (y : Rq (powTwoCyclotomic α)) :
    traceH α k (c * y) = c * traceH α k y := by
  unfold traceH traceOver
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [galoisAut_mul α m (Hexp_odd_mem α k m hm), galoisAut_fixed_of_mem α k hc m hm]

/-! ## The Theorem 2 kernel -/

/-- **The kernel `Tr_H(X^{e_p + e_q·σ_{-1}}) = (d/k)·[p = q]`** (Hachi [NOZ26, §3, Theorem 2]).
With `e_v = packExp v` and `n = d/2k`: on the diagonal the exponent is `e_p·2d`, so `X^{…} = 1`
and the trace is `d/k`; off the diagonal, `n ∣ (e_p + e_q·σ_{-1}) ↔ p ≡ q mod n`, so when
`p ≢ q mod n` Claim 2 applies, and when `p ≡ q mod n` (but `p ≠ q`) the exponent is `±d/2`, so
`X^{2·(…)} = -1` and the generalized Claim 3 applies. -/
theorem traceH_kernel (α κ : ℕ) (h2 : (2 : R) ≠ 0) (hκ : κ + 1 ≤ α)
    (p q : Fin (2 ^ α / 2 ^ κ)) :
    traceH α (2 ^ κ) (Xpow (powTwoCyclotomic (R := R) α)
        (packExp α (2 ^ κ) p.val + packExp α (2 ^ κ) q.val * conjExp α))
      = if p = q then (2 ^ α / 2 ^ κ) • (1 : Rq (powTwoCyclotomic (R := R) α)) else 0 := by
  have hk : 2 * 2 ^ κ ∣ 2 ^ α := by
    rw [show 2 * 2 ^ κ = 2 ^ (κ + 1) from by rw [pow_succ]; ring]; exact pow_dvd_pow 2 hκ
  set n := 2 ^ α / (2 * 2 ^ κ) with hn
  have hrange : n = 2 ^ (α - κ - 1) := by
    rw [hn, show 2 * 2 ^ κ = 2 ^ (κ + 1) from by rw [pow_succ]; ring, Nat.pow_div hκ (by norm_num),
      Nat.sub_sub]
  have hnpos : 0 < n := by rw [hrange]; positivity
  have hn_dvd_M : n ∣ 2 ^ (α + 1) := by rw [hrange]; exact pow_dvd_pow 2 (by omega)
  have hd2 : 2 ^ (α - 1) = 2 ^ κ * n := by rw [hrange, ← pow_add]; congr 1; omega
  have hc1 : conjExp α + 1 = 2 ^ (α + 1) := by
    have : 1 ≤ 2 ^ (α + 1) := Nat.one_le_two_pow; rw [conjExp]; omega
  have htwon : 2 ^ α / 2 ^ κ = 2 * n := by
    rw [hrange, Nat.pow_div (by omega) (by norm_num), ← pow_succ']; congr 1; omega
  have h2α : 2 * 2 ^ (α - 1) = 2 ^ α := by rw [← pow_succ']; congr 1; omega
  have hαα : 2 ^ α + 2 ^ α = 2 ^ (α + 1) := by rw [← two_mul, ← pow_succ']
  have hpackmod : ∀ v, packExp α (2 ^ κ) v % n = v % n := by
    intro v
    unfold packExp
    rw [← hn]
    split_ifs with hv
    · rfl
    · rw [hd2, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod,
        ← Nat.mod_eq_sub_mod (Nat.not_lt.mp hv)]
  set ep := packExp α (2 ^ κ) p.val with hep
  set eq := packExp α (2 ^ κ) q.val with heq
  have hzmod : eq * 2 ^ (α + 1) % n = 0 := by
    obtain ⟨c, hc⟩ := hn_dvd_M.mul_left eq; rw [hc, Nat.mul_mod_right]
  -- `n ∣ J ↔ p ≡ q (mod n)`
  have hJn : (ep + eq * conjExp α + eq) % n = ep % n := by
    rw [show ep + eq * conjExp α + eq = ep + eq * 2 ^ (α + 1) from by rw [← hc1]; ring,
      Nat.add_mod, hzmod, Nat.add_zero, Nat.mod_mod]
  have hJdvd : n ∣ (ep + eq * conjExp α) ↔ p.val % n = q.val % n := by
    rw [Nat.dvd_iff_mod_eq_zero, ← hpackmod p.val, ← hpackmod q.val, ← hep, ← heq]
    constructor
    · intro h0
      have h1 : (ep + eq * conjExp α + eq) % n = eq % n := by
        rw [Nat.add_mod, h0, Nat.zero_add, Nat.mod_mod]
      rw [hJn] at h1; exact h1
    · intro hpq
      have hb : (ep + eq * conjExp α + eq) % n = (0 + eq) % n := by rw [hJn, Nat.zero_add, hpq]
      exact Nat.ModEq.add_right_cancel' eq hb
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos rfl,
      show ep + ep * conjExp α = 2 ^ (α + 1) * ep from by
        rw [conjExp, Nat.mul_sub, mul_one, Nat.add_sub_cancel'
          (Nat.le_mul_of_pos_right _ (by positivity)), mul_comm],
      Xpow_mul, Xpow_conductor, one_pow, traceH_one α (2 ^ κ) ⟨κ, rfl⟩ hk]
  · rw [if_neg hpq]
    by_cases hmod : p.val % n = q.val % n
    · -- `±d/2` case: `X^{2J} = -1`, generalized Claim 3
      refine traceH_Xpow_neg_one_sq α (2 ^ κ) _ ⟨κ, rfl⟩ hk ?_
      have hqlt : q.val < 2 * n := htwon ▸ q.isLt
      have hplt : p.val < 2 * n := htwon ▸ p.isLt
      have hne : p.val ≠ q.val := fun h => hpq (Fin.ext h)
      have h2pp : 2 * ep ≡ 2 ^ α + 2 * eq [MOD 2 ^ (α + 1)] := by
        rcases lt_or_ge p.val n with hpn | hpn
        · have hqn : ¬ q.val < n := fun hqn =>
            hne (by rw [Nat.mod_eq_of_lt hpn, Nat.mod_eq_of_lt hqn] at hmod; exact hmod)
          have hqv : q.val - n = p.val := by
            have hp' : p.val % n = p.val := Nat.mod_eq_of_lt hpn
            have hq' : q.val % n = q.val - n := by
              rw [Nat.mod_eq_sub_mod (Nat.not_lt.mp hqn), Nat.mod_eq_of_lt (by omega)]
            rw [hp', hq'] at hmod; exact hmod.symm
          have hepv : ep = p.val := by rw [hep]; unfold packExp; rw [← hn, if_pos hpn]
          have heqv : eq = 2 ^ (α - 1) + p.val := by
            rw [heq]; unfold packExp; rw [← hn, if_neg hqn, hqv]
          rw [hepv, heqv, Nat.ModEq,
            show 2 ^ α + 2 * (2 ^ (α - 1) + p.val) = 2 ^ (α + 1) + 2 * p.val from by omega,
            Nat.add_mod_left]
        · have hqn : q.val < n := by
            by_contra hqn'
            have hp' : p.val % n = p.val - n := by
              rw [Nat.mod_eq_sub_mod hpn, Nat.mod_eq_of_lt (by omega)]
            have hq' : q.val % n = q.val - n := by
              rw [Nat.mod_eq_sub_mod (Nat.not_lt.mp hqn'), Nat.mod_eq_of_lt (by omega)]
            rw [hp', hq'] at hmod; exact hne (by omega)
          have hpv : p.val - n = q.val := by
            have hp' : p.val % n = p.val - n := by
              rw [Nat.mod_eq_sub_mod hpn, Nat.mod_eq_of_lt (by omega)]
            have hq' : q.val % n = q.val := Nat.mod_eq_of_lt hqn
            rw [hp', hq'] at hmod; exact hmod
          have hepv : ep = 2 ^ (α - 1) + q.val := by
            rw [hep]; unfold packExp; rw [← hn, if_neg (not_lt.mpr hpn), hpv]
          have heqv : eq = q.val := by rw [heq]; unfold packExp; rw [← hn, if_pos hqn]
          rw [hepv, heqv,
            show 2 * (2 ^ (α - 1) + q.val) = 2 ^ α + 2 * q.val from by omega]
      have hJ2 : 2 * (ep + eq * conjExp α) + 2 * eq ≡ 2 * ep [MOD 2 ^ (α + 1)] := by
        rw [Nat.ModEq, show 2 * (ep + eq * conjExp α) + 2 * eq
            = 2 * ep + (2 * eq) * 2 ^ (α + 1) from by rw [← hc1]; ring, Nat.add_mul_mod_self_right]
      have hkey : 2 * (ep + eq * conjExp α) % 2 ^ (α + 1) = 2 ^ α % 2 ^ (α + 1) :=
        Nat.ModEq.add_right_cancel' (2 * eq) (hJ2.trans h2pp)
      rw [Xpow_congr_mod α hkey, Xpow_natDegree]
    · -- `d/2k ∤ J` case: Claim 2
      refine traceH_Xpow_eq_zero α (2 ^ κ) h2 ⟨κ, rfl⟩ hk ?_
      rw [← hn]
      exact fun h => hmod (hJdvd.mp h)

/-! ## The Theorem 2 trace formula -/

/-- `Tr_H` distributes over finite sums (it is additive). -/
theorem traceH_sum (α k : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → Rq (powTwoCyclotomic (R := R) α)) :
    traceH α k (∑ j ∈ s, f j) = ∑ j ∈ s, traceH α k (f j) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact traceOver_zero _ _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha,
      show traceH α k (f a + ∑ j ∈ s, f j) = traceH α k (f a) + traceH α k (∑ j ∈ s, f j) from
        traceOver_add _ _ _ _,
      ih, Finset.sum_insert ha]

/-- **Hachi [NOZ26, §3, Theorem 2]**: `Tr_H(ψ(a)·σ_{-1}(ψ(b))) = (d/k)·⟨a,b⟩`, where
`⟨a,b⟩ = Σ_i a_i b_i` is the inner product over `R_q^H`. Expand the product as a double sum,
pull the `R_q^H`-coefficients out of `Tr_H` (`traceH_smul_fixed`), evaluate the monomial kernel
(`traceH_kernel`, which is `(d/k)·[p=q]`), and collapse the diagonal. -/
theorem traceH_psi_mul_conj (α k : ℕ) (h2 : (2 : R) ≠ 0) (hk2pow : ∃ κ, k = 2 ^ κ)
    (hk : 2 * k ∣ 2 ^ α)
    (a b : Fin (2 ^ α / k) → fixedSubring (R := R) α k) :
    traceH α k (psi α k a * conjAut α (psi α k b))
      = (2 ^ α / k) • ((∑ i, a i * b i : fixedSubring (R := R) α k) :
          Rq (powTwoCyclotomic (R := R) α)) := by
  obtain ⟨κ, rfl⟩ := hk2pow
  have hκ : κ + 1 ≤ α := succ_le_of_two_mul_two_pow_dvd hk
  -- `σ_{-1}(ψ(b)) = Σ_q ↑(b q)·X^{e_q·σ_{-1}}` (`σ_{-1}` fixes `b q ∈ R_q^H`)
  have hconjpsi : conjAut α (psi α (2 ^ κ) b)
      = ∑ q, (b q : Rq (powTwoCyclotomic α))
          * Xpow (powTwoCyclotomic α) (packExp α (2 ^ κ) q.val * conjExp α) := by
    unfold psi
    rw [map_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [map_mul, ((mem_fixedSubring_iff α (2 ^ κ) _).mp (b q).2).1, conjAut, galoisRingHom_apply,
      galoisAut_Xpow' α (conjExp α) _ (conjExp_odd α)]
  -- Rewrite each summand in place via `Finset.sum_congr`; the coefficient `↑(a p)·↑(b q)` arises
  -- from `mul_mem`/`traceH_smul_fixed`, so it is never written as a `coe * coe` product (which
  -- mis-resolves to the subring's `*`).
  rw [hconjpsi]
  unfold psi
  rw [Finset.sum_mul_sum]
  simp only [traceH_sum]
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => by
    rw [mul_mul_mul_comm, ← Xpow_add, traceH_smul_fixed α (2 ^ κ) (mul_mem (a p).2 (b q).2),
      traceH_kernel α κ h2 hκ p q]))]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_smul_comm,
    mul_one]
  rw [← Finset.smul_sum]
  congr 1
  rw [AddSubmonoidClass.coe_finsetSum]
  simp only [MulMemClass.coe_mul]

/-! ## `ψ` is injective (from the non-degenerate trace pairing) -/

/-- **`ψ` is injective** (Hachi [NOZ26, §3, Theorem 2]). The trace form `(a,b) ↦ ⟨a,b⟩` is
non-degenerate (testing against `b = eⱼ` recovers `aⱼ`), and `d/k` is a unit in `R_q` (it is a
power of `2`, invertible since `q` is odd). So `ψ(a) = ψ(b)` forces `⟨a,eⱼ⟩ = ⟨b,eⱼ⟩`, i.e.
`aⱼ = bⱼ`, for every `j`. -/
theorem psi_injective (α k : ℕ) (h2 : (2 : R) ≠ 0) (hk2pow : ∃ κ, k = 2 ^ κ)
    (hk : 2 * k ∣ 2 ^ α) : Function.Injective (psi (R := R) α k) := by
  obtain ⟨κ, rfl⟩ := hk2pow
  have hκ : κ ≤ α := Nat.le_of_succ_le (succ_le_of_two_mul_two_pow_dvd hk)
  have hunit : IsUnit ((2 ^ α / 2 ^ κ : ℕ) : Rq (powTwoCyclotomic (R := R) α)) := by
    rw [Nat.pow_div hκ (by norm_num), Nat.cast_pow, Nat.cast_ofNat]
    exact (isUnit_two (powTwoCyclotomic α) h2).pow _
  intro a b hab
  funext j
  have ha := traceH_psi_mul_conj α (2 ^ κ) h2 ⟨κ, rfl⟩ hk a (Pi.single j 1)
  have hb := traceH_psi_mul_conj α (2 ^ κ) h2 ⟨κ, rfl⟩ hk b (Pi.single j 1)
  rw [hab] at ha
  have heq := ha.symm.trans hb
  rw [nsmul_eq_mul, nsmul_eq_mul] at heq
  have hcancel := hunit.mul_left_cancel heq
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hcancel
  exact Subtype.coe_injective hcancel

end ArkLib.Lattices.CyclotomicModulus
