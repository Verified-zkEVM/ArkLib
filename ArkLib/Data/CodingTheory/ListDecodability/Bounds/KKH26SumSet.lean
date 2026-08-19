/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# KKH26 sum-set lower bound

This module proves the number-theoretic sum-set estimate underlying [KKH26]'s Reed--Solomon
list-size lower bound: over a prime field, the sum-set of all `k̂`-subsets of a power-of-two-order
multiplicative subgroup is large.

## Main result

- `two_pow_mul_choose_le_card_sumSet` — over a prime field `𝔽_q` with `q > h^{h/2}`, the family of
  all `k̂`-subsets of a power-of-two-order subgroup `H` of size `h` has `|Λ_𝒮| ≥ 2^k̂ · C(h/2, k̂)`.

## References

- [KKH26] Krachun, Kazanin, Haböck. *Failure of proximity gaps close to capacity*. ePrint 2026/782,
  Lemma 1.
-/

open Polynomial

namespace CodingTheory.AdditiveSetListDecoding

/-- The sum set `Λ_𝒮 := {∑_{α ∈ S} α : S ∈ 𝒮}` of a family of finite sets. -/
def sumSet {F : Type*} [CommRing F] [DecidableEq F] (𝒮 : Finset (Finset F)) : Finset F :=
  𝒮.image fun S => ∑ α ∈ S, α

private def KKHSignedChoice (n k : ℕ) :=
  Σ I : {I : Finset (Fin n) // I.card = k}, I.1 → Bool

private theorem kkh_card_signedChoice (n k : ℕ) :
    Nat.card (KKHSignedChoice n k) = 2 ^ k * n.choose k := by
  classical
  rw [KKHSignedChoice, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  have hsum : (∑ I : {I : Finset (Fin n) // I.card = k}, 2 ^ I.1.card)
      = ∑ _I : {I : Finset (Fin n) // I.card = k}, 2 ^ k := by
    apply Finset.sum_congr rfl
    intro I _
    rw [I.2]
  rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_finset_len,
    Fintype.card_fin]
  simp only [nsmul_eq_mul]
  ac_rfl

private theorem kkh_exists_generator {q h : ℕ} [Fact q.Prime] (H : Subgroup (ZMod q)ˣ)
    (hHcard : Nat.card H = h) : ∃ g : H, orderOf g = h := by
  letI : IsCyclic H := isCyclic_subgroup_units H
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
  exact ⟨g, hg.trans hHcard⟩

private theorem kkh_generator_half_pow {q h : ℕ} [Fact q.Prime] (g : (ZMod q)ˣ)
    (hg : orderOf g = h) (hh : 2 ≤ h) (heven : Even h) :
    g ^ (h / 2) = -1 := by
  have hsq : (g ^ (h / 2)) ^ 2 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel heven.two_dvd]
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hne : g ^ (h / 2) ≠ 1 := by
    intro heq
    have hdvd := orderOf_dvd_of_pow_eq_one heq
    rw [hg] at hdvd
    have hhalfpos : 0 < h / 2 := by omega
    have hhalflt : h / 2 < h := by omega
    exact (Nat.not_dvd_of_pos_of_lt hhalfpos hhalflt) hdvd
  have hsqval : (((g ^ (h / 2) : (ZMod q)ˣ) : ZMod q) ^ 2) = 1 := by
    exact congrArg Units.val hsq
  rcases (sq_eq_one_iff.mp hsqval) with hone | hneg
  · exact absurd (Units.ext hone) hne
  · exact Units.ext hneg

private theorem kkh_pow_two_arithmetic {h khat : ℕ} (hpow2 : ∃ m : ℕ, h = 2 ^ m)
    (hk1 : 1 ≤ khat) (hk2 : khat ≤ h / 2) :
    2 ≤ h ∧ Even h ∧ 2 * (h / 2) = h ∧ Nat.totient h = h / 2 := by
  obtain ⟨m, rfl⟩ := hpow2
  cases m with
  | zero =>
      norm_num at hk2
      omega
  | succ r =>
      have hhalf : 2 ^ (Nat.succ r) / 2 = 2 ^ r := by
        rw [pow_succ]
        omega
      refine ⟨by omega, ?_, ?_, ?_⟩
      · exact ⟨2 ^ r, by rw [pow_succ]; omega⟩
      · rw [hhalf]
        rw [pow_succ]
        omega
      · rw [Nat.totient_prime_pow_succ Nat.prime_two r, hhalf]
        norm_num

/-- Let `H` be a multiplicative subgroup of a prime field `𝔽_q` with `|H| = h` a power of two.
If `q > h^{h/2}`, then for any `1 ≤ k̂ ≤ h/2`, the family of all `k̂`-subsets of `H` satisfies
`|Λ_𝒮| ≥ 2^k̂ · C(h/2, k̂)` [KKH26, Lemma 1].

The proof embeds the `2^k̂ · C(h/2, k̂)` signed subset-sums of a generator's powers into `Λ_𝒮`;
injectivity follows from a resultant/root-of-unity argument bounding the coefficients of the
associated `±1`-valued polynomials against the cyclotomic polynomial `Φ_h`. -/
theorem two_pow_mul_choose_le_card_sumSet {q : ℕ} [Fact q.Prime] {h khat : ℕ}
    (H : Subgroup (ZMod q)ˣ) (hHcard : Nat.card H = h)
    (hpow2 : ∃ m : ℕ, h = 2 ^ m) (hq : h ^ (h / 2) < q)
    (hk1 : 1 ≤ khat) (hk2 : khat ≤ h / 2) :
    2 ^ khat * (h / 2).choose khat ≤
      (sumSet ((Set.toFinite
        ((fun u : (ZMod q)ˣ => (u : ZMod q)) '' (H : Set (ZMod q)ˣ))).toFinset.powersetCard
          khat)).card := by
  classical
  obtain ⟨h2, heven, hdouble, htot⟩ := kkh_pow_two_arithmetic hpow2 hk1 hk2
  have hhpos : 0 < h / 2 := by omega
  have hhpos' : 0 < h := by omega
  obtain ⟨m, hm⟩ := hpow2
  have hmpos : 0 < m := by
    cases m with
    | zero => norm_num at hm; omega
    | succ r => omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
  have hhpow : h = 2 ^ (r + 1) := by rw [hm, hr]
  have hd' : 2 ^ (r + 1) / 2 = 2 ^ r := by
    rw [pow_succ]
    omega
  have hcyclo : cyclotomic h ℤ = X ^ (h / 2) + 1 := by
    rw [hhpow, hd', cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
    norm_num [Finset.sum_range_succ]
    ac_rfl
  obtain ⟨g, hg⟩ := kkh_exists_generator H hHcard
  have hg' : orderOf (g : (ZMod q)ˣ) = h := (Subgroup.orderOf_coe g).trans hg
  have ghalf : ((g : (ZMod q)ˣ) ^ (h / 2)) = -1 :=
    kkh_generator_half_pow (g : (ZMod q)ˣ) hg' h2 heven
  let gv : ZMod q := ((g : (ZMod q)ˣ) : ZMod q)
  have gvhalf : gv ^ (h / 2) = -1 := by
    have hval := congrArg Units.val ghalf
    simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, gv] using hval
  have hpowsign (i : ℕ) (b : Bool) :
      (((g ^ (i + if b then h / 2 else 0) : H) : (ZMod q)ˣ) : ZMod q) =
        if b then -(gv ^ i) else gv ^ i := by
    cases b with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero, Subgroup.coe_pow,
          Units.val_pow_eq_pow_val, gv]
    | true =>
        simp only [↓reduceIte]
        rw [pow_add]
        change ((((g : H) : (ZMod q)ˣ) ^ i * ((g : H) : (ZMod q)ˣ) ^ (h / 2) :
          (ZMod q)ˣ) : ZMod q) = -(gv ^ i)
        rw [ghalf]
        simp only [mul_neg, mul_one, Units.val_neg, Units.val_pow_eq_pow_val, gv]
  let pick : KKHSignedChoice (h / 2) khat → Finset (ZMod q) := fun ⟨I, eps⟩ =>
    I.1.attach.image fun i =>
      (((g ^ (i.1.val + if eps i then h / 2 else 0) : H) : (ZMod q)ˣ) : ZMod q)
  have hpickinj (x : KKHSignedChoice (h / 2) khat) :
      Set.InjOn (fun i : {j // j ∈ x.1.1} =>
        (((g ^ (i.1.val + if x.2 i then h / 2 else 0) : H) : (ZMod q)ˣ) : ZMod q))
        ↑x.1.1.attach := by
    intro i hi j hj hij
    have hpows : g ^ (i.1.val + if x.2 i then h / 2 else 0) =
        g ^ (j.1.val + if x.2 j then h / 2 else 0) := by
      apply Subtype.ext
      apply Units.ext
      exact hij
    have hei : i.1.val + (if x.2 i then h / 2 else 0) < orderOf g := by
      rw [hg]
      have hi' := i.1.isLt
      split <;> omega
    have hej : j.1.val + (if x.2 j then h / 2 else 0) < orderOf g := by
      rw [hg]
      have hj' := j.1.isLt
      split <;> omega
    have heq := pow_injOn_Iio_orderOf hei hej hpows
    apply Subtype.ext
    apply Fin.ext
    by_cases bi : x.2 i <;> by_cases bj : x.2 j <;>
      simp only [bi, bj, Bool.false_eq_true, ↓reduceIte] at heq <;>
      have hi' := i.1.isLt <;> have hj' := j.1.isLt <;> omega
  have hpickcard (x : KKHSignedChoice (h / 2) khat) : (pick x).card = khat := by
    change (x.1.1.attach.image fun i =>
      (((g ^ (i.1.val + if x.2 i then h / 2 else 0) : H) : (ZMod q)ˣ) : ZMod q)).card = khat
    rw [Finset.card_image_of_injOn (hpickinj x), Finset.card_attach, x.1.2]
  let base : Finset (ZMod q) := (Set.toFinite
    ((fun u : (ZMod q)ˣ => (u : ZMod q)) '' (H : Set (ZMod q)ˣ))).toFinset
  have hpicksub (x : KKHSignedChoice (h / 2) khat) : pick x ⊆ base := by
    intro y hy
    change y ∈ (x.1.1.attach.image fun i =>
      (((g ^ (i.1.val + if x.2 i then h / 2 else 0) : H) : (ZMod q)ˣ) : ZMod q)) at hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    simp only [base, Set.Finite.mem_toFinset, Set.mem_image]
    exact ⟨((g ^ (i.1.val + if x.2 i then h / 2 else 0) : H) : (ZMod q)ˣ),
      (g ^ (i.1.val + if x.2 i then h / 2 else 0)).2, rfl⟩
  have hpickmem (x : KKHSignedChoice (h / 2) khat) : pick x ∈ base.powersetCard khat := by
    rw [Finset.mem_powersetCard]
    exact ⟨hpicksub x, hpickcard x⟩
  let sigma : KKHSignedChoice (h / 2) khat → ZMod q := fun x => ∑ y ∈ pick x, y
  have hsigmamem (x : KKHSignedChoice (h / 2) khat) :
      sigma x ∈ sumSet (base.powersetCard khat) := by
    rw [sumSet, Finset.mem_image]
    exact ⟨pick x, hpickmem x, rfl⟩
  have hsigned (x : KKHSignedChoice (h / 2) khat) : sigma x =
      ∑ i ∈ x.1.1.attach, if x.2 i then -(gv ^ i.1.val) else gv ^ i.1.val := by
    change (∑ y ∈ (x.1.1.attach.image fun i =>
      (((g ^ (i.1.val + if x.2 i then h / 2 else 0) : H) : (ZMod q)ˣ) : ZMod q)), y) = _
    rw [Finset.sum_image (hpickinj x)]
    apply Finset.sum_congr rfl
    intro i hi
    exact hpowsign i.1.val (x.2 i)
  let P : KKHSignedChoice (h / 2) khat → ℤ[X] := fun x =>
    ∑ i ∈ x.1.1.attach, C (if x.2 i then (-1 : ℤ) else 1) * X ^ i.1.val
  have hPeval (x : KKHSignedChoice (h / 2) khat) :
      ((P x).map (Int.castRingHom (ZMod q))).eval gv =
        ∑ i ∈ x.1.1.attach, if x.2 i then -(gv ^ i.1.val) else gv ^ i.1.val := by
    rcases x with ⟨⟨I, hI⟩, eps⟩
    change (Polynomial.map (Int.castRingHom (ZMod q))
      (∑ i ∈ I.attach, C (if eps i then (-1 : ℤ) else 1) * X ^ i.1.val)).eval gv = _
    rw [Polynomial.map_sum, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i hi
    split <;> simp
  have hPdeg (x : KKHSignedChoice (h / 2) khat) : (P x).natDegree < h / 2 := by
    rcases x with ⟨⟨I, hI⟩, eps⟩
    change (∑ i ∈ I.attach, C (if eps i then (-1 : ℤ) else 1) * X ^ i.1.val).natDegree < h / 2
    have hle : (∑ i ∈ I.attach,
        C (if eps i then (-1 : ℤ) else 1) * X ^ i.1.val).natDegree ≤ h / 2 - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      have hi' := i.1.isLt
      cases hb : eps i <;> simp <;> omega
    omega
  have hcoeff_mem (I : Finset (Fin (h / 2))) (eps : I → Bool)
      (a : Fin (h / 2)) (ha : a ∈ I) :
      (∑ i ∈ I.attach, C (if eps i then (-1 : ℤ) else 1) * X ^ i.1.val).coeff a.val =
        (if eps ⟨a, ha⟩ then (-1 : ℤ) else 1) := by
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single ⟨a, ha⟩]
    · rw [Polynomial.coeff_C_mul_X_pow]
      simp
    · intro b hb hba
      rw [Polynomial.coeff_C_mul_X_pow]
      have hne : a.val ≠ b.1.val := by
        intro hab
        apply hba
        apply Subtype.ext
        apply Fin.ext
        exact hab.symm
      simp [hne]
    · simp
  have hcoeff_not_mem (I : Finset (Fin (h / 2))) (eps : I → Bool)
      (a : Fin (h / 2)) (ha : a ∉ I) :
      (∑ i ∈ I.attach, C (if eps i then (-1 : ℤ) else 1) * X ^ i.1.val).coeff a.val = 0 := by
    rw [Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Polynomial.coeff_C_mul_X_pow]
    have hne : a.val ≠ b.1.val := by
      intro hab
      apply ha
      have heq : a = b.1 := Fin.ext hab
      exact heq ▸ b.2
    simp [hne]
  have hPinj : Function.Injective P := by
    intro x y hxy
    rcases x with ⟨⟨I, hI⟩, eps⟩
    rcases y with ⟨⟨J, hJ⟩, eta⟩
    have hIJ : I = J := by
      ext a
      constructor
      · intro haI
        by_contra haJ
        have hc := congrArg (fun p : ℤ[X] => p.coeff a.val) hxy
        simp only [P] at hc
        rw [hcoeff_mem I eps a haI, hcoeff_not_mem J eta a haJ] at hc
        cases hb : eps ⟨a, haI⟩ <;> simp [hb] at hc
      · intro haJ
        by_contra haI
        have hc := congrArg (fun p : ℤ[X] => p.coeff a.val) hxy
        simp only [P] at hc
        rw [hcoeff_not_mem I eps a haI, hcoeff_mem J eta a haJ] at hc
        cases hb : eta ⟨a, haJ⟩ <;> simp [hb] at hc
    subst J
    have hh : hI = hJ := Subsingleton.elim _ _
    subst hJ
    congr 2
    funext i
    have hc := congrArg (fun p : ℤ[X] => p.coeff i.1.val) hxy
    simp only [P] at hc
    rw [hcoeff_mem I eps i.1 i.2, hcoeff_mem I eta i.1 i.2] at hc
    cases he : eps i <;> cases hf : eta i <;> simp [he, hf] at hc ⊢
  have hPevalC (x : KKHSignedChoice (h / 2) khat) (z : ℂ) :
      ((P x).map (Int.castRingHom ℂ)).eval z =
        ∑ i ∈ x.1.1.attach, if x.2 i then -(z ^ i.1.val) else z ^ i.1.val := by
    rcases x with ⟨⟨I, hI⟩, eps⟩
    change (Polynomial.map (Int.castRingHom ℂ)
      (∑ i ∈ I.attach, C (if eps i then (-1 : ℤ) else 1) * X ^ i.1.val)).eval z = _
    rw [Polynomial.map_sum, Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i hi
    split <;> simp
  have hPnorm (x : KKHSignedChoice (h / 2) khat) (z : ℂ) (hz : ‖z‖ = 1) :
      ‖((P x).map (Int.castRingHom ℂ)).eval z‖ ≤ (khat : ℝ) := by
    rcases x with ⟨⟨I, hI⟩, eps⟩
    rw [hPevalC]
    calc
      ‖∑ i ∈ I.attach, if eps i then -(z ^ i.1.val) else z ^ i.1.val‖
          ≤ ∑ i ∈ I.attach,
              ‖if eps i then -(z ^ i.1.val) else z ^ i.1.val‖ := norm_sum_le _ _
      _ = ∑ _i ∈ I.attach, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        split <;> simp [norm_pow, hz]
      _ = (khat : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_attach, hI]
        norm_num
  let PhiC : ℂ[X] := (cyclotomic h ℤ).map (Int.castRingHom ℂ)
  have hPhiCne : PhiC ≠ 0 := by
    change (cyclotomic h ℤ).map (Int.castRingHom ℂ) ≠ 0
    rw [(Polynomial.int_cyclotomic_spec h).1]
    exact Polynomial.cyclotomic'_ne_zero h ℂ
  have hPhiCsplit : PhiC.Splits := by
    change ((cyclotomic h ℤ).map (Int.castRingHom ℂ)).Splits
    rw [(Polynomial.int_cyclotomic_spec h).1]
    exact Polynomial.cyclotomic'_splits h
  have hPhiCnat : PhiC.natDegree = h / 2 := by
    change ((cyclotomic h ℤ).map (Int.castRingHom ℂ)).natDegree = h / 2
    rw [(Polynomial.int_cyclotomic_spec h).1,
      Polynomial.natDegree_cyclotomic' (Complex.isPrimitiveRoot_exp h hhpos'.ne'), htot]
  have hPhiCmonic : PhiC.Monic := by
    change ((cyclotomic h ℤ).map (Int.castRingHom ℂ)).Monic
    exact (Polynomial.cyclotomic.monic h ℤ).map _
  have hrootnorm : ∀ z ∈ PhiC.roots, ‖z‖ = 1 := by
    intro z hz
    have heval : PhiC.eval z = 0 := (Polynomial.mem_roots hPhiCne).mp hz
    have hzhalf : z ^ (h / 2) = -1 := by
      change ((cyclotomic h ℤ).map (Int.castRingHom ℂ)).eval z = 0 at heval
      rw [hcyclo, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_one, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one] at heval
      exact eq_neg_of_add_eq_zero_left heval
    have hzh : z ^ h = 1 := by
      rw [← hdouble, mul_comm, pow_mul, hzhalf]
      norm_num
    exact Complex.norm_eq_one_of_pow_eq_one hzh hhpos'.ne'
  have hRnorm (x y : KKHSignedChoice (h / 2) khat) (z : ℂ) (hz : ‖z‖ = 1) :
      ‖((P x - P y).map (Int.castRingHom ℂ)).eval z‖ ≤ (h : ℝ) := by
    rw [Polynomial.map_sub, Polynomial.eval_sub]
    calc
      ‖((P x).map (Int.castRingHom ℂ)).eval z -
          ((P y).map (Int.castRingHom ℂ)).eval z‖
          ≤ ‖((P x).map (Int.castRingHom ℂ)).eval z‖ +
            ‖((P y).map (Int.castRingHom ℂ)).eval z‖ := norm_sub_le _ _
      _ ≤ (khat : ℝ) + khat := add_le_add (hPnorm x z hz) (hPnorm y z hz)
      _ ≤ (h : ℝ) := by exact_mod_cast (show khat + khat ≤ h by omega)
  have hprodBound (x y : KKHSignedChoice (h / 2) khat) :
      ‖(PhiC.roots.map (fun z => ((P x - P y).map (Int.castRingHom ℂ)).eval z)).prod‖
        ≤ (h : ℝ) ^ PhiC.roots.card := by
    let f : ℂ → ℂ := fun z => ((P x - P y).map (Int.castRingHom ℂ)).eval z
    have hind : ∀ s : Multiset ℂ, (∀ z ∈ s, ‖z‖ = 1) →
        ‖(s.map f).prod‖ ≤ (h : ℝ) ^ s.card := by
      intro s hs
      induction s using Multiset.induction_on with
      | empty => simp
      | @cons z s ih =>
          have hz : ‖z‖ = 1 := hs z (by simp)
          have hs' : ∀ w ∈ s, ‖w‖ = 1 := by
            intro w hw
            exact hs w (by simp [hw])
          rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]
          calc
            ‖f z‖ * ‖(Multiset.map f s).prod‖
                ≤ (h : ℝ) * ‖(Multiset.map f s).prod‖ := by
                  gcongr
                  exact hRnorm x y z hz
            _ ≤ (h : ℝ) * ((h : ℝ) ^ s.card) := by
                  gcongr
                  exact ih hs'
            _ = (h : ℝ) ^ s.card * h := by ring
    exact hind PhiC.roots hrootnorm
  have hresultant_dvd (x y : KKHSignedChoice (h / 2) khat)
      (heval : ((P x).map (Int.castRingHom (ZMod q))).eval gv =
        ((P y).map (Int.castRingHom (ZMod q))).eval gv) :
      (q : ℤ) ∣ (cyclotomic h ℤ).resultant (P x - P y) (h / 2) (h / 2) := by
    have hRdeg : (P x - P y).natDegree ≤ h / 2 := by
      refine (Polynomial.natDegree_sub_le _ _).trans ?_
      exact max_le (hPdeg x).le (hPdeg y).le
    have hPhideg : (cyclotomic h ℤ).natDegree ≤ h / 2 := by
      rw [Polynomial.natDegree_cyclotomic, htot]
    have hPhiEval : (((cyclotomic h ℤ).map (Int.castRingHom (ZMod q))).eval gv) = 0 := by
      rw [hcyclo, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
        Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        gvhalf, neg_add_cancel]
    have hREval : (((P x - P y).map (Int.castRingHom (ZMod q))).eval gv) = 0 := by
      rw [Polynomial.map_sub, Polynomial.eval_sub, heval, sub_self]
    obtain ⟨A, B, hA, hB, hbez⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
      (cyclotomic h ℤ) (P x - P y) hPhideg hRdeg (Or.inl hhpos.ne')
    have hc := congrArg (fun T : ℤ[X] =>
      ((T.map (Int.castRingHom (ZMod q))).eval gv)) hbez
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      hPhiEval, hREval, zero_mul, zero_mul, zero_add] at hc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc.symm
  have hresultant_norm (x y : KKHSignedChoice (h / 2) khat) :
      ‖(((cyclotomic h ℤ).resultant (P x - P y) (h / 2) (h / 2) : ℤ) : ℂ)‖
        ≤ (h : ℝ) ^ (h / 2) := by
    have hRdeg : ((P x - P y).map (Int.castRingHom ℂ)).natDegree ≤ h / 2 := by
      exact Polynomial.natDegree_map_le.trans
        ((Polynomial.natDegree_sub_le _ _).trans (max_le (hPdeg x).le (hPdeg y).le))
    have hresmap := Polynomial.resultant_map_map (f := cyclotomic h ℤ)
      (g := P x - P y) (m := h / 2) (n := h / 2) (Int.castRingHom ℂ)
    have hresmap' :
        (((cyclotomic h ℤ).resultant (P x - P y) (h / 2) (h / 2) : ℤ) : ℂ) =
          PhiC.resultant ((P x - P y).map (Int.castRingHom ℂ)) (h / 2) (h / 2) := by
      change (Int.castRingHom ℂ) ((cyclotomic h ℤ).resultant
        (P x - P y) (h / 2) (h / 2)) = _
      exact hresmap.symm
    have hprod := Polynomial.resultant_eq_prod_eval PhiC
      ((P x - P y).map (Int.castRingHom ℂ)) (h / 2) hRdeg hPhiCsplit
    rw [hPhiCnat] at hprod
    have hb := hprodBound x y
    rw [← hPhiCsplit.natDegree_eq_card_roots, hPhiCnat] at hb
    rw [hresmap', hprod, hPhiCmonic.leadingCoeff, one_pow, one_mul]
    exact hb
  have hzero_of_dvd_norm (a : ℤ) (hdvd : (q : ℤ) ∣ a)
      (hnorm : ‖(a : ℂ)‖ ≤ (h : ℝ) ^ (h / 2)) : a = 0 := by
    have hnatabs : a.natAbs ≤ h ^ (h / 2) := by
      rw [Complex.norm_intCast, ← Int.cast_abs, ← Nat.cast_natAbs] at hnorm
      exact_mod_cast hnorm
    by_contra ha
    have hqle : q ≤ a.natAbs := by
      have hle := Int.natAbs_le_of_dvd_ne_zero hdvd ha
      simpa using hle
    omega
  have hRzero_of_resultant (x y : KKHSignedChoice (h / 2) khat)
      (hreszero : (cyclotomic h ℤ).resultant (P x - P y) (h / 2) (h / 2) = 0) :
      P x - P y = 0 := by
    let RZ : ℤ[X] := P x - P y
    let RC : ℂ[X] := RZ.map (Int.castRingHom ℂ)
    have hRCdeg : RC.natDegree ≤ h / 2 := by
      exact Polynomial.natDegree_map_le.trans
        ((Polynomial.natDegree_sub_le _ _).trans (max_le (hPdeg x).le (hPdeg y).le))
    have hpadded := Polynomial.resultant_eq_prod_eval PhiC RC (h / 2) hRCdeg hPhiCsplit
    rw [hPhiCnat, hPhiCmonic.leadingCoeff, one_pow, one_mul] at hpadded
    have hstandard := Polynomial.resultant_eq_prod_eval PhiC RC RC.natDegree le_rfl hPhiCsplit
    rw [hPhiCmonic.leadingCoeff, one_pow, one_mul] at hstandard
    have hresmap := Polynomial.resultant_map_map (f := cyclotomic h ℤ) (g := RZ)
      (m := h / 2) (n := h / 2) (Int.castRingHom ℂ)
    have hpaddedzero : PhiC.resultant RC (h / 2) (h / 2) = 0 := by
      change ((cyclotomic h ℤ).map (Int.castRingHom ℂ)).resultant
        (RZ.map (Int.castRingHom ℂ)) (h / 2) (h / 2) = 0
      rw [hresmap, hreszero, map_zero]
    have hstdzero : PhiC.resultant RC = 0 := by
      rw [hstandard, ← hpadded, hpaddedzero]
    have hnotcopC : ¬IsCoprime PhiC RC := (Polynomial.resultant_eq_zero_iff.mp hstdzero).2
    let PhiQ : ℚ[X] := cyclotomic h ℚ
    let RQ : ℚ[X] := RZ.map (Int.castRingHom ℚ)
    have hcomp : (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
      ext n
      norm_num
    have hnotcopQ : ¬IsCoprime PhiQ RQ := by
      intro hcop
      have hcopC := (Polynomial.isCoprime_map (p := PhiQ) (q := RQ)
        (Rat.castHom ℂ)).2 hcop
      apply hnotcopC
      convert hcopC using 1 <;>
        simp only [PhiQ, RQ, PhiC, RC, RZ, Polynomial.map_cyclotomic,
          Polynomial.map_map, hcomp]
    have hdivQ : PhiQ ∣ RQ :=
      (Irreducible.dvd_iff_not_isCoprime (Polynomial.cyclotomic.irreducible_rat hhpos')).2 hnotcopQ
    have hRQzero : RQ = 0 := by
      by_contra hne
      have hdegdiv := Polynomial.natDegree_le_of_dvd hdivQ hne
      have hPhiQdeg : PhiQ.natDegree = h / 2 := by
        change (cyclotomic h ℚ).natDegree = h / 2
        rw [Polynomial.natDegree_cyclotomic, htot]
      have hRQdeg : RQ.natDegree < h / 2 := by
        exact lt_of_le_of_lt Polynomial.natDegree_map_le
          ((Polynomial.natDegree_sub_le _ _).trans_lt
            (max_lt (hPdeg x) (hPdeg y)))
      omega
    have hcastinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
    exact (Polynomial.map_eq_zero_iff hcastinj).mp hRQzero
  have hsigmainj : Function.Injective sigma := by
    intro x y hxy
    have heval : ((P x).map (Int.castRingHom (ZMod q))).eval gv =
        ((P y).map (Int.castRingHom (ZMod q))).eval gv := by
      rw [hPeval, hPeval, ← hsigned, ← hsigned, hxy]
    have hdvd := hresultant_dvd x y heval
    have hnorm := hresultant_norm x y
    have hreszero := hzero_of_dvd_norm
      ((cyclotomic h ℤ).resultant (P x - P y) (h / 2) (h / 2)) hdvd hnorm
    have hRzero := hRzero_of_resultant x y hreszero
    apply hPinj
    exact sub_eq_zero.mp hRzero
  letI : Fintype (KKHSignedChoice (h / 2) khat) := by
    unfold KKHSignedChoice
    infer_instance
  have hcardim : Fintype.card (KKHSignedChoice (h / 2) khat) ≤
      (sumSet (base.powersetCard khat)).card := by
    let e : KKHSignedChoice (h / 2) khat ↪ ZMod q := ⟨sigma, hsigmainj⟩
    have hsub : Finset.univ.image e ⊆ sumSet (base.powersetCard khat) := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨x, -, rfl⟩ := hy
      exact hsigmamem x
    calc
      Fintype.card (KKHSignedChoice (h / 2) khat) = Finset.univ.card := Finset.card_univ.symm
      _ = (Finset.univ.image e).card :=
        (Finset.card_image_of_injective _ e.injective).symm
      _ ≤ (sumSet (base.powersetCard khat)).card := Finset.card_le_card hsub
  calc
    2 ^ khat * (h / 2).choose khat = Nat.card (KKHSignedChoice (h / 2) khat) :=
      (kkh_card_signedChoice (h / 2) khat).symm
    _ = Fintype.card (KKHSignedChoice (h / 2) khat) := Nat.card_eq_fintype_card
    _ ≤ (sumSet (base.powersetCard khat)).card := hcardim
    _ = (sumSet ((Set.toFinite
        ((fun u : (ZMod q)ˣ => (u : ZMod q)) '' (H : Set (ZMod q)ˣ))).toFinset.powersetCard
          khat)).card := by rfl

end CodingTheory.AdditiveSetListDecoding
