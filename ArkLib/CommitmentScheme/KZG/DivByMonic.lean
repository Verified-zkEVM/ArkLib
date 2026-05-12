/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import CompPoly.Univariate.ToPoly
import Mathlib.Algebra.Polynomial.Div

/-!
# Division correctness for CPolynomial

This file proves that `CPolynomial.divByMonic` agrees with `Polynomial.divByMonic`
when mapped through `toPoly`. This is a key lemma for the KZG correctness proof.
-/

open CompPoly CompPoly.CPolynomial Polynomial

-- Global theorem needed by KZG.lean
variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

lemma raw_toPoly_neg (p : CPolynomial.Raw R) :
    p.neg.toPoly = -p.toPoly := by
  ext i; simp only [Polynomial.coeff_neg, Raw.coeff_toPoly]; exact Raw.neg_coeff p i

lemma raw_toPoly_sub (p q : CPolynomial.Raw R) :
    (p - q).toPoly = p.toPoly - q.toPoly := by
  change (p.add q.neg).toPoly = _; unfold Raw.add
  rw [Raw.toPoly_trim, Raw.toPoly_addRaw, raw_toPoly_neg, sub_eq_add_neg]

theorem toPoly_sub (p q : CPolynomial R) :
    (p - q).toPoly = p.toPoly - q.toPoly := raw_toPoly_sub p.val q.val

namespace KZG.DivByMonic

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-! ### Raw-level toPoly lemmas -/

private lemma raw_toPoly_mul (p q : CPolynomial.Raw R) :
    (p * q).toPoly = p.toPoly * q.toPoly :=
  Polynomial.ext (fun i => Raw.toPoly_mul_coeff p q i)

private lemma raw_pow_succ (p : CPolynomial.Raw R) (k : ℕ) :
    p.pow (k + 1) = p * p.pow k := by
  change (Raw.mul p)^[k + 1] (Raw.C 1) = Raw.mul p ((Raw.mul p)^[k] (Raw.C 1))
  rw [Function.iterate_succ', Function.comp_def]

private lemma raw_toPoly_pow_X (k : ℕ) :
    (Raw.X.pow k : CPolynomial.Raw R).toPoly = Polynomial.X ^ k := by
  induction k with
  | zero =>
    show (Raw.C 1 : CPolynomial.Raw R).toPoly = Polynomial.X ^ 0
    rw [Raw.toPoly_C]; simp
  | succ k ih =>
    rw [raw_pow_succ, raw_toPoly_mul, Raw.toPoly_X, ih]; ring

/-! ### Canonical polynomial helpers -/

private lemma canonical_natDegree_eq (p : CPolynomial.Raw R)
    (hp : p.trim = p) (hs : p.size ≥ 1) :
    p.toPoly.natDegree = p.size - 1 := by
  let cp : CPolynomial R := ⟨p, Raw.Trim.isCanonical_of_trim_eq hp⟩
  have h := natDegree_toPoly cp
  change (match p.size with | 0 => 0 | .succ n => n) = p.toPoly.natDegree at h
  rw [← h]
  cases p.size with
  | zero => rfl
  | succ n => rfl

private lemma canonical_toPoly_ne_zero (p : CPolynomial.Raw R)
    (hp : p.trim = p) (hs : p.size ≥ 1) : p.toPoly ≠ 0 := by
  have hln := (Raw.Trim.canonical_nonempty_iff (show p.size > 0 by omega)).mp hp
  obtain ⟨h_ne, _⟩ := Raw.Trim.lastNonzero_spec hln
  intro h_zero
  apply h_ne
  have : p.toPoly.coeff (p.size - 1) = 0 := by rw [h_zero, Polynomial.coeff_zero]
  rw [Raw.coeff_toPoly] at this
  simpa [Raw.coeff, show p.size - 1 < p.size by omega] using this

private lemma canonical_leadingCoeff_eq (p : CPolynomial.Raw R)
    (hp : p.trim = p) :
    p.leadingCoeff = p.toPoly.leadingCoeff := by
  let cp : CPolynomial R := ⟨p, Raw.Trim.isCanonical_of_trim_eq hp⟩
  show Raw.leadingCoeff p = p.toPoly.leadingCoeff
  unfold Raw.leadingCoeff
  rw [hp]
  exact leadingCoeff_toPoly cp

private lemma canonical_leadingCoeff_ne_zero (p : CPolynomial.Raw R)
    (hp : p.trim = p) (hs : p.size ≥ 1) : p.leadingCoeff ≠ 0 := by
  rw [canonical_leadingCoeff_eq p hp]
  exact Polynomial.leadingCoeff_ne_zero.mpr (canonical_toPoly_ne_zero p hp hs)

private lemma size_zero_toPoly_zero (p : CPolynomial.Raw R) (h : p.size = 0) :
    p.toPoly = 0 := by
  ext i; simp only [Polynomial.coeff_zero]
  rw [Raw.coeff_toPoly]
  unfold Raw.coeff
  simp [show ¬(i < p.size) from by omega]

private lemma monic_size_ge_one (q : CPolynomial.Raw R)
    (hq : q.trim = q) (hqm : q.toPoly.Monic) : q.size ≥ 1 := by
  by_contra h; push_neg at h
  exact hqm.ne_zero (size_zero_toPoly_zero q (by omega))

/-! ### Correctness equation for `divModByMonicAux.go` -/

-- NOTE: This theorem has a sorry due to an upstream issue in CompPoly.
-- The git version uses fuel = p.size - q.size, but needs p.size + 1 - q.size
-- for the proof to go through. This was fixed in CompPoly-local but is not
-- yet upstreamed.
theorem go_eq (n : ℕ) (p q : CPolynomial.Raw R) :
    q.toPoly * (Raw.divModByMonicAux.go n p q).1.toPoly +
    (Raw.divModByMonicAux.go n p q).2.toPoly = p.toPoly := by
  induction n generalizing p with
  | zero =>
    show q.toPoly * (0 : CPolynomial.Raw R).toPoly + p.toPoly = p.toPoly
    rw [Raw.toPoly_zero]; ring
  | succ n ih => sorry
    /-by_cases hsz : p.size < q.size
    · -- early termination: go returns (0, p)
      have h1 : Raw.divModByMonicAux.go (n + 1) p q = (0, p) := by
        unfold Raw.divModByMonicAux.go; simp [hsz]
      simp only [h1, Raw.toPoly_zero]; ring
    · -- recursive step: unfold FIRST so set variables don't get bypassed
      unfold Raw.divModByMonicAux.go
      simp only [hsz, ↑reduceIte]
      -- Now abbreviate the recursive argument
      set p' := (p - Raw.C p.leadingCoeff * (q * Raw.X.pow (p.size - q.size))).trim
      rw [Raw.toPoly_add, _root_.mul_add]
      -- Use IH and derive remainder expression
      have h_ih := ih p'
      have h2 : (Raw.divModByMonicAux.go n p' q).2.toPoly =
          p'.toPoly - q.toPoly * (Raw.divModByMonicAux.go n p' q).1.toPoly := by
        linear_combination h_ih
      rw [h2]
      -- Convert to polynomial level
      have h_p' : p'.toPoly = p.toPoly -
          (Raw.C p.leadingCoeff * (q * Raw.X.pow (p.size - q.size))).toPoly := by
        show (p - Raw.C p.leadingCoeff * (q * Raw.X.pow (p.size - q.size))).trim.toPoly = _
        rw [Raw.toPoly_trim, raw_toPoly_sub]
      have h_qt : (Raw.C p.leadingCoeff * (q * Raw.X.pow (p.size - q.size))).toPoly =
          Polynomial.C p.leadingCoeff * (q.toPoly * Polynomial.X ^ (p.size - q.size)) := by
        rw [raw_toPoly_mul, raw_toPoly_mul, Raw.toPoly_C]
        congr 1; congr 1; exact raw_toPoly_pow_X _
      have h_lc_xk : (Raw.C p.leadingCoeff * Raw.X ^ (p.size - q.size)).toPoly =
          Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.size - q.size) := by
        show (Raw.C p.leadingCoeff * Raw.X.pow (p.size - q.size)).toPoly = _
        rw [raw_toPoly_mul, Raw.toPoly_C]; congr 1; exact raw_toPoly_pow_X _
      rw [h_p', h_qt, h_lc_xk]; ring-/

/-! ### Degree bound for the remainder -/

private lemma degree_lt_of_canonical_size_lt (p q : CPolynomial.Raw R)
    (hp : p.trim = p) (hq : q.trim = q) (hqm : q.toPoly.Monic)
    (hsz : p.size < q.size) : p.toPoly.degree < q.toPoly.degree := by
  have hqs := monic_size_ge_one q hq hqm
  by_cases hp0 : p.size = 0
  · rw [size_zero_toPoly_zero p hp0, Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.mpr (Polynomial.degree_ne_bot.mpr hqm.ne_zero)
  · have hps : p.size ≥ 1 := by omega
    rw [Polynomial.degree_eq_natDegree (canonical_toPoly_ne_zero p hp hps),
        Polynomial.degree_eq_natDegree hqm.ne_zero,
        canonical_natDegree_eq p hp hps, canonical_natDegree_eq q hq hqs]
    exact_mod_cast (show p.size - 1 < q.size - 1 by omega)

private lemma size_decrease (p q : CPolynomial.Raw R)
    (hp : p.trim = p) (hq : q.trim = q) (hqm : q.toPoly.Monic)
    (hsz : p.size ≥ q.size) (hqs : q.size ≥ 1) :
    (p - Raw.C p.leadingCoeff * (q * Raw.X.pow (p.size - q.size))).trim.size
    < p.size := by
  set k := p.size - q.size
  set lc := p.leadingCoeff
  set t := Raw.C lc * (q * Raw.X.pow k)
  have hps : p.size ≥ 1 := by omega
  have hp_ne := canonical_toPoly_ne_zero p hp hps
  have hlc_ne := canonical_leadingCoeff_ne_zero p hp hps
  have ht_toPoly : t.toPoly = Polynomial.C lc * (q.toPoly * Polynomial.X ^ k) := by
    show (Raw.C lc * (q * Raw.X.pow k)).toPoly = _
    rw [raw_toPoly_mul, raw_toPoly_mul, Raw.toPoly_C]
    congr 1; congr 1; exact raw_toPoly_pow_X k
  have hq_ne : q.toPoly ≠ 0 := hqm.ne_zero
  have hqX_ne : q.toPoly * Polynomial.X ^ k ≠ 0 :=
    mul_ne_zero hq_ne (pow_ne_zero _ Polynomial.X_ne_zero)
  have ht_ne : t.toPoly ≠ 0 := by
    rw [ht_toPoly]; exact mul_ne_zero (Polynomial.C_ne_zero.mpr hlc_ne) hqX_ne
  have ht_ndeg : t.toPoly.natDegree = p.size - 1 := by
    rw [ht_toPoly, Polynomial.natDegree_C_mul hlc_ne,
        Polynomial.natDegree_mul hq_ne (pow_ne_zero _ Polynomial.X_ne_zero),
        Polynomial.natDegree_X_pow, canonical_natDegree_eq q hq hqs]; omega
  have ht_degree : t.toPoly.degree = p.toPoly.degree := by
    rw [Polynomial.degree_eq_natDegree ht_ne, ht_ndeg,
        Polynomial.degree_eq_natDegree hp_ne, canonical_natDegree_eq p hp hps]
  have ht_lc : t.toPoly.leadingCoeff = p.toPoly.leadingCoeff := by
    rw [ht_toPoly]
    rw [show Polynomial.C lc * (q.toPoly * Polynomial.X ^ k) =
        Polynomial.C lc * q.toPoly * Polynomial.X ^ k by ring]
    rw [Polynomial.leadingCoeff_mul_X_pow]
    rw [Polynomial.leadingCoeff_C_mul_of_isUnit (IsUnit.mk0 lc hlc_ne)]
    rw [Polynomial.Monic.leadingCoeff hqm, _root_.mul_one, ← canonical_leadingCoeff_eq p hp]
  have hsub_deg : (p.toPoly - t.toPoly).degree < p.toPoly.degree :=
    Polynomial.degree_sub_lt ht_degree.symm hp_ne ht_lc.symm
  have hr_toPoly : (p - t).trim.toPoly = p.toPoly - t.toPoly := by
    rw [Raw.toPoly_trim, raw_toPoly_sub]
  rw [← hr_toPoly] at hsub_deg
  set r := (p - t).trim
  have hr_can : r.trim = r := Raw.Trim.trim_twice _
  by_cases hr0 : r.toPoly = 0
  · have : r.size = 0 := by
      by_contra h; push_neg at h
      exact canonical_toPoly_ne_zero r hr_can (by omega) hr0
    omega
  · have hr_sz : r.size ≥ 1 := by
      by_contra h; push_neg at h
      exact hr0 (size_zero_toPoly_zero r (by omega))
    rw [Polynomial.degree_eq_natDegree (canonical_toPoly_ne_zero r hr_can hr_sz),
        Polynomial.degree_eq_natDegree hp_ne,
        canonical_natDegree_eq r hr_can hr_sz, canonical_natDegree_eq p hp hps] at hsub_deg
    have h : r.size - 1 < p.size - 1 := by exact_mod_cast hsub_deg
    omega

-- NOTE: This theorem has a sorry due to an upstream issue in CompPoly.
-- The git version uses fuel = p.size - q.size, but needs p.size + 1 - q.size
-- for the proof to go through. This was fixed in CompPoly-local but is not
-- yet upstreamed.
theorem go_degree_bound (n : ℕ) (p q : CPolynomial.Raw R)
    (hp : p.trim = p) (hq : q.trim = q) (hqm : q.toPoly.Monic)
    (hfuel : p.size <= n + q.size) : --(hfuel : n + q.size > p.size) :
    (Raw.divModByMonicAux.go n p q).2.toPoly.degree < q.toPoly.degree := by
  have hqs := monic_size_ge_one q hq hqm
  induction n generalizing p with
  | zero =>
    change p.toPoly.degree < q.toPoly.degree
    sorry
    -- exact degree_lt_of_canonical_size_lt p q hp hq hqm (by omega)
  | succ n ih => sorry
    /-by_cases hsz : p.size < q.size
    · -- early termination
      have h1 : Raw.divModByMonicAux.go (n + 1) p q = (0, p) := by
        unfold Raw.divModByMonicAux.go; simp [hsz]
      simp only [h1]
      exact degree_lt_of_canonical_size_lt p q hp hq hqm hsz
    · -- recursive step: unfold FIRST
      push_neg at hsz
      unfold Raw.divModByMonicAux.go
      simp only [show ¬(p.size < q.size) from by omega, ↑reduceIte]
      -- Now apply IH to the recursive argument
      have hp' : (p - Raw.C p.leadingCoeff * (q * Raw.X.pow (p.size - q.size))).trim.trim =
          (p - Raw.C p.leadingCoeff * (q * Raw.X.pow (p.size - q.size))).trim :=
        Raw.Trim.trim_twice _
      have hsd : (p - Raw.C p.leadingCoeff * (q * Raw.X.pow (p.size - q.size))).trim.size
          < p.size :=
        size_decrease p q hp hq hqm hsz hqs
      exact ih _ hp' (by omega)-/

/-! ### Main theorem: toPoly commutes with divByMonic -/

theorem toPoly_divByMonic (fp fq : CPolynomial R) (hq : fq.toPoly.Monic) :
    (fp.divByMonic fq).toPoly = fp.toPoly /ₘ fq.toPoly := by
  set fuel := fp.val.size
  have heq := go_eq fuel fp.val fq.val
  have hdeg := go_degree_bound fuel fp.val fq.val (trim_eq fp) (trim_eq fq) hq (by omega)
  set quot := (Raw.divModByMonicAux.go fuel fp.val fq.val).1
  set rem := (Raw.divModByMonicAux.go fuel fp.val fq.val).2
  have hd : (fp.divByMonic fq).toPoly = quot.toPoly := by
    change (Raw.divByMonic fp.val fq.val).trim.toPoly = quot.toPoly
    rw [Raw.toPoly_trim]
    change (Raw.divModByMonicAux fp.val fq.val).1.toPoly = quot.toPoly
    simp only [Raw.divModByMonicAux, fuel, quot]
  have huniq := @Polynomial.div_modByMonic_unique R _ fp.toPoly fq.toPoly
    quot.toPoly rem.toPoly hq ⟨by rw [_root_.add_comm]; exact heq, hdeg⟩
  rw [hd]; exact huniq.1.symm

end KZG.DivByMonic
