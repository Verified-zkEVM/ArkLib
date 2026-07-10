/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import CompPoly.Univariate.Basic
import CompPoly.Univariate.ToPoly
import Mathlib.Algebra.Polynomial.Div

/-!
  # Additions to `CompPoly.Univariate.Basic` not yet upstreamed to CompPoly.
-/

namespace CompPoly.CPolynomial

variable {R : Type*}

/-- Construct a canonical polynomial from a coefficient function `Fin n → R`.

  The coefficients are stored in an array (index `i` gives the coefficient of `X^i`)
  and then trimmed to remove trailing zeros.
-/
def ofFn [Zero R] [BEq R] [LawfulBEq R] {n : ℕ} (f : Fin n → R) : CPolynomial R :=
  ⟨(Raw.mk (Array.ofFn f)).trim, Raw.Trim.isCanonical_trim _⟩

/-- A `CPolynomial` coefficient past the stored `size` is `0` (`coeff` reads `Array.getD … 0`). -/
theorem coeff_eq_zero_of_size_le [Zero R] (p : CPolynomial R) {pos : ℕ} (h : p.size ≤ pos) :
    p.coeff pos = 0 := by
  change p.val.getD pos 0 = 0
  unfold Array.getD
  split_ifs with hh
  · exact absurd hh (Nat.not_lt.mpr h)
  · rfl

section DivisionToPoly

open Polynomial

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R]

/-! ### Helper lemmas for the theorem `toPoly_divByMonic` -/

private lemma Raw.toPoly_mul_eq (p q : CPolynomial.Raw R) :
    (p * q).toPoly = p.toPoly * q.toPoly := by
  ext i
  exact Raw.toPoly_mul_coeff p q i

private lemma Raw.toPoly_sub_eq (p q : CPolynomial.Raw R) :
    (p - q).toPoly = p.toPoly - q.toPoly := by
  ext i
  rw [Polynomial.coeff_sub, Raw.coeff_toPoly, Raw.coeff_toPoly, Raw.coeff_toPoly]
  exact Raw.sub_coeff p q i

private lemma Raw.toPoly_pow_eq (p : CPolynomial.Raw R) (n : ℕ) :
    (p ^ n).toPoly = p.toPoly ^ n := by
  induction n with
  | zero =>
    rw [Raw.pow_zero, Raw.toPoly_C]
    simp
  | succ n ih =>
    rw [Raw.pow_succ, Raw.toPoly_mul_eq, ih]
    exact (_root_.pow_succ' p.toPoly n).symm

private lemma Raw.toPoly_powFn_eq (p : CPolynomial.Raw R) (n : ℕ) :
    (Raw.pow p n).toPoly = p.toPoly ^ n :=
  Raw.toPoly_pow_eq p n

private lemma Raw.toPoly_degree_eq (p : CPolynomial.Raw R) (hp : p.trim = p) :
    p.toPoly.degree =
      match p.size with
      | 0 => ⊥
      | .succ n => n := by
  let cp : CPolynomial R := ⟨p, Raw.Trim.isCanonical_of_trim_eq hp⟩
  change cp.toPoly.degree =
    match cp.val.size with
    | 0 => ⊥
    | .succ n => n
  rw [← degree_toPoly cp]
  rfl

private lemma Raw.toPoly_natDegree_eq (p : CPolynomial.Raw R) (hp : p.trim = p) :
    p.toPoly.natDegree =
      match p.size with
      | 0 => 0
      | .succ n => n := by
  let cp : CPolynomial R := ⟨p, Raw.Trim.isCanonical_of_trim_eq hp⟩
  change cp.toPoly.natDegree =
    match cp.val.size with
    | 0 => 0
    | .succ n => n
  rw [← natDegree_toPoly cp]
  rfl

private lemma Raw.toPoly_natDegree_eq_size_sub_one (p : CPolynomial.Raw R)
    (hp : p.trim = p) (hsize : 0 < p.size) :
    p.toPoly.natDegree = p.size - 1 := by
  rw [Raw.toPoly_natDegree_eq p hp]
  cases hs : p.size with
  | zero => omega
  | succ n => simp

private lemma Raw.leadingCoeff_toPoly_eq (p : CPolynomial.Raw R) (hp : p.trim = p) :
    p.leadingCoeff = p.toPoly.leadingCoeff := by
  let cp : CPolynomial R := ⟨p, Raw.Trim.isCanonical_of_trim_eq hp⟩
  change p.trim.getLastD 0 = p.toPoly.leadingCoeff
  rw [hp]
  change cp.leadingCoeff = cp.toPoly.leadingCoeff
  exact leadingCoeff_toPoly cp

private lemma Raw.toPoly_ne_zero_of_size_pos {p : CPolynomial.Raw R}
    (hp : p.trim = p) (hsize : 0 < p.size) : p.toPoly ≠ 0 := by
  let cp : CPolynomial R := ⟨p, Raw.Trim.isCanonical_of_trim_eq hp⟩
  intro hp0
  have hcp0 : cp = 0 := by
    rw [← toPoly_eq_zero_iff cp]
    exact hp0
  have hp_empty : p = (#[] : CPolynomial.Raw R) := by
    simpa [cp] using congrArg Subtype.val hcp0
  have : p.size = 0 := by simpa using congrArg Array.size hp_empty
  omega

omit [BEq R] [LawfulBEq R] in
private lemma Raw.size_pos_of_toPoly_ne_zero {p : CPolynomial.Raw R}
    (hp0 : p.toPoly ≠ 0) : 0 < p.size := by
  by_contra h
  have hsize : p.size = 0 := Nat.eq_zero_of_not_pos h
  have hval : p = (#[] : CPolynomial.Raw R) := Array.eq_empty_of_size_eq_zero hsize
  exact hp0 (by simpa [hval] using (Raw.toPoly_zero (R := R)))

private lemma Raw.toPoly_degree_le_of_size_le {p q : CPolynomial.Raw R}
    (hp : p.trim = p) (hq : q.trim = q) (hsize : p.size ≤ q.size) :
    p.toPoly.degree ≤ q.toPoly.degree := by
  rw [Raw.toPoly_degree_eq p hp, Raw.toPoly_degree_eq q hq]
  cases hp_size : p.size <;> cases hq_size : q.size <;> simp_all

private lemma Raw.size_lt_of_toPoly_degree_lt {p q : CPolynomial.Raw R}
    (hp : p.trim = p) (hq : q.trim = q) (hdeg : q.toPoly.degree < p.toPoly.degree) :
    q.size < p.size := by
  rw [Raw.toPoly_degree_eq q hq, Raw.toPoly_degree_eq p hp] at hdeg
  cases hp_size : p.size <;> cases hq_size : q.size <;> simp_all

private lemma Raw.toPoly_degree_lt_of_size_lt {p q : CPolynomial.Raw R}
    (hp : p.trim = p) (hq : q.trim = q) (hsize : p.size < q.size) :
    p.toPoly.degree < q.toPoly.degree := by
  rw [Raw.toPoly_degree_eq p hp, Raw.toPoly_degree_eq q hq]
  cases hp_size : p.size <;> cases hq_size : q.size <;> simp_all

private lemma divModByMonicAux_step_degree_lt (p q : CPolynomial.Raw R)
    (hp : p.trim = p) (hq : q.trim = q) (hqm : q.toPoly.Monic)
    (hfits : q.size ≤ p.size) :
    ((p - Raw.C p.leadingCoeff * (q * Raw.X.pow (p.size - q.size))).trim).toPoly.degree <
      p.toPoly.degree := by
  have hq_size_pos : 0 < q.size := Raw.size_pos_of_toPoly_ne_zero hqm.ne_zero
  have hp_size_pos : 0 < p.size := hq_size_pos.trans_le hfits
  have hp_ne : p.toPoly ≠ 0 := Raw.toPoly_ne_zero_of_size_pos hp hp_size_pos
  have hdegree_le : q.toPoly.degree ≤ p.toPoly.degree :=
    Raw.toPoly_degree_le_of_size_le hq hp hfits
  have hdrop := Polynomial.div_wf_lemma
    (p := p.toPoly) (q := q.toPoly) ⟨hdegree_le, hp_ne⟩ hqm
  have hk : p.size - q.size = p.toPoly.natDegree - q.toPoly.natDegree := by
    rw [Raw.toPoly_natDegree_eq_size_sub_one p hp hp_size_pos,
      Raw.toPoly_natDegree_eq_size_sub_one q hq hq_size_pos]
    omega
  rw [Raw.toPoly_trim, Raw.toPoly_sub_eq, Raw.toPoly_mul_eq, Raw.toPoly_C,
    Raw.toPoly_mul_eq, Raw.toPoly_powFn_eq, Raw.toPoly_X,
    Raw.leadingCoeff_toPoly_eq p hp, hk]
  convert hdrop using 2
  ring

private lemma divModByMonicAux_go_eq (n : ℕ) (p q : CPolynomial.Raw R) :
    q.toPoly * (Raw.divModByMonicAux.go n p q).1.toPoly +
    (Raw.divModByMonicAux.go n p q).2.toPoly = p.toPoly := by
  induction n generalizing p with
  | zero =>
    change q.toPoly * (0 : CPolynomial.Raw R).toPoly + p.toPoly = p.toPoly
    rw [Raw.toPoly_zero]
    ring
  | succ n ih =>
    by_cases hlt : p.size < q.size
    · simp only [Raw.divModByMonicAux.go, hlt, ↓reduceIte]
      rw [Raw.toPoly_zero]
      ring
    · let k := p.size - q.size
      let q' := Raw.C p.leadingCoeff * (q * Raw.X.pow k)
      let p' := (p - q').trim
      have ih' := ih p'
      simp only [Raw.divModByMonicAux.go, hlt, ↓reduceIte]
      change q.toPoly *
            ((Raw.divModByMonicAux.go n p' q).1 +
              Raw.C p.leadingCoeff * Raw.X ^ k).toPoly +
          (Raw.divModByMonicAux.go n p' q).2.toPoly = p.toPoly
      rw [Raw.toPoly_add, Raw.toPoly_mul_eq, Raw.toPoly_C, Raw.toPoly_pow_eq,
        Raw.toPoly_X]
      set g := Raw.divModByMonicAux.go n p' q
      change q.toPoly * g.1.toPoly + g.2.toPoly = p'.toPoly at ih'
      calc
        q.toPoly * (g.1.toPoly + Polynomial.C p.leadingCoeff * Polynomial.X ^ k) +
            g.2.toPoly =
          (q.toPoly * g.1.toPoly + g.2.toPoly) +
            q.toPoly * (Polynomial.C p.leadingCoeff * Polynomial.X ^ k) := by
            ring
        _ = p'.toPoly +
            q.toPoly * (Polynomial.C p.leadingCoeff * Polynomial.X ^ k) := by
            rw [ih']
        _ = p.toPoly := by
          dsimp only [p', q', k]
          rw [Raw.toPoly_trim, Raw.toPoly_sub_eq, Raw.toPoly_mul_eq, Raw.toPoly_C,
            Raw.toPoly_mul_eq, Raw.toPoly_powFn_eq, Raw.toPoly_X]
          ring


private lemma divModByMonicAux_go_degree_bound (n : ℕ) (p q : CPolynomial.Raw R)
    (hp : p.trim = p) (hq : q.trim = q) (hqm : q.toPoly.Monic)
    (hfuel : p.size < n + q.size) :
    (Raw.divModByMonicAux.go n p q).2.toPoly.degree < q.toPoly.degree := by
  induction n generalizing p with
  | zero =>
    change p.toPoly.degree < q.toPoly.degree
    exact Raw.toPoly_degree_lt_of_size_lt hp hq (by simpa using hfuel)
  | succ n ih =>
    by_cases hlt : p.size < q.size
    · simp only [Raw.divModByMonicAux.go, hlt, ↓reduceIte]
      exact Raw.toPoly_degree_lt_of_size_lt hp hq hlt
    · let k := p.size - q.size
      let q' := Raw.C p.leadingCoeff * (q * Raw.X.pow k)
      let p' := (p - q').trim
      have hp' : p'.trim = p' := by
        dsimp only [p']
        exact Raw.Trim.trim_twice _
      have hfits : q.size ≤ p.size := Nat.le_of_not_gt hlt
      have hstep_degree : p'.toPoly.degree < p.toPoly.degree := by
        dsimp only [p', q', k]
        exact divModByMonicAux_step_degree_lt p q hp hq hqm hfits
      have hstep_size : p'.size < p.size :=
        Raw.size_lt_of_toPoly_degree_lt hp hp' hstep_degree
      have hfuel' : p'.size < n + q.size := by omega
      simp only [Raw.divModByMonicAux.go, hlt, ↓reduceIte]
      exact ih p' hp' hfuel'

/-! ### Main theorem: toPoly commutes with divByMonic -/

theorem toPoly_divByMonic (fp fq : CPolynomial R) (hq : fq.toPoly.Monic) :
    (fp.divByMonic fq).toPoly = fp.toPoly /ₘ fq.toPoly := by
  set fuel := fp.val.size
  have heq := divModByMonicAux_go_eq fuel fp.val fq.val
  have hdeg :=
    divModByMonicAux_go_degree_bound fuel fp.val fq.val (trim_eq fp) (trim_eq fq) hq
      (by
        have hq_size_pos : 0 < fq.val.size := Raw.size_pos_of_toPoly_ne_zero hq.ne_zero
        omega)
  set quot := (Raw.divModByMonicAux.go fuel fp.val fq.val).1
  set rem := (Raw.divModByMonicAux.go fuel fp.val fq.val).2
  have hd : (fp.divByMonic fq).toPoly = quot.toPoly := by
    change (Raw.divByMonic fp.val fq.val).toPoly = quot.toPoly
    change (Raw.divModByMonicAux fp.val fq.val).1.toPoly = quot.toPoly
    simp only [Raw.divModByMonicAux, fuel, quot]
  have huniq := @Polynomial.div_modByMonic_unique R _ fp.toPoly fq.toPoly
    quot.toPoly rem.toPoly hq ⟨by rw [_root_.add_comm]; exact heq, hdeg⟩
  rw [hd]
  exact huniq.1.symm

theorem toPoly_modByMonic (fp fq : CPolynomial R) (hq : fq.toPoly.Monic) :
    (fp.modByMonic fq).toPoly = fp.toPoly %ₘ fq.toPoly := by
  set fuel := fp.val.size
  have heq := divModByMonicAux_go_eq fuel fp.val fq.val
  have hdeg :=
    divModByMonicAux_go_degree_bound fuel fp.val fq.val (trim_eq fp) (trim_eq fq) hq
      (by
        have hq_size_pos : 0 < fq.val.size := Raw.size_pos_of_toPoly_ne_zero hq.ne_zero
        omega)
  set quot := (Raw.divModByMonicAux.go fuel fp.val fq.val).1
  set rem := (Raw.divModByMonicAux.go fuel fp.val fq.val).2
  have hd : (fp.modByMonic fq).toPoly = rem.toPoly := by
    change (Raw.modByMonic fp.val fq.val).toPoly = rem.toPoly
    change (Raw.divModByMonicAux fp.val fq.val).2.toPoly = rem.toPoly
    simp only [Raw.divModByMonicAux, fuel, rem]
  have huniq := @Polynomial.div_modByMonic_unique R _ fp.toPoly fq.toPoly
    quot.toPoly rem.toPoly hq ⟨by rw [_root_.add_comm]; exact heq, hdeg⟩
  rw [hd]
  exact huniq.2.symm

end DivisionToPoly

section OfFinCoeff

open Polynomial Finset

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R] [DecidableEq R] [Nontrivial R]

/-- Extracting the `k`-th coefficient as an additive homomorphism. -/
def coeffHom (k : ℕ) : CPolynomial R →+ R where
  toFun p := p.coeff k
  map_zero' := coeff_zero k
  map_add' p q := coeff_add p q k

omit [DecidableEq R] in
@[simp] theorem coeffHom_apply (k : ℕ) (p : CPolynomial R) : coeffHom k p = p.coeff k := rfl

/-- The polynomial with prescribed finite coefficient function: `Σ_{k<N} cₖ Xᵏ`. -/
def ofFinCoeff (N : ℕ) (c : ℕ → R) : CPolynomial R :=
  ∑ k ∈ range N, monomial k (c k)

@[simp] theorem coeff_ofFinCoeff (N : ℕ) (c : ℕ → R) (j : ℕ) :
    (ofFinCoeff N c).coeff j = if j < N then c j else 0 := by
  rw [ofFinCoeff,
    show (∑ k ∈ range N, monomial k (c k)).coeff j
        = ∑ k ∈ range N, (monomial k (c k)).coeff j from map_sum (coeffHom j) _ _]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq (range N) j (fun k => c k)]
  simp

omit [DecidableEq R] [Nontrivial R] in
/-- `toPoly` of a constant is the Mathlib constant. -/
theorem toPoly_C (c : R) : (C c).toPoly = Polynomial.C c := by
  ext i
  rw [show (C c).toPoly = (C c).val.toPoly from rfl, Raw.coeff_toPoly, Polynomial.coeff_C]
  exact coeff_C c i

omit [Nontrivial R] in
/-- `toPoly` of a monomial is the Mathlib monomial. -/
theorem toPoly_monomial (n : ℕ) (c : R) :
    (monomial n c).toPoly = Polynomial.monomial n c := by
  ext i
  rw [show (monomial n c).toPoly = (monomial n c).val.toPoly from rfl, Raw.coeff_toPoly,
    show (monomial n c).val.coeff i = (monomial n c).coeff i from rfl,
    coeff_monomial, Polynomial.coeff_monomial]
  exact if_congr eq_comm rfl rfl

omit [Nontrivial R] in
/-- The polynomial built from `N` coefficients has degree below `N`. -/
theorem degree_toPoly_ofFinCoeff_lt (N : ℕ) (c : ℕ → R) :
    (ofFinCoeff N c).toPoly.degree < (N : WithBot ℕ) := by
  rw [ofFinCoeff, toPoly_sum]
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _)
    ((Finset.sup_lt_iff (WithBot.bot_lt_coe N)).mpr (fun k hk => ?_))
  rw [toPoly_monomial]
  exact lt_of_le_of_lt (Polynomial.degree_monomial_le k (c k))
    (WithBot.coe_lt_coe.mpr (mem_range.mp hk))

omit [Nontrivial R] in
/-- A monomial with zero coefficient is the zero polynomial. -/
theorem monomial_eq_zero (n : ℕ) : (monomial n (0 : R) : CPolynomial R) = 0 :=
  eq_zero_iff_coeff_zero.mpr (fun j => by rw [coeff_monomial]; split_ifs <;> rfl)

end OfFinCoeff

end CompPoly.CPolynomial
