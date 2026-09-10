/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.DimensionBridge
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.IntermediateSpace


/-!
# Reachable coordinates of local interpolation

The weighted cutoff and total jet degree bound every reachable local coordinate. This
module derives those constraints and counts a finite space containing the image, without
a lower cutoff or characteristic assumption.

The displacement and error exponents satisfy `h ≤ i` and `i + d*h < m`. Writing `r = i-h`
gives the contact-slot count with denominator `d+1`. The remaining visible first-derivative
exponent is bounded using total degree minus the actual higher-jet degree.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

open scoped BigOperators Pointwise

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

/-- Finite coordinates in the proposed local image bound, with `r = i-h`.
This type counts possible coordinates; membership of the actual local image is a separate
proof obligation. In particular, its cardinality is not asserted to be an actual rank. -/
abbrev LocalCoordinateBudgetIndex (d m W Be : ℕ) :=
  Fin Be × (Σ r : Fin m,
    Fin ((m - r.val) ⌈/⌉ (d + 1)) × ↥(weightedHigherJetTuples d (W + r.val)))

/-- The manuscript's `T`-degree-sensitive numerical rank budget. -/
def localCoordinateBudget (d m W Be : ℕ) : ℕ :=
  Be * ∑ r ∈ Finset.range m,
    ((m - r) ⌈/⌉ (d + 1)) * weightedHigherJetCount d (W + r)

/-- Cardinality of the potential local-coordinate index, before proving image containment. -/
theorem card_localCoordinateBudgetIndex (d m W Be : ℕ) :
    Fintype.card (LocalCoordinateBudgetIndex d m W Be) =
      localCoordinateBudget d m W Be := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun r ↦ ((m - r) ⌈/⌉ (d + 1)) * weightedHigherJetCount d (W + r)) m


section SupportWeights

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
variable {σ τ : Type*}

omit [PartialOrder M] [IsOrderedAddMonoid M] in
private theorem support_weight_C_eq_zero (w : τ → M) (a : R)
    {e : τ →₀ ℕ} (he : e ∈ (C a : MvPolynomial τ R).support) :
    Finsupp.weight w e = 0 := by
  classical
  have he' : e ∈ ({0} : Finset (τ →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset he
  have : e = 0 := Finset.mem_singleton.mp he'
  subst e
  exact map_zero (Finsupp.weight w)

omit [PartialOrder M] [IsOrderedAddMonoid M] in
private theorem support_weight_X_eq (w : τ → M) (i : τ)
    {e : τ →₀ ℕ} (he : e ∈ (X i : MvPolynomial τ R).support) :
    Finsupp.weight w e = w i := by
  classical
  have he' : e ∈ ({Finsupp.single i 1} : Finset (τ →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset he
  have : e = Finsupp.single i 1 := Finset.mem_singleton.mp he'
  subst e
  rw [Finsupp.weight_single]
  exact one_nsmul (w i)

omit [IsOrderedAddMonoid M] in
private theorem support_weight_add_le (w : τ → M)
    {P Q : MvPolynomial τ R} {a : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a)
    (hQ : ∀ e ∈ Q.support, Finsupp.weight w e ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (P + Q).support) :
    Finsupp.weight w e ≤ a := by
  classical
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with heP | heQ
  · exact hP e heP
  · exact hQ e heQ

omit [IsOrderedAddMonoid M] in
private theorem support_weight_sum_le (w : τ → M)
    {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial τ R) {a : M}
    (hP : ∀ i ∈ s, ∀ e ∈ (P i).support, Finsupp.weight w e ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (s.sum P).support) :
    Finsupp.weight w e ≤ a := by
  classical
  have he' := MvPolynomial.support_sum he
  rcases Finset.mem_biUnion.mp he' with ⟨i, hi, hei⟩
  exact hP i hi e hei

private theorem support_weight_mul_le (w : τ → M)
    {P Q : MvPolynomial τ R} {a b : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a)
    (hQ : ∀ e ∈ Q.support, Finsupp.weight w e ≤ b)
    {e : τ →₀ ℕ} (he : e ∈ (P * Q).support) :
    Finsupp.weight w e ≤ a + b := by
  classical
  have he' : e ∈ P.support + Q.support := MvPolynomial.support_mul P Q he
  rcases Finset.mem_add.mp he' with ⟨eP, heP, eQ, heQ, rfl⟩
  simpa using add_le_add (hP eP heP) (hQ eQ heQ)

private theorem support_weight_pow_le (w : τ → M)
    {P : MvPolynomial τ R} {a : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a) (n : ℕ)
    {e : τ →₀ ℕ} (he : e ∈ (P ^ n).support) :
    Finsupp.weight w e ≤ n • a := by
  induction n generalizing e with
  | zero =>
      simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | succ n ih =>
      rw [pow_succ] at he
      simpa [succ_nsmul] using support_weight_mul_le w
        (fun e he => ih he) hP he

private theorem support_weight_prod_le (w : τ → M)
    {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial τ R) (a : ι → M)
    (hP : ∀ i ∈ s, ∀ e ∈ (P i).support, Finsupp.weight w e ≤ a i)
    {e : τ →₀ ℕ} (he : e ∈ (s.prod P).support) :
    Finsupp.weight w e ≤ s.sum a := by
  classical
  induction s using Finset.induction_on generalizing e with
  | empty =>
      simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi] at he
      rw [Finset.sum_insert hi]
      exact support_weight_mul_le w
        (hP i (Finset.mem_insert_self i s))
        (fun e he => ih
          (fun j hj => hP j (Finset.mem_insert_of_mem hj)) he) he

/-- Substitution cannot increase a support weight if every substituted
variable has support weight at most the weight assigned to that variable. -/
private theorem support_weight_bind₁_le (wSource : σ → M) (wTarget : τ → M)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, ∀ e ∈ (f i).support,
      Finsupp.weight wTarget e ≤ wSource i)
    {P : MvPolynomial σ R} {a : M}
    (hP : ∀ u ∈ P.support, Finsupp.weight wSource u ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (MvPolynomial.bind₁ f P).support) :
    Finsupp.weight wTarget e ≤ a := by
  classical
  rw [MvPolynomial.as_sum P, map_sum] at he
  have he' := MvPolynomial.support_sum he
  rcases Finset.mem_biUnion.mp he' with ⟨u, hu, heu⟩
  rw [MvPolynomial.bind₁_monomial] at heu
  have hprod : ∀ v ∈ (u.support.prod fun i => f i ^ u i).support,
      Finsupp.weight wTarget v ≤ Finsupp.weight wSource u := by
    intro v hv
    simpa only [Finsupp.weight_apply, Finsupp.sum] using
      (support_weight_prod_le wTarget u.support
        (fun i => f i ^ u i) (fun i => u i • wSource i)
        (fun i hi v hv => support_weight_pow_le wTarget (hf i) (u i) hv) hv)
  have hmul := support_weight_mul_le wTarget
    (a := (0 : M)) (b := Finsupp.weight wSource u)
    (fun v hv => le_of_eq (support_weight_C_eq_zero wTarget _ hv))
    hprod heu
  have hmono : Finsupp.weight wTarget e ≤ Finsupp.weight wSource u := by
    simpa using hmul
  exact hmono.trans (hP u hu)

end SupportWeights


variable {R : Type*} [CommRing R] {d m W : ℕ}

/-- Total degree in the error and visible jets, omitting `T`. -/
def reachableLocalJetDegree (e : LocalVariable d →₀ ℕ) : ℕ := Finsupp.degree e.some

/-- Integer weights on the displacement, error, and derivative variables. -/
def localWeight (t aux : ℤ) (jets : Fin d → ℤ) : LocalVariable d → ℤ
  | none => t
  | some none => aux
  | some (some j) => jets j

/-- Integer weights on the source variable and jets, with `Y₀` separate. -/
def sourceWeight (x y : ℤ) (jets : Fin d → ℤ) : JetVariable d → ℤ
  | none => x
  | some j => Fin.cases y jets j

private theorem unscaled_generator_weight_le (t aux x y : ℤ) (jets : Fin d → ℤ)
    (ht : t ≤ x) (hx : 0 ≤ x) (hy : 0 ≤ y) (haux : t + aux ≤ y)
    (hjets : ∀ j : Fin d, (j.val + 1) • t + jets j ≤ y)
    (center received : R) (v : JetVariable d) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalImage d center received v).support) :
    Finsupp.weight (localWeight t aux jets) e ≤ sourceWeight x y jets v := by
  rcases v with _ | j
  · apply support_weight_add_le _ ?_ ?_ he
    · intro z hz
      simpa [support_weight_C_eq_zero _ _ hz, sourceWeight] using hx
    · intro z hz
      simpa [support_weight_X_eq _ _ hz, localWeight, localT, sourceWeight] using ht
  · induction j using Fin.cases with
    | zero =>
      apply support_weight_add_le _ ?_ ?_ he
      · apply support_weight_add_le _
        · intro z hz
          simpa [support_weight_C_eq_zero _ _ hz, sourceWeight] using hy
        · intro z hz
          rw [localCorrection] at hz
          apply support_weight_sum_le _ Finset.univ _ (a := y) ?_ hz
          intro j hj z hz
          have h := support_weight_mul_le (localWeight t aux jets)
            (a := (j.val + 1) • t) (b := jets j)
            (fun v hv ↦ by
              have hp := support_weight_mul_le (localWeight t aux jets)
                (a := 0) (b := (j.val + 1) • t)
                (fun w hw ↦ (support_weight_C_eq_zero _ _ hw).le)
                (fun w hw ↦ support_weight_pow_le _
                  (fun q hq ↦ by simpa [localWeight, localT] using
                    (support_weight_X_eq (localWeight t aux jets) (localT d) hq).le)
                  (j.val + 1) hw) hv
              simpa using hp)
            (fun v hv ↦ by simpa [localWeight, localY] using
              (support_weight_X_eq (localWeight t aux jets) (localY j) hv).le) hz
          exact h.trans (hjets j)
      · intro z hz
        have h := support_weight_mul_le (localWeight t aux jets)
          (a := t) (b := aux)
          (fun v hv ↦ by simpa [localWeight, localT] using
            (support_weight_X_eq (localWeight t aux jets) (localT d) hv).le)
          (fun v hv ↦ by simpa [localWeight, localE, localAux] using
            (support_weight_X_eq (localWeight t aux jets) (localE d) hv).le) hz
        exact h.trans haux
    | succ j =>
      simpa [unscaledLocalImage, sourceWeight, localWeight, localY] using
        (support_weight_X_eq (localWeight t aux jets) (localY j) he).le

/-- Bounds on the images of generators transport an arbitrary integer source-weight cap
through the backward-Taylor substitution. Negative displacement weights retain cancellations. -/
theorem unscaled_support_weight_le (t aux x y : ℤ) (jets : Fin d → ℤ)
    (ht : t ≤ x) (hx : 0 ≤ x) (hy : 0 ≤ y) (haux : t + aux ≤ y)
    (hjets : ∀ j : Fin d, (j.val + 1) • t + jets j ≤ y)
    (center received : R) {Q : DifferentialPolynomial R d} {cap : ℤ}
    (hQ : ∀ u ∈ Q.support, Finsupp.weight (sourceWeight x y jets) u ≤ cap)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    Finsupp.weight (localWeight t aux jets) e ≤ cap :=
  support_weight_bind₁_le _ _ _
    (unscaled_generator_weight_le t aux x y jets ht hx hy haux hjets center received) hQ he

private theorem weight_source_higher (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (sourceWeight 0 0 (fun j : Fin d ↦ (j.val : ℤ))) u =
      (fullHigherJetWeight u : ℤ) := by
  simp only [Finsupp.weight_eq_sum, fullHigherJetWeight, Fintype.sum_option,
    sourceWeight, nsmul_eq_mul, mul_zero, zero_add]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp

private theorem weight_source_total (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (sourceWeight 0 1 (fun _ : Fin d ↦ 1)) u =
      (totalJetDegree u : ℤ) := by
  simp only [Finsupp.weight_eq_sum, totalJetDegree, Finsupp.degree_eq_sum,
    Fintype.sum_option, sourceWeight, nsmul_eq_mul, mul_zero, zero_add]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp

private theorem weight_local_balance (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (localWeight (-1) 1 (fun _ : Fin d ↦ 0)) e =
      (e (localE d) : ℤ) - e (localT d) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, localWeight, localE, localAux, localT]
  ring

private theorem weight_local_higher (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (localWeight (-1) 1 (fun j : Fin d ↦ (j.val : ℤ))) e =
      (Finsupp.weight (localHigherJetWeight d) e : ℤ) + e (localE d) - e (localT d) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, localWeight,
    localHigherJetWeight, localE, localAux, localT, Nat.cast_sum, Nat.cast_mul]
  ring

private theorem weight_local_total (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (localWeight 0 1 (fun _ : Fin d ↦ 1)) e =
      (reachableLocalJetDegree e : ℤ) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, localWeight,
    reachableLocalJetDegree, Finsupp.degree_eq_sum, Nat.cast_sum]

/-- Every unscaled local monomial has at least as many `T` factors as error factors.
This holds before contact projection and for every received point. -/
theorem unscaledLocal_error_le_t (center received : R) (Q : DifferentialPolynomial R d)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    e (localE d) ≤ e (localT d) := by
  have h := unscaled_support_weight_le (-1) 1 0 0 (fun _ : Fin d ↦ 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun j ↦ by simp) center received (cap := 0)
    (fun u hu ↦ by
      simp [Finsupp.weight_eq_sum, sourceWeight, Fin.sum_univ_succ, Fintype.sum_option]) he
  rw [weight_local_balance] at h
  omega

/-- The retained higher-jet weight gains at most `i-h`, not merely `i`. -/
theorem unscaledLocal_higher_weight_le (center received : R) {Q : DifferentialPolynomial R d}
    (hQ : ∀ u ∈ Q.support, fullHigherJetWeight u ≤ W)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    Finsupp.weight (localHigherJetWeight d) e ≤ W + (e (localT d) - e (localE d)) := by
  have h := unscaled_support_weight_le (-1) 1 0 0 (fun j : Fin d ↦ (j.val : ℤ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun j ↦ by simp) center received (cap := W)
    (fun u hu ↦ by rw [weight_source_higher]; exact_mod_cast hQ u hu) he
  rw [weight_local_higher] at h
  have hbalance := unscaledLocal_error_le_t center received Q he
  omega

private theorem weight_source_derivative (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (sourceWeight 0 0 (fun j : Fin d ↦ (j.val + 1 : ℤ))) u =
      (fullDerivativeJetWeight u : ℤ) := by
  simp only [Finsupp.weight_eq_sum, fullDerivativeJetWeight, Fintype.sum_option,
    sourceWeight, nsmul_eq_mul, mul_zero, zero_add]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp

private theorem weight_local_derivative (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (localWeight (-1) 1 (fun j : Fin d ↦ (j.val + 1 : ℤ))) e =
      (Finsupp.weight (localDerivativeJetWeight d) e : ℤ) +
        e (localE d) - e (localT d) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, localWeight,
    localDerivativeJetWeight, localE, localAux, localT, Nat.cast_sum, Nat.cast_mul]
  ring

/-- Charging every derivative by its order bounds the visible local weight by `W+i-h`.
The error exponent `h` consumes one of the `T` factors, leaving displacement `i-h`. -/
theorem unscaledLocal_derivativeJetWeight_le (center received : R)
    {Q : DifferentialPolynomial R d}
    (hQ : ∀ u ∈ Q.support, fullDerivativeJetWeight u ≤ W)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    Finsupp.weight (localDerivativeJetWeight d) e ≤ W + (e (localT d) - e (localE d)) := by
  have h := unscaled_support_weight_le (-1) 1 0 0 (fun j : Fin d ↦ (j.val + 1 : ℤ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun j ↦ by simp) center received (cap := W)
    (fun u hu ↦ by rw [weight_source_derivative]; exact_mod_cast hQ u hu) he
  rw [weight_local_derivative] at h
  have hbalance := unscaledLocal_error_le_t center received Q he
  omega

/-- A source total-jet degree cap is preserved by the actual local substitution. -/
theorem unscaledLocal_jet_degree_le (center received : R) {Q : DifferentialPolynomial R d}
    {B : ℕ} (hQ : ∀ u ∈ Q.support, totalJetDegree u ≤ B)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    reachableLocalJetDegree e ≤ B := by
  have h := unscaled_support_weight_le 0 1 0 1 (fun _ : Fin d ↦ 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun j ↦ by simp) center received (cap := B)
    (fun u hu ↦ by rw [weight_source_total]; exact_mod_cast hQ u hu) he
  rw [weight_local_total] at h
  exact_mod_cast h

/-- A strict total-jet cutoff survives substitution, independently of the support shape. -/
theorem unscaled_jet_degree_lt_of_support (center received : R)
    {Q : DifferentialPolynomial R d} {T : ℝ}
    (hsource : ∀ u ∈ Q.support, (totalJetDegree u : ℝ) < T)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    (reachableLocalJetDegree e : ℝ) < T := by
  have hne : Q ≠ 0 := by
    intro hz
    simp [hz] at he
  obtain ⟨u, hu⟩ := (MvPolynomial.support_nonempty.mpr hne)
  have hpos : 0 < ⌈T⌉₊ :=
    (Nat.zero_le (totalJetDegree u)).trans_lt (Nat.lt_ceil.mpr (hsource u hu))
  have hbound := unscaledLocal_jet_degree_le center received
    (B := ⌈T⌉₊ - 1)
    (fun u hu ↦ by have := Nat.lt_ceil.mpr (hsource u hu); omega) he
  apply Nat.lt_ceil.mp
  omega

private theorem mem_support_project {P : LocalPolynomial R d}
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (projectLowContact m P).support) :
    localContactOrder d e < m ∧ e ∈ P.support := by
  rw [MvPolynomial.mem_support_iff, projectLowContact, coeff_filterLocalMonomials] at he
  split_ifs at he with h
  · exact ⟨h, MvPolynomial.mem_support_iff.mpr he⟩
  · exact False.elim (he rfl)

/-- The rate-partition support reaches only local coordinates with the prescribed
derivative-order weight and contact budget. This statement is field independent. -/
theorem localConstraint_support_of_derivative_weight (center received : R)
    {Q : DifferentialPolynomial R d}
    (hweight : ∀ u ∈ Q.support, fullDerivativeJetWeight u ≤ W)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e (localE d) ≤ e (localT d) ∧
      Finsupp.weight (localDerivativeJetWeight d) e ≤ W + (e (localT d) - e (localE d)) ∧
      localContactOrder d e < m := by
  have hp := mem_support_project he
  exact ⟨unscaledLocal_error_le_t center received Q hp.2,
    unscaledLocal_derivativeJetWeight_le center received hweight hp.2, hp.1⟩

/-- Reachable local coordinates preserve higher-jet weight and total jet degree. -/
theorem localConstraint_support_of_weight_bounds (center received : R)
    {Q : DifferentialPolynomial R d} {T : ℝ}
    (hweight : ∀ u ∈ Q.support, fullHigherJetWeight u ≤ W)
    (htotal : ∀ u ∈ Q.support, (totalJetDegree u : ℝ) < T)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e (localE d) ≤ e (localT d) ∧
      Finsupp.weight (localHigherJetWeight d) e ≤ W + (e (localT d) - e (localE d)) ∧
      localContactOrder d e < m ∧
      (reachableLocalJetDegree e : ℝ) < T := by
  have hp := mem_support_project he
  exact ⟨unscaledLocal_error_le_t center received Q hp.2,
    unscaledLocal_higher_weight_le center received hweight hp.2, hp.1,
    unscaled_jet_degree_lt_of_support center received htotal hp.2⟩

theorem reachableLocalJetDegree_eq_coordinates (hd : 0 < d)
    (e : LocalVariable d →₀ ℕ) :
    reachableLocalJetDegree e = (localExponentCoordinatesEquiv hd e).2.1 +
      (localExponentCoordinatesEquiv hd e).2.2.1 +
      higherJetTupleDegree (localExponentCoordinatesEquiv hd e).2.2.2 := by
  rw [reachableLocalJetDegree, Finsupp.degree_eq_sum, Fintype.sum_option,
    sum_localJet_eq_first_add_higher hd]
  simp [higherJetTupleDegree, localU, localAux, localY, Nat.add_assoc]

theorem localContact_eq_coordinates (hd : 0 < d) (e : LocalVariable d →₀ ℕ) :
    localContactOrder d e = (localExponentCoordinatesEquiv hd e).1 +
      d * (localExponentCoordinatesEquiv hd e).2.1 := by
  simp [localContactOrder, Finsupp.weight_eq_sum, Fintype.sum_option,
    localContactWeight, localT, localU, localAux, Nat.mul_comm]

/-! ## Counting the remaining first-derivative degree

For each contact residual and higher-jet tuple, retain its own remaining degree. This
weighted count avoids replacing every fiber by a uniform first-derivative cap.
-/

/-- Local coordinates with a separate remaining-degree bound for each higher-jet tuple. -/
abbrev LocalResidualCoordinateIndex (d m W : ℕ) (T : ℝ) :=
  Σ r : Fin m, Fin ((m - r.val) ⌈/⌉ (d + 1)) ×
    (Σ z : ↥(weightedHigherJetTuples d (W + r.val)),
      Fin ⌈T - higherJetTupleDegree z.val⌉₊)

/-- The exact weighted count of potential residual coordinates. -/
def localResidualCoordinateBudget (d m W : ℕ) (T : ℝ) : ℕ :=
  ∑ r ∈ Finset.range m, ((m - r) ⌈/⌉ (d + 1)) *
    ∑ z ∈ weightedHigherJetTuples d (W + r), ⌈T - higherJetTupleDegree z⌉₊

/-- The dependent coordinate index has precisely the weighted sum cardinality. -/
theorem card_localResidualCoordinateIndex (d m W : ℕ) (T : ℝ) :
    Fintype.card (LocalResidualCoordinateIndex d m W T) =
      localResidualCoordinateBudget d m W T := by
  simp only [LocalResidualCoordinateIndex, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_fin, localResidualCoordinateBudget]
  conv_lhs =>
    arg 2
    ext r
    arg 2
    rw [Finset.sum_coe_sort (weightedHigherJetTuples d (W + r.val))
      (fun z ↦ ⌈T - higherJetTupleDegree z⌉₊)]
  exact Fin.sum_univ_eq_sum_range
    (fun r ↦ ((m - r) ⌈/⌉ (d + 1)) *
      ∑ z ∈ weightedHigherJetTuples d (W + r), ⌈T - higherJetTupleDegree z⌉₊) m

/-- Recover the local monomial from its residual coordinates. -/
def localResidualExponent {d m W : ℕ} {T : ℝ} (hd : 0 < d)
    (p : LocalResidualCoordinateIndex d m W T) : LocalVariable d →₀ ℕ :=
  (localExponentCoordinatesEquiv hd).symm
    (p.1.val + p.2.1.val, (p.2.1.val, (p.2.2.2.val, p.2.2.1.val)))

/-- All potential local monomials in the residual budget. -/
def localResidualExponents {d : ℕ} (hd : 0 < d) (m W : ℕ) (T : ℝ) :
    Finset (LocalVariable d →₀ ℕ) :=
  Finset.univ.image (localResidualExponent (m := m) (W := W) (T := T) hd)

/-- Passing from coordinate indices to exponents cannot increase cardinality. -/
theorem card_localResidualExponents_le {d : ℕ} (hd : 0 < d) (m W : ℕ) (T : ℝ) :
    (localResidualExponents hd m W T).card ≤ localResidualCoordinateBudget d m W T := by
  exact Finset.card_image_le.trans (by
    rw [Finset.card_univ, card_localResidualCoordinateIndex])

/-- Every reachable monomial lies in the residual count, with no lower cutoff. -/
theorem mem_localResidualExponents_of_bounds {d m W : ℕ} (hd : 0 < d)
    {T : ℝ} {e : LocalVariable d →₀ ℕ}
    (hbalance : e (localE d) ≤ e (localT d))
    (hweight : Finsupp.weight (localHigherJetWeight d) e ≤
      W + (e (localT d) - e (localE d)))
    (hcontact : localContactOrder d e < m)
    (htotal : (reachableLocalJetDegree e : ℝ) < T) :
    e ∈ localResidualExponents hd m W T := by
  rw [reachableLocalJetDegree_eq_coordinates hd] at htotal
  rw [localContact_eq_coordinates hd] at hcontact
  rw [localHigherJetWeight_eq_coordinate hd] at hweight
  let c := localExponentCoordinatesEquiv hd e
  have hb : c.2.1 ≤ c.1 := hbalance
  have hc : c.1 + d * c.2.1 < m := hcontact
  have hr : c.1 - c.2.1 < m := by omega
  have hh : c.2.1 < (m - (c.1 - c.2.1)) ⌈/⌉ (d + 1) := by
    apply lt_of_not_ge
    intro h
    have hmul := (ceilDiv_le_iff_le_mul (Nat.succ_pos d)).mp h
    rw [Nat.succ_mul] at hmul
    omega
  have hz : c.2.2.2 ∈ weightedHigherJetTuples d (W + (c.1 - c.2.1)) :=
    mem_weightedHigherJetTuples.mpr hweight
  have he₁ : c.2.2.1 < ⌈T - higherJetTupleDegree c.2.2.2⌉₊ := by
    apply Nat.lt_ceil.mpr
    have ht : ((c.2.1 + c.2.2.1 + higherJetTupleDegree c.2.2.2 : ℕ) : ℝ) < T := htotal
    push_cast at ht
    have hnonneg : (0 : ℝ) ≤ c.2.1 := Nat.cast_nonneg _
    linarith
  let p : LocalResidualCoordinateIndex d m W T :=
    ⟨⟨c.1 - c.2.1, hr⟩, ⟨⟨c.2.1, hh⟩, ⟨⟨c.2.2.2, hz⟩, ⟨c.2.2.1, he₁⟩⟩⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨p, Finset.mem_univ _, ?_⟩
  apply (localExponentCoordinatesEquiv hd).injective
  change (localExponentCoordinatesEquiv hd)
    ((localExponentCoordinatesEquiv hd).symm
      (c.1 - c.2.1 + c.2.1, (c.2.1, (c.2.2.1, c.2.2.2)))) = c
  simp [Nat.sub_add_cancel hb]

end ReedSolomon.HiddenDerivative
