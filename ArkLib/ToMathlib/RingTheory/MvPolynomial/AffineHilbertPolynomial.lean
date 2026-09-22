/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.Polynomial.EventualGrowth
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.StandardMonomials

/-!
# The affine Hilbert polynomial

Let `I` be an ideal of `MvPolynomial σ k`, where `k` is a field and `σ` is finite. The affine
Hilbert function `N ↦ affineHilbertFunction I N` agrees, for all large `N`, with a polynomial of
degree at most `Nat.card σ` (`MvPolynomial.exists_eval_eq_affineHilbertFunction`). Two polynomials
over `ℚ` that agree at all large natural numbers are equal, so this polynomial is unique. It is
`MvPolynomial.affineHilbertPolynomial I : ℚ[X]`. Its image in `K[X]` is the unique such polynomial
over every field `K` of characteristic zero.

The polynomial is zero exactly for the unit ideal. It is the constant
`Module.finrank k (MvPolynomial σ k ⧸ I)` when the quotient is finite-dimensional, and conversely
natural degree zero forces the quotient to be finite-dimensional. For `⊥` it is the binomial
polynomial `Polynomial.preHilbertPoly ℚ (Nat.card σ) 0`, and for a nonzero principal ideal
`span {f}` it is the backward difference of that polynomial with step `totalDegree f`. Its natural
degree and leading coefficient decrease along inclusions of ideals.

For an element `f` of total degree at most `b` whose class is a non-zero-divisor on the quotient
by `I`, the principal-cut inequality `H(I ⊔ span {f}, N) + H(I, N - b) ≤ H(I, N)` passes to the
polynomials: the polynomial of `I ⊔ span {f}` has natural degree at most one less than that of
`I`, and its coefficient in that degree is at most `b * natDegree P * leadingCoeff P`, where `P`
is the polynomial of `I`.

## Main statements

* `MvPolynomial.affineHilbertPolynomial`: the polynomial, with
  `MvPolynomial.exists_eval_affineHilbertPolynomial` and the uniqueness statements
  `MvPolynomial.eq_affineHilbertPolynomial_of_eval_eq` and
  `MvPolynomial.eq_map_affineHilbertPolynomial_of_eval_eq`.
* `MvPolynomial.affineHilbertPolynomial_eq_C_finrank`,
  `MvPolynomial.natDegree_affineHilbertPolynomial_eq_zero_iff`: finite-dimensional quotients.
* `MvPolynomial.affineHilbertPolynomial_eq_zero_iff`,
  `MvPolynomial.affineHilbertPolynomial_ne_zero`: vanishing exactly for the unit ideal.
* `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_le`,
  `MvPolynomial.leadingCoeff_affineHilbertPolynomial_le_of_le`: comparison along inclusions.
* `MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le`: the principal-cut
  degree drop, and its prime-ideal form `..._of_isPrime`.
* `MvPolynomial.affineHilbertPolynomial_bot`, `MvPolynomial.affineHilbertPolynomial_span_singleton`,
  `MvPolynomial.natDegree_affineHilbertPolynomial_span_singleton_add_one`: the polynomial ring and
  hypersurfaces.
* `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_mem`: an ideal containing a nonzero
  polynomial has natural degree at most `Nat.card σ - 1`.
-/

@[expose] public section

noncomputable section

open Filter Polynomial

namespace MvPolynomial

variable {k σ : Type*} [Field k] [Finite σ]

/-- The affine Hilbert polynomial of `I`: the polynomial over `ℚ` that agrees with the affine
Hilbert function `affineHilbertFunction I N` for all large natural numbers `N`. It is chosen from
`exists_eval_eq_affineHilbertFunction`; `eq_affineHilbertPolynomial_of_eval_eq` shows that the
choice does not matter. -/
def affineHilbertPolynomial (I : Ideal (MvPolynomial σ k)) : ℚ[X] :=
  (exists_eval_eq_affineHilbertFunction ℚ I).choose

/-- The affine Hilbert polynomial has natural degree at most the number of variables. -/
theorem natDegree_affineHilbertPolynomial_le (I : Ideal (MvPolynomial σ k)) :
    (affineHilbertPolynomial I).natDegree ≤ Nat.card σ :=
  (exists_eval_eq_affineHilbertFunction ℚ I).choose_spec.1

/-- The affine Hilbert polynomial agrees with the affine Hilbert function from some degree on. -/
theorem exists_eval_affineHilbertPolynomial (I : Ideal (MvPolynomial σ k)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (affineHilbertPolynomial I).eval (N : ℚ) = affineHilbertFunction I N :=
  (exists_eval_eq_affineHilbertFunction ℚ I).choose_spec.2

/-- The filter form of `exists_eval_affineHilbertPolynomial`. -/
theorem eventually_eval_affineHilbertPolynomial (I : Ideal (MvPolynomial σ k)) :
    ∀ᶠ N : ℕ in atTop,
      (affineHilbertPolynomial I).eval (N : ℚ) = affineHilbertFunction I N :=
  eventually_atTop.mpr (exists_eval_affineHilbertPolynomial I)

/-- Uniqueness: a polynomial over `ℚ` that agrees with the affine Hilbert function from some
degree on is the affine Hilbert polynomial. -/
theorem eq_affineHilbertPolynomial_of_eval_eq {I : Ideal (MvPolynomial σ k)} {P : ℚ[X]}
    {N₀ : ℕ} (hP : ∀ N ≥ N₀, P.eval (N : ℚ) = affineHilbertFunction I N) :
    P = affineHilbertPolynomial I := by
  obtain ⟨N₁, hN₁⟩ := exists_eval_affineHilbertPolynomial I
  refine eq_of_eventually_eval_natCast_eq (N₀ := max N₀ N₁) fun N hN ↦ ?_
  rw [hP N (le_of_max_le_left hN), hN₁ N (le_of_max_le_right hN)]

/-- Uniqueness over any field `K` of characteristic zero: a polynomial over `K` that agrees with
the affine Hilbert function from some degree on is the image of the affine Hilbert polynomial.
So the choice of `ℚ` as coefficient field loses nothing. -/
theorem eq_map_affineHilbertPolynomial_of_eval_eq {K : Type*} [Field K] [CharZero K]
    {I : Ideal (MvPolynomial σ k)} {P : K[X]} {N₀ : ℕ}
    (hP : ∀ N ≥ N₀, P.eval (N : K) = affineHilbertFunction I N) :
    P = (affineHilbertPolynomial I).map (algebraMap ℚ K) := by
  obtain ⟨N₁, hN₁⟩ := exists_eval_affineHilbertPolynomial I
  refine eq_of_eventually_eval_natCast_eq (N₀ := max N₀ N₁) fun N hN ↦ ?_
  rw [hP N (le_of_max_le_left hN), eval_map_algebraMap, ← map_natCast (algebraMap ℚ K) N,
    aeval_algebraMap_apply_eq_algebraMap_eval, hN₁ N (le_of_max_le_right hN), map_natCast]

/-- The affine Hilbert polynomial is eventually nonnegative on the natural numbers, since the
affine Hilbert function is a dimension. -/
theorem eventually_eval_affineHilbertPolynomial_nonneg (I : Ideal (MvPolynomial σ k)) :
    ∀ᶠ N : ℕ in atTop, 0 ≤ (affineHilbertPolynomial I).eval (N : ℚ) :=
  (eventually_eval_affineHilbertPolynomial I).mono fun _ hN ↦ hN ▸ Nat.cast_nonneg _

/-- For a finite-dimensional quotient, the affine Hilbert polynomial is the constant
`Module.finrank k (MvPolynomial σ k ⧸ I)`, because the affine Hilbert function stabilizes at that
value. -/
theorem affineHilbertPolynomial_eq_C_finrank (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    affineHilbertPolynomial I = Polynomial.C (Module.finrank k (MvPolynomial σ k ⧸ I) : ℚ) := by
  obtain ⟨N₀, hN₀⟩ := exists_affineHilbertFunction_eq_finrank I
  exact (eq_affineHilbertPolynomial_of_eval_eq (N₀ := N₀) fun N hN ↦ by
    rw [Polynomial.eval_C, hN₀ N hN]).symm

/-- The unit ideal has the zero affine Hilbert polynomial. -/
@[simp]
theorem affineHilbertPolynomial_top :
    affineHilbertPolynomial (⊤ : Ideal (MvPolynomial σ k)) = 0 :=
  (eq_affineHilbertPolynomial_of_eval_eq (N₀ := 0) fun N _ ↦ by
    rw [Polynomial.eval_zero, affineHilbertFunction_top, Nat.cast_zero]).symm

/-- A proper ideal has a nonzero affine Hilbert polynomial, since its affine Hilbert function is
at least `1` in every degree. -/
theorem affineHilbertPolynomial_ne_zero {I : Ideal (MvPolynomial σ k)} (hI : I ≠ ⊤) :
    affineHilbertPolynomial I ≠ 0 := by
  intro h
  obtain ⟨N₀, hN₀⟩ := exists_eval_affineHilbertPolynomial I
  have h1 := one_le_affineHilbertFunction hI N₀
  have h0 := hN₀ N₀ le_rfl
  rw [h, Polynomial.eval_zero] at h0
  exact absurd (Nat.cast_eq_zero.mp h0.symm) (Nat.one_le_iff_ne_zero.mp h1)

/-- The affine Hilbert polynomial vanishes exactly for the unit ideal. -/
@[simp]
theorem affineHilbertPolynomial_eq_zero_iff {I : Ideal (MvPolynomial σ k)} :
    affineHilbertPolynomial I = 0 ↔ I = ⊤ :=
  ⟨fun h ↦ by_contra fun hI ↦ affineHilbertPolynomial_ne_zero hI h,
    fun h ↦ h ▸ affineHilbertPolynomial_top⟩

/-- A proper ideal has an affine Hilbert polynomial with positive leading coefficient. -/
theorem leadingCoeff_affineHilbertPolynomial_pos {I : Ideal (MvPolynomial σ k)} (hI : I ≠ ⊤) :
    0 < (affineHilbertPolynomial I).leadingCoeff :=
  leadingCoeff_pos_of_eventually_eval_natCast_nonneg (affineHilbertPolynomial_ne_zero hI)
    (eventually_eval_affineHilbertPolynomial_nonneg I)

/-- If the affine Hilbert polynomial is constant, the quotient is finite-dimensional.

A constant polynomial makes the affine Hilbert function eventually constant, say from `N₀` on.
The `N₀`-th piece of the filtration then equals every later piece, since it is contained in them
and has the same finite dimension; as the pieces exhaust the quotient, the `N₀`-th piece is the
whole quotient. -/
theorem moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero
    {I : Ideal (MvPolynomial σ k)} (hdeg : (affineHilbertPolynomial I).natDegree = 0) :
    Module.Finite k (MvPolynomial σ k ⧸ I) := by
  obtain ⟨N₀, hN₀⟩ := exists_eval_affineHilbertPolynomial I
  have hconst : ∀ N ≥ N₀, affineHilbertFunction I N = affineHilbertFunction I N₀ := by
    intro N hN
    have hc : ∀ M : ℕ, (affineHilbertPolynomial I).eval (M : ℚ) =
        (affineHilbertPolynomial I).coeff 0 := fun M ↦ by
      rw [eq_C_of_natDegree_eq_zero hdeg, Polynomial.eval_C, Polynomial.coeff_C_zero]
    have h := (hN₀ N hN).symm.trans ((hc N).trans ((hc N₀).symm.trans (hN₀ N₀ le_rfl)))
    exact_mod_cast h
  have htop : quotientDegreeLE I N₀ = ⊤ := by
    refine top_unique fun x _ ↦ ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hle : N₀ ≤ max N₀ p.totalDegree := le_max_left _ _
    rw [Submodule.eq_of_le_of_finrank_eq (quotientDegreeLE_mono I hle) (hconst _ hle).symm]
    exact mk_mem_quotientDegreeLE (le_max_right _ _)
  have : Module.Finite k (⊤ : Submodule k (MvPolynomial σ k ⧸ I)) := htop ▸ inferInstance
  exact Module.Finite.of_surjective (⊤ : Submodule k (MvPolynomial σ k ⧸ I)).subtype
    fun x ↦ ⟨⟨x, Submodule.mem_top⟩, rfl⟩

/-- The affine Hilbert polynomial has natural degree zero exactly when the quotient is
finite-dimensional. -/
theorem natDegree_affineHilbertPolynomial_eq_zero_iff {I : Ideal (MvPolynomial σ k)} :
    (affineHilbertPolynomial I).natDegree = 0 ↔ Module.Finite k (MvPolynomial σ k ⧸ I) :=
  ⟨moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero, fun _ ↦ by
    rw [affineHilbertPolynomial_eq_C_finrank, Polynomial.natDegree_C]⟩

/-- For `I ≤ J`, the affine Hilbert polynomial of `J` is at most that of `I` at all large natural
numbers, because the affine Hilbert function is antitone in the ideal
(`affineHilbertFunction_anti`). -/
theorem eventually_eval_affineHilbertPolynomial_le_of_le {I J : Ideal (MvPolynomial σ k)}
    (hIJ : I ≤ J) :
    ∀ᶠ N : ℕ in atTop, (affineHilbertPolynomial J).eval (N : ℚ) ≤
      (affineHilbertPolynomial I).eval (N : ℚ) := by
  filter_upwards [eventually_eval_affineHilbertPolynomial I,
    eventually_eval_affineHilbertPolynomial J] with N hI hJ
  rw [hI, hJ]
  exact_mod_cast affineHilbertFunction_anti hIJ N

/-- A larger ideal has an affine Hilbert polynomial of no larger natural degree. No properness
hypothesis is needed: for `J = ⊤` the left side is `0`. -/
theorem natDegree_affineHilbertPolynomial_le_of_le {I J : Ideal (MvPolynomial σ k)}
    (hIJ : I ≤ J) :
    (affineHilbertPolynomial J).natDegree ≤ (affineHilbertPolynomial I).natDegree :=
  (natDegree_le_of_eventually_eval_natCast_le (eventually_eval_affineHilbertPolynomial_nonneg J)
    (eventually_eval_affineHilbertPolynomial_le_of_le hIJ)).1

/-- When a larger ideal has an affine Hilbert polynomial of the same natural degree, its leading
coefficient is no larger. -/
theorem leadingCoeff_affineHilbertPolynomial_le_of_le {I J : Ideal (MvPolynomial σ k)}
    (hIJ : I ≤ J)
    (hdeg : (affineHilbertPolynomial J).natDegree = (affineHilbertPolynomial I).natDegree) :
    (affineHilbertPolynomial J).leadingCoeff ≤ (affineHilbertPolynomial I).leadingCoeff :=
  (natDegree_le_of_eventually_eval_natCast_le (eventually_eval_affineHilbertPolynomial_nonneg J)
    (eventually_eval_affineHilbertPolynomial_le_of_le hIJ)).2 hdeg

/-- The principal-cut degree drop. Let the class of `f` be a non-zero-divisor on
`MvPolynomial σ k ⧸ I` and let `f` have total degree at most `b`. Write `P` for the affine Hilbert
polynomial of `I` and `Q` for that of `I ⊔ span {f}`. Then `natDegree Q ≤ natDegree P - 1`, and
the coefficient of `Q` in degree `natDegree P - 1` is at most `b * natDegree P * leadingCoeff P`.

The principal-cut inequality `H(I ⊔ span {f}, N) + H(I, N - b) ≤ H(I, N)` puts `Q` below the
backward difference `P(X) - P(X - b)` at large natural numbers, and the polynomial comparison
`Polynomial.natDegree_le_and_coeff_le_of_eventually_eval_natCast_le_backwardDifference` gives both
bounds. Regularity of `f` is needed: for `I = span {X ^ 2}` in one variable and `f = X`, `P` is the
constant `2` and `Q` the constant `1`, so the coefficient bound `1 ≤ 0` fails. When
`I ⊔ span {f} = ⊤`, `Q = 0` and both bounds hold trivially. -/
theorem principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    {I : Ideal (MvPolynomial σ k)} {f : MvPolynomial σ k}
    (hf : IsLeftRegular (Ideal.Quotient.mk I f)) {b : ℕ} (hfdeg : f.totalDegree ≤ b) :
    (affineHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree ≤
        (affineHilbertPolynomial I).natDegree - 1 ∧
      (affineHilbertPolynomial (I ⊔ Ideal.span {f})).coeff
          ((affineHilbertPolynomial I).natDegree - 1) ≤
        (b : ℚ) * (affineHilbertPolynomial I).natDegree *
          (affineHilbertPolynomial I).leadingCoeff := by
  refine natDegree_le_and_coeff_le_of_eventually_eval_natCast_le_backwardDifference
    (eventually_eval_affineHilbertPolynomial_nonneg _) ?_
  obtain ⟨N₀, hN₀⟩ := exists_eval_affineHilbertPolynomial I
  filter_upwards [eventually_eval_affineHilbertPolynomial (I ⊔ Ideal.span {f}),
    eventually_ge_atTop (N₀ + b)] with N hQ hN
  have hbN : b ≤ N := by omega
  rw [hQ, eval_backwardDifference, ← Nat.cast_sub hbN, hN₀ N (by omega), hN₀ (N - b) (by omega),
    le_sub_iff_add_le]
  exact_mod_cast principalCut_affineHilbertFunction_add_le hf hfdeg hbN

/-- The principal-cut degree drop for a prime ideal `I` and an element `f ∉ I`, whose class is
then a non-zero-divisor on the domain `MvPolynomial σ k ⧸ I`. -/
theorem principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    {I : Ideal (MvPolynomial σ k)} (hI : I.IsPrime) {f : MvPolynomial σ k} (hfI : f ∉ I)
    {b : ℕ} (hfdeg : f.totalDegree ≤ b) :
    (affineHilbertPolynomial (I ⊔ Ideal.span {f})).natDegree ≤
        (affineHilbertPolynomial I).natDegree - 1 ∧
      (affineHilbertPolynomial (I ⊔ Ideal.span {f})).coeff
          ((affineHilbertPolynomial I).natDegree - 1) ≤
        (b : ℚ) * (affineHilbertPolynomial I).natDegree *
          (affineHilbertPolynomial I).leadingCoeff :=
  have := hI
  principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hfI)) hfdeg

/-! ### The polynomial ring and hypersurfaces -/

/-- The polynomial ring in `n = Nat.card σ` variables has affine Hilbert polynomial
`Polynomial.preHilbertPoly ℚ n 0`, which evaluates to `(N + n).choose n` at every natural
number `N`. -/
theorem affineHilbertPolynomial_bot :
    affineHilbertPolynomial (⊥ : Ideal (MvPolynomial σ k)) = preHilbertPoly ℚ (Nat.card σ) 0 :=
  (eq_affineHilbertPolynomial_of_eval_eq (N₀ := 0) fun N _ ↦ by
    rw [preHilbertPoly_eq_choose_add_sub ℚ _ (Nat.zero_le _), Nat.sub_zero,
      affineHilbertFunction_bot]).symm

/-- The polynomial ring in `n` variables has affine Hilbert polynomial of natural degree `n`. -/
@[simp]
theorem natDegree_affineHilbertPolynomial_bot :
    (affineHilbertPolynomial (⊥ : Ideal (MvPolynomial σ k))).natDegree = Nat.card σ := by
  rw [affineHilbertPolynomial_bot, natDegree_preHilbertPoly]

/-- For `f ≠ 0` and `N ≥ totalDegree f`, the affine Hilbert function of `span {f}` in `n`
variables is `(N + n).choose n - (N - totalDegree f + n).choose n`: the `degLex`-standard exponents
are those not above the leading exponent of `f`, which has degree `totalDegree f`. -/
theorem affineHilbertFunction_span_singleton {f : MvPolynomial σ k} (hf : f ≠ 0) {N : ℕ}
    (hN : f.totalDegree ≤ N) :
    (affineHilbertFunction (Ideal.span {f}) N : ℚ) =
      ((N + Nat.card σ).choose (Nat.card σ) : ℚ) -
        ((N - f.totalDegree + Nat.card σ).choose (Nat.card σ) : ℚ) := by
  classical
  have := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  set e₀ := MonomialOrder.degLex.degree f
  have he₀ : e₀.degree = f.totalDegree :=
    MonomialOrder.degree_degree_eq_totalDegree (fun _ _ ↦ degree_le_degree_of_degLex_le) f
  have hset : {e : σ →₀ ℕ | e ∈ MonomialOrder.degLex.standardExponents (Ideal.span {f}) ∧
      e.degree ≤ N} = ↑({e ∈ Finsupp.degreeLEFinset σ N | ¬e₀ ≤ e}) := by
    ext e
    simp [MonomialOrder.mem_standardExponents_span_singleton _ hf, e₀, and_comm]
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finsupp.degreeLEFinset σ N)
    (fun e ↦ e₀ ≤ e)
  rw [Finsupp.card_filter_le_degreeLEFinset _ (he₀ ▸ hN), Finsupp.card_degreeLEFinset,
    he₀] at hsplit
  rw [affineHilbertFunction_eq_standard_count, hset, Set.ncard_coe_finset,
    Nat.card_eq_fintype_card, ← hsplit]
  push_cast
  ring

/-- A nonzero principal ideal `span {f}` has affine Hilbert polynomial equal to the backward
difference of `Polynomial.preHilbertPoly ℚ n 0` with step `totalDegree f`, where `n = Nat.card σ`.
The hypothesis `f ≠ 0` is needed: `span {0} = ⊥` has polynomial `preHilbertPoly ℚ n 0` itself,
while the backward difference with step `0` is zero. -/
theorem affineHilbertPolynomial_span_singleton {f : MvPolynomial σ k} (hf : f ≠ 0) :
    affineHilbertPolynomial (Ideal.span {f}) =
      backwardDifference (f.totalDegree : ℚ) (preHilbertPoly ℚ (Nat.card σ) 0) := by
  refine (eq_affineHilbertPolynomial_of_eval_eq (N₀ := f.totalDegree) fun N hN ↦ ?_).symm
  rw [affineHilbertFunction_span_singleton hf hN, eval_backwardDifference, ← Nat.cast_sub hN,
    preHilbertPoly_eq_choose_add_sub ℚ _ (Nat.zero_le _),
    preHilbertPoly_eq_choose_add_sub ℚ _ (Nat.zero_le _), Nat.sub_zero, Nat.sub_zero]

omit [Finite σ] in
/-- A nonzero polynomial generating a proper ideal has positive total degree: a nonzero constant
is a unit. -/
theorem totalDegree_pos_of_span_singleton_ne_top {f : MvPolynomial σ k} (hf : f ≠ 0)
    (hproper : Ideal.span {f} ≠ ⊤) : 0 < f.totalDegree := by
  refine Nat.pos_of_ne_zero fun hdeg ↦ hproper (Ideal.span_singleton_eq_top.mpr ?_)
  rw [totalDegree_eq_zero_iff_eq_C.mp hdeg] at hf ⊢
  exact (isUnit_iff_ne_zero.mpr fun h ↦ hf (by rw [h, map_zero])).map C

/-- A nonzero proper hypersurface `span {f}` in `n` variables has affine Hilbert polynomial of
natural degree `n - 1`, stated as `natDegree + 1 = n`. Both hypotheses are needed: `span {0} = ⊥`
has natural degree `n`, and a nonzero constant generates `⊤`, whose polynomial is `0`. -/
theorem natDegree_affineHilbertPolynomial_span_singleton_add_one {f : MvPolynomial σ k}
    (hf : f ≠ 0) (hproper : Ideal.span {f} ≠ ⊤) :
    (affineHilbertPolynomial (Ideal.span {f})).natDegree + 1 = Nat.card σ := by
  have hb := totalDegree_pos_of_span_singleton_ne_top hf hproper
  have hσ : 0 < Nat.card σ := by
    obtain ⟨e, he, hepos⟩ : ∃ e ∈ f.support, 0 < e.degree := by
      by_contra! h
      exact hb.ne' (Nat.le_zero.mp (Finset.sup_le h))
    obtain ⟨i, -⟩ := (Finsupp.support_nonempty_iff (f := e)).mpr fun h0 ↦ by
      rw [h0, map_zero] at hepos
      exact lt_irrefl 0 hepos
    have : Nonempty σ := ⟨i⟩
    exact Nat.card_pos
  have hd : 0 < (preHilbertPoly ℚ (Nat.card σ) 0).natDegree := by
    rwa [natDegree_preHilbertPoly]
  rw [affineHilbertPolynomial_span_singleton hf,
    (natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero
      (Nat.cast_ne_zero.mpr hb.ne') hd).1, natDegree_preHilbertPoly]
  omega

/-- An ideal containing a nonzero polynomial `g` in `n` variables has affine Hilbert polynomial of
natural degree at most `n - 1`.

If `span {g}` is proper, this is `natDegree_affineHilbertPolynomial_le_of_le` and
`natDegree_affineHilbertPolynomial_span_singleton_add_one`; otherwise `g` is a unit, `I = ⊤` and
the polynomial is `0`. The hypothesis `g ≠ 0` is needed: `I = ⊥` contains `0` and has natural
degree `n`. -/
theorem natDegree_affineHilbertPolynomial_le_of_mem {I : Ideal (MvPolynomial σ k)}
    {g : MvPolynomial σ k} (hg : g ≠ 0) (hgI : g ∈ I) :
    (affineHilbertPolynomial I).natDegree ≤ Nat.card σ - 1 := by
  by_cases hproper : Ideal.span {g} = ⊤
  · rw [eq_top_mono ((Ideal.span_singleton_le_iff_mem I).mpr hgI) hproper,
      affineHilbertPolynomial_top, Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · have := natDegree_affineHilbertPolynomial_span_singleton_add_one hg hproper
    have := natDegree_affineHilbertPolynomial_le_of_le ((Ideal.span_singleton_le_iff_mem I).mpr hgI)
    omega

end MvPolynomial
