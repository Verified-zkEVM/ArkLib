
import Mathlib.Algebra.MvPolynomial.Equiv
import ArkLib.ToMathlib.Finsupp.Fin

namespace MvPolynomial

open Function Finsupp Polynomial

noncomputable section

section FinSuccEquivNth

variable {n : ℕ} {σ : Type*} (R : Type*) [CommSemiring R] (p : Fin (n + 1))

/-- The algebra isomorphism between multivariable polynomials in `Fin (n + 1)` and polynomials over
  multivariable polynomials in `Fin n`, where the `p`-th (pivot) variable is the indeterminate `X`.

  `finSuccEquiv` is the special case when `p = 0`. -/
def finSuccEquivNth : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv' p)).trans (optionEquivLeft R (Fin n))

theorem finSuccEquivNth_eq :
    (finSuccEquivNth R p : MvPolynomial (Fin (n + 1)) R →+* Polynomial (MvPolynomial (Fin n) R)) =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R))
        (Fin.insertNth p Polynomial.X (Polynomial.C ∘ X)) := by
  ext j : 2
  · simp only [finSuccEquivNth, optionEquivLeft_apply, aeval_C, AlgEquiv.coe_trans, RingHom.coe_coe,
      coe_eval₂Hom, comp_apply, renameEquiv_apply, eval₂_C, RingHom.coe_comp, rename_C]
    rfl
  · refine Fin.succAboveCases p ?_ ?_ j <;> simp [finSuccEquivNth, optionEquivLeft]

theorem finSuccEquivNth_apply (f : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquivNth R p f =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R))
        (Fin.insertNth p Polynomial.X (Polynomial.C ∘ X)) f := by
  rw [← finSuccEquivNth_eq, RingHom.coe_coe]

theorem finSuccEquivNth_comp_C_eq_C :
    (↑(finSuccEquivNth R p).symm : Polynomial (MvPolynomial (Fin n) R) →+* _).comp
        (Polynomial.C.comp C) = (C : R →+* MvPolynomial (Fin n.succ) R) := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply]
  refine
    (finSuccEquivNth R p).injective
      (Trans.trans ((finSuccEquivNth R p).apply_symm_apply _) ?_)
  simp only [finSuccEquivNth_apply, MvPolynomial.eval₂Hom_C]

variable {R} {p}

@[simp]
theorem finSuccEquivNth_X_same : finSuccEquivNth R p (X p) = Polynomial.X := by
  simp [finSuccEquivNth_apply]

@[simp]
theorem finSuccEquivNth_X_above {i : Fin n} (h : p < i.succ) :
    finSuccEquivNth R p (X i.succ) = Polynomial.C (X i) := by
  simp [finSuccEquivNth_apply, Fin.insertNth_apply_above h _ _]

@[simp]
theorem finSuccEquivNth_X_below {i : Fin n} (h : i.castSucc < p) :
    finSuccEquivNth R p (X i.castSucc) = Polynomial.C (X i) := by
  simp [finSuccEquivNth_apply, Fin.insertNth_apply_below h _ _]

/-- The coefficient of `m` in the `i`-th coefficient of `finSuccEquivNth R p f` equals the
    coefficient of `m.insertNth p i` in `f`. -/
theorem finSuccEquivNth_coeff_coeff (m : Fin n →₀ ℕ) (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ) :
    coeff m (Polynomial.coeff (finSuccEquivNth R p f) i) = coeff (m.insertNth p i) f := by
  induction f using MvPolynomial.induction_on' generalizing i m with
  | monomial u a =>
    simp only [finSuccEquivNth_apply, coe_eval₂Hom, eval₂_monomial, RingHom.coe_comp, comp_apply,
      prod_pow, Fin.prod_univ_succAbove _ p, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, Polynomial.coeff_C_mul, coeff_C_mul, coeff_monomial,
      ← map_prod, ← RingHom.map_pow]
    rw [← mul_boole, mul_comm (Polynomial.X ^ u p), Polynomial.coeff_C_mul_X_pow]; congr 1
    obtain rfl | hjmi := eq_or_ne u (m.insertNth p i)
    · simpa only [insertNth_apply_same, if_pos rfl, insertNth_apply_succAbove, monomial_eq, C_1,
        one_mul, prod_pow] using coeff_monomial m m (1 : R)
    · simp only [hjmi, if_false]
      obtain hij | rfl := ne_or_eq i (u p)
      · simp only [hij, if_false, coeff_zero]
      simp only [if_true]
      have hmj : m ≠ u.removeNth p := by
        rintro rfl
        rw [insertNth_self_removeNth] at hjmi
        contradiction
      simpa only [monomial_eq, C_1, one_mul, prod_pow, Finsupp.removeNth_apply, if_neg hmj.symm]
        using coeff_monomial m (u.removeNth p) (1 : R)
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]

/-- The evaluation of `f` at `Fin.insertNth p y s` equals the evaluation at `y` of the polynomial
obtained by partially evaluating `finSuccEquivNth R p f` at `s`.
-/
theorem eval_eq_eval_mv_eval_finSuccEquivNth (s : Fin n → R) (y : R)
    (f : MvPolynomial (Fin (n + 1)) R) :
      eval (Fin.insertNth p y s : Fin (n + 1) → R) f =
        Polynomial.eval y (Polynomial.map (eval s) (finSuccEquivNth R p f)) := by
  change
    aeval (Fin.insertNth p y s : Fin (n + 1) → R) f = (Polynomial.aeval y).comp
      ((Polynomial.mapAlgHom (aeval s)).comp (finSuccEquivNth R p).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  simp only [Fin.forall_iff_succAbove p, aeval_X, Fin.insertNth_apply_same, Polynomial.mapAlgHom,
    AlgHom.toRingHom_eq_coe, coe_aeval_eq_eval, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp,
    Polynomial.coe_aeval_eq_eval, AlgHom.coe_mk, coe_mapRingHom, AlgHom.coe_coe, comp_apply,
    finSuccEquivNth_apply, eval₂Hom_X', Polynomial.map_X, Polynomial.eval_X,
    Fin.insertNth_apply_succAbove, Polynomial.map_C, eval_X, Polynomial.eval_C, implies_true,
    and_self]

/-- A monomial index `m` is in the support of the `i`-th coefficient of `finSuccEquivNth R p f` if
and only if `m.insertNth p i` is in the support of `f`. -/
theorem support_coeff_finSuccEquivNth {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {m : Fin n →₀ ℕ} :
    m ∈ (Polynomial.coeff ((finSuccEquivNth R p) f) i).support ↔ m.insertNth p i ∈ f.support := by
  constructor <;> intro h
  · simpa [← finSuccEquivNth_coeff_coeff] using h
  · simpa [mem_support_iff, ← finSuccEquivNth_coeff_coeff m f i] using h

/--
The `totalDegree` of a multivariable polynomial `f` is at least `i` more than the `totalDegree` of
the `i`th coefficient of `finSuccEquivNth R p` applied to `f`, if this is nonzero.
-/
theorem totalDegree_coeff_finSuccEquivNth_add_le (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ)
    (hi : (finSuccEquivNth R p f).coeff i ≠ 0) :
      totalDegree ((finSuccEquivNth R p f).coeff i) + i ≤ totalDegree f := by
  have hf'_sup : ((finSuccEquivNth R p f).coeff i).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, support_eq_empty]
    exact hi
  -- Let σ be a monomial index of ((finSuccEquivNth R p f).coeff i) of maximal total degree
  have ⟨σ, hσ1, hσ2⟩ := Finset.exists_mem_eq_sup (support _) hf'_sup
                          (fun s => Finsupp.sum s fun _ e => e)
  -- Then σ.insertNth p i is a monomial index of f with total degree equal to the desired bound
  convert le_totalDegree (s := σ.insertNth p i) _
  · rw [totalDegree, hσ2, sum_insertNth _ _ p, add_comm]
  · rwa [← support_coeff_finSuccEquivNth]

/-- The support of `finSuccEquivNth R p f` equals the support of `f` projected onto the `p`-th
variable. -/
theorem support_finSuccEquivNth (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquivNth R p f).support = Finset.image (fun m : Fin (n + 1) →₀ ℕ => m p) f.support := by
  ext i
  rw [Polynomial.mem_support_iff, Finset.mem_image, Finsupp.ne_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m.insertNth p i, ?_, insertNth_apply_same _ _ _⟩
    rw [← support_coeff_finSuccEquivNth]
    simpa using hm
  · rintro ⟨m, h, rfl⟩
    refine ⟨m.removeNth p, ?_⟩
    rwa [← coeff, zero_apply, ← mem_support_iff, support_coeff_finSuccEquivNth,
      insertNth_self_removeNth]

theorem mem_support_finSuccEquivNth {f : MvPolynomial (Fin (n + 1)) R} {x} :
    x ∈ (finSuccEquivNth R p f).support ↔ x ∈ (fun m : Fin (n + 1) →₀ _ ↦ m p) '' f.support := by
  simpa using congr(x ∈ $(support_finSuccEquivNth f))

theorem image_support_finSuccEquivNth {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} :
    Finset.image (Finsupp.insertNth p i) (Polynomial.coeff ((finSuccEquivNth R p) f) i).support =
      f.support.filter fun m => m p = i := by
  ext m
  rw [Finset.mem_filter, Finset.mem_image, mem_support_iff]
  conv_lhs =>
    congr
    ext
    rw [mem_support_iff, finSuccEquivNth_coeff_coeff, Ne]
  constructor
  · rintro ⟨m', ⟨h, hm'⟩⟩
    simp only [← hm']
    exact ⟨h, by rw [insertNth_apply_same]⟩
  · intro h
    use m.removeNth p
    rw [← h.2, insertNth_removeNth]
    simp [h.1]

lemma mem_image_support_coeff_finSuccEquivNth {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {x} :
    x ∈ Finsupp.insertNth p i '' ((finSuccEquivNth R p f).coeff i).support ↔
      x ∈ f.support ∧ x p = i := by
  simpa using congr(x ∈ $image_support_finSuccEquivNth)

lemma mem_support_coeff_finSuccEquivNth {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {x} :
    x ∈ ((finSuccEquivNth R p f).coeff i).support ↔ x.insertNth p i ∈ f.support := by
  rw [← (Finsupp.insertNth_right_injective p).mem_finset_image (a := x),
    image_support_finSuccEquivNth]
  simp only [Finset.mem_filter, mem_support_iff, ne_eq, insertNth_apply_same, and_true]

theorem support_finSuccEquivNth_nonempty {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquivNth R p f).support.Nonempty := by
  rwa [Polynomial.support_nonempty, EmbeddingLike.map_ne_zero_iff]

/-- The degree of `finSuccEquivNth R p f` equals the `p`-th degree of `f`. -/
theorem degree_finSuccEquivNth {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquivNth R p f).degree = degreeOf p f := by
  have hCast : WithBot.some = Nat.cast := rfl
  have h' : ((finSuccEquivNth R p f).support.sup id) = degreeOf p f := by
    rw [degreeOf_eq_sup, support_finSuccEquivNth f, Finset.sup_image, Function.id_comp]
  rw [Polynomial.degree, ← h', ← hCast, Finset.coe_sup_of_nonempty
    (Polynomial.support_nonempty.mpr (EmbeddingLike.map_ne_zero_iff.mpr h)),
    Finset.max_eq_sup_coe, Function.comp_id]

/-- The `natDegree` of `finSuccEquivNth R p f` equals the `p`-th `natDegree` of `f`. -/
theorem natDegree_finSuccEquivNth (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquivNth R p f).natDegree = degreeOf p f := by
  by_cases c : f = 0
  · rw [c, map_zero, Polynomial.natDegree_zero, degreeOf_zero]
  · rw [Polynomial.natDegree, degree_finSuccEquivNth (by simpa only [Ne])]
    erw [WithBot.unbotD_coe, Nat.cast_id]

/-- The degree of `j` in the `i`th coefficient of `finSuccEquivNth R p f` is at most the degree of
`j.succ` in `f`. -/
theorem degreeOf_coeff_finSuccEquivNth (f : MvPolynomial (Fin (n + 1)) R) (j : Fin n) (i : ℕ) :
    degreeOf j (Polynomial.coeff (finSuccEquivNth R p f) i) ≤ degreeOf (p.succAbove j) f := by
  rw [degreeOf_eq_sup, degreeOf_eq_sup, Finset.sup_le_iff]
  intro m hm
  rw [← Finsupp.insertNth_apply_succAbove p i m j]
  exact Finset.le_sup (f := fun (g : Fin n.succ →₀ ℕ) => g (Fin.succAbove p j))
    (support_coeff_finSuccEquivNth.1 hm)

/-- Consider a multivariate polynomial `φ` whose variables are indexed by `Option σ`,
and suppose that `σ ≃ Fin n`.
Then one may view `φ` as a polynomial over `MvPolynomial (Fin n) R`, by

1. renaming the variables via `Option σ ≃ Fin (n+1)`, and then singling out the `p`-th variable
    via `MvPolynomial.finSuccEquivNth R p`;
2. first viewing it as polynomial over `MvPolynomial σ R` via `MvPolynomial.optionEquivLeft`,
    and then renaming the variables.

This theorem shows that both constructions are the same. -/
theorem finSuccEquivNth_rename_finSuccEquivNth (e : σ ≃ Fin n) (φ : MvPolynomial (Option σ) R) :
    ((finSuccEquivNth R p) ((rename ((Equiv.optionCongr e).trans (_root_.finSuccEquiv' p).symm)) φ))
      = Polynomial.map (rename e).toRingHom (optionEquivLeft R σ φ) := by
  suffices (finSuccEquivNth R p).toRingEquiv.toRingHom.comp (rename ((Equiv.optionCongr e).trans
        (_root_.finSuccEquiv' p).symm)).toRingHom =
      (Polynomial.mapRingHom (rename e).toRingHom).comp (optionEquivLeft R σ) by
    exact DFunLike.congr_fun this φ
  apply ringHom_ext
  · simp [finSuccEquivNth_apply, Polynomial.algebraMap_apply, algebraMap_eq, optionEquivLeft]
  · rintro (i|i) <;> simp [finSuccEquivNth_apply, optionEquivLeft]

end FinSuccEquivNth

end

end MvPolynomial
