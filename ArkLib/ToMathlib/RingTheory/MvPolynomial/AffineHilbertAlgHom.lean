/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPolynomial
public import Mathlib.Data.Fintype.Order
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Affine Hilbert polynomials under algebra maps

Let `k` be a field, `σ` and `τ` finite types, `I` an ideal of `MvPolynomial σ k` and `J` an ideal
of `MvPolynomial τ k`, and let `g : MvPolynomial τ k ⧸ J →ₐ[k] MvPolynomial σ k ⧸ I` be a map of
`k`-algebras. Write `H(I, N)` for `affineHilbertFunction I N` and `P_I` for
`affineHilbertPolynomial I`.

If the images under `g` of the variables of `MvPolynomial τ k ⧸ J` lie in the `c`-th piece of the
filtration of `MvPolynomial σ k ⧸ I`, then `g` maps the `N`-th piece into the `(c * N)`-th piece.
So an injective `g` gives `H(J, N) ≤ H(I, c * N)`, and hence `natDegree P_J ≤ natDegree P_I`.
If instead `g` is finite, that is, `MvPolynomial σ k ⧸ I` is a finitely generated module over
`MvPolynomial τ k ⧸ J` through `g`, then `H(I, N) ≤ m * H(J, c * N)` for constants `m, c > 0`,
and hence `natDegree P_I ≤ natDegree P_J`. A surjective `g` is finite, and a finite injective `g`
preserves the natural degree of the affine Hilbert polynomial.

Both filtration bounds are instances of `MvPolynomial.aeval_mem_of_forall_mul_mem`: a family of
submodules `T M` that contains `1` at `M = 0` and is moved from `T M` into `T (M + c)` by
multiplication by each `y i` contains `aeval y q` in `T (c * N)` whenever `q` has total degree at
most `N`. For the finite case, `T M` consists of the combinations `∑ l, g (b l) * l` over a finite
generating set containing `1`, with each `b l` in the `M`-th piece of the filtration of
`MvPolynomial τ k ⧸ J`.

The finite case is stated for an algebra map `g` with `g.Finite`. For an `Algebra` instance with
`IsScalarTower` and `Module.Finite`, apply it to `IsScalarTower.toAlgHom` using
`RingHom.finite_algebraMap`. None of the degree comparisons assumes that `I` or `J` is proper.

## Main statements

* `MvPolynomial.aeval_mem_of_forall_mul_mem`: the filtration bound for `aeval`.
* `MvPolynomial.map_mem_quotientDegreeLE`: an algebra map with the images of the variables in the
  `c`-th piece maps the `N`-th piece into the `(c * N)`-th piece.
* `MvPolynomial.affineHilbertFunction_le_of_injective`,
  `MvPolynomial.exists_affineHilbertFunction_le_of_injective`: the Hilbert-function bound for an
  injective map.
* `MvPolynomial.exists_affineHilbertFunction_le_mul_of_finite`: the Hilbert-function bound for a
  finite map.
* `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_eventually_le_mul`: an eventual bound
  `H(I, N) ≤ m * H(J, c * N)` with `c > 0` compares natural degrees.
* `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_injective`,
  `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_finite`,
  `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_surjective`,
  `MvPolynomial.natDegree_affineHilbertPolynomial_eq_of_finite_of_injective`: the degree
  comparisons.
-/

@[expose] public section

noncomputable section

open Filter Polynomial

namespace MvPolynomial

section Aeval

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- Let `T : ℕ → Submodule R S` be monotone with `1 ∈ T 0`, and suppose that multiplication by
each `y i` maps `T M` into `T (M + c)`. Then `aeval y q ∈ T (c * N)` for every `q` of total degree
at most `N`.

Each monomial `r • ∏ i, y i ^ e i` is reached from `1 ∈ T 0` by `∑ i, e i` multiplications by the
`y i`, which lands in `T (c * ∑ i, e i)`, and `∑ i, e i ≤ N`. The hypothesis `1 ∈ T 0` is needed
for the constant term. -/
theorem aeval_mem_of_forall_mul_mem (y : σ → S) {T : ℕ → Submodule R S} (hT : Monotone T)
    (h1 : (1 : S) ∈ T 0) {c : ℕ} (hmul : ∀ i M t, t ∈ T M → y i * t ∈ T (M + c))
    {q : MvPolynomial σ R} {N : ℕ} (hq : q.totalDegree ≤ N) : aeval y q ∈ T (c * N) := by
  classical
  have hpow : ∀ i n M t, t ∈ T M → y i ^ n * t ∈ T (M + c * n) := by
    intro i n
    induction n with
    | zero => intro M t ht; simpa using ht
    | succ n ih =>
      intro M t ht
      rw [pow_succ', mul_assoc, Nat.mul_succ, ← Nat.add_assoc]
      exact hmul i _ _ (ih M t ht)
  have hprod : ∀ (e : σ →₀ ℕ) (s : Finset σ) M t, t ∈ T M →
      (∏ i ∈ s, y i ^ e i) * t ∈ T (M + c * ∑ i ∈ s, e i) := by
    intro e s
    induction s using Finset.induction_on with
    | empty => intro M t ht; simpa using ht
    | insert j s hj ih =>
      intro M t ht
      rw [Finset.prod_insert hj, Finset.sum_insert hj, mul_assoc, Nat.mul_add,
        Nat.add_comm (c * e j), ← Nat.add_assoc]
      exact hpow j (e j) _ _ (ih M t ht)
  rw [q.as_sum, map_sum]
  refine Submodule.sum_mem _ fun e he ↦ ?_
  rw [aeval_monomial, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have h := hprod e e.support 0 1 h1
  rw [mul_one, Nat.zero_add] at h
  exact hT (Nat.mul_le_mul_left c ((le_totalDegree he).trans hq)) h

end Aeval

variable {k σ τ : Type*} [Field k] {I : Ideal (MvPolynomial σ k)} {J : Ideal (MvPolynomial τ k)}

/-- If an algebra map `g` sends the class of every variable into the `c`-th piece of the
filtration, then it sends the `N`-th piece into the `(c * N)`-th piece. The filtration is
multiplicative (`mul_mem_quotientDegreeLE`), and a class of total degree at most `N` is a
polynomial of degree at most `N` in the classes of the variables. -/
theorem map_mem_quotientDegreeLE (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I))
    {c : ℕ} (hc : ∀ i, g (Ideal.Quotient.mk J (X i)) ∈ quotientDegreeLE I c) {N : ℕ}
    {x : MvPolynomial τ k ⧸ J} (hx : x ∈ quotientDegreeLE J N) :
    g x ∈ quotientDegreeLE I (c * N) := by
  obtain ⟨q, hq, rfl⟩ := mem_quotientDegreeLE.mp hx
  have hg : g (Ideal.Quotient.mk J q) = aeval (fun i ↦ g (Ideal.Quotient.mk J (X i))) q :=
    DFunLike.congr_fun (aeval_unique (g.comp (Ideal.Quotient.mkₐ k J))) q
  rw [hg]
  exact aeval_mem_of_forall_mul_mem _ (quotientDegreeLE_mono I) (one_mem_quotientDegreeLE I 0)
    (fun i M _ ht ↦ Nat.add_comm c M ▸ mul_mem_quotientDegreeLE (hc i) ht) hq

/-- An injective algebra map that sends the class of every variable into the `c`-th piece of the
filtration gives `H(J, N) ≤ H(I, c * N)`: it embeds the `N`-th piece for `J` into the
`(c * N)`-th piece for `I`. Only `σ` needs to be finite, so that the target piece is
finite-dimensional. -/
theorem affineHilbertFunction_le_of_injective [Finite σ]
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I)) (hg : Function.Injective g)
    {c : ℕ} (hc : ∀ i, g (Ideal.Quotient.mk J (X i)) ∈ quotientDegreeLE I c) (N : ℕ) :
    affineHilbertFunction J N ≤ affineHilbertFunction I (c * N) := by
  let L : quotientDegreeLE J N →ₗ[k] quotientDegreeLE I (c * N) :=
    (g.toLinearMap.domRestrict (quotientDegreeLE J N)).codRestrict _
      fun x ↦ map_mem_quotientDegreeLE g hc x.2
  exact LinearMap.finrank_le_finrank_of_injective (f := L)
    fun x y hxy ↦ Subtype.ext (hg (congrArg Subtype.val hxy))

/-- An injective algebra map gives a positive constant `c` with `H(J, N) ≤ H(I, c * N)` for all
`N`. The constant is any level of the filtration containing the images of the finitely many
variables, and at least `1`. -/
theorem exists_affineHilbertFunction_le_of_injective [Finite σ] [Finite τ]
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I)) (hg : Function.Injective g) :
    ∃ c, 0 < c ∧ ∀ N, affineHilbertFunction J N ≤ affineHilbertFunction I (c * N) := by
  choose n hn using fun i : τ ↦ exists_mem_quotientDegreeLE I (g (Ideal.Quotient.mk J (X i)))
  obtain ⟨M, hM⟩ := Finite.exists_le n
  exact ⟨max 1 M, lt_max_of_lt_left Nat.one_pos, affineHilbertFunction_le_of_injective g hg
    fun i ↦ quotientDegreeLE_mono I ((hM i).trans (le_max_right 1 M)) (hn i)⟩

/-- If `MvPolynomial σ k ⧸ I` is a finite module over `MvPolynomial τ k ⧸ J` through `g`, there are
positive constants `m` and `c` with `H(I, N) ≤ m * H(J, c * N)` for all `N`.

Choose a finite generating set `s` containing `1`, and write each product of the class of a
variable with a generator as a combination `∑ l, g (a l) * l`. If `c` bounds the filtration levels
of the finitely many coefficients `a l`, the combinations `∑ l, g (b l) * l` with every `b l` in the
`M`-th piece form a subspace `T M` of dimension at most `s.card * H(J, M)`, and multiplication by
the class of a variable maps `T M` into `T (M + c)`. So the `N`-th piece for `I` lies in
`T (c * N)`, and `m = s.card`. -/
theorem exists_affineHilbertFunction_le_mul_of_finite [Finite σ] [Finite τ]
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I)) (hg : g.Finite) :
    ∃ m c, 0 < m ∧ 0 < c ∧
      ∀ N, affineHilbertFunction I N ≤ m * affineHilbertFunction J (c * N) := by
  classical
  let _ : Algebra (MvPolynomial τ k ⧸ J) (MvPolynomial σ k ⧸ I) := g.toRingHom.toAlgebra
  have hfin : Module.Finite (MvPolynomial τ k ⧸ J) (MvPolynomial σ k ⧸ I) := hg
  obtain ⟨s₀, hs₀⟩ := hfin.fg_top
  set s := insert (1 : MvPolynomial σ k ⧸ I) s₀ with hs_def
  have hone : (1 : MvPolynomial σ k ⧸ I) ∈ s := Finset.mem_insert_self _ _
  have hspan : ∀ x : MvPolynomial σ k ⧸ I, ∃ a : s → MvPolynomial τ k ⧸ J,
      ∑ l, g (a l) * (l : MvPolynomial σ k ⧸ I) = x := by
    intro x
    have hx : x ∈ Submodule.span (MvPolynomial τ k ⧸ J)
        (Set.range fun l : s ↦ (l : MvPolynomial σ k ⧸ I)) := by
      rw [Subtype.range_coe_subtype, Finset.setOfPred_mem]
      exact Submodule.span_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _))
        (hs₀.symm ▸ Submodule.mem_top)
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hx
    exact ⟨a, ha⟩
  choose a ha using fun (i : σ) (l : s) ↦ hspan (Ideal.Quotient.mk I (X i) * l)
  choose n hn using fun (p : σ × s × s) ↦ exists_mem_quotientDegreeLE J (a p.1 p.2.1 p.2.2)
  obtain ⟨M₀, hM₀⟩ := Finite.exists_le n
  set c := max 1 M₀
  have ha_mem : ∀ i l l', a i l l' ∈ quotientDegreeLE J c := fun i l l' ↦
    quotientDegreeLE_mono J ((hM₀ (i, l, l')).trans (le_max_right 1 M₀)) (hn (i, l, l'))
  -- The subspaces `T M` and their description by coefficients.
  let L : ∀ M, (s → quotientDegreeLE J M) →ₗ[k] MvPolynomial σ k ⧸ I := fun M ↦
    ∑ l : s, (LinearMap.mulRight k (l : MvPolynomial σ k ⧸ I)).comp
      ((g.toLinearMap.comp (quotientDegreeLE J M).subtype).comp (LinearMap.proj l))
  have hL : ∀ M z, L M z = ∑ l, g (z l) * (l : MvPolynomial σ k ⧸ I) := by
    intro M z
    simp [L]
  let T : ℕ → Submodule k (MvPolynomial σ k ⧸ I) := fun M ↦ LinearMap.range (L M)
  have hmemT : ∀ M t, t ∈ T M ↔ ∃ b : s → MvPolynomial τ k ⧸ J,
      (∀ l, b l ∈ quotientDegreeLE J M) ∧ ∑ l, g (b l) * (l : MvPolynomial σ k ⧸ I) = t := by
    intro M t
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨fun l ↦ z l, fun l ↦ (z l).2, (hL M z).symm⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨fun l ↦ ⟨b l, hb l⟩, hL M _⟩
  have hT : Monotone T := by
    intro M M' hMM' t ht
    obtain ⟨b, hb, rfl⟩ := (hmemT M t).mp ht
    exact (hmemT M' _).mpr ⟨b, fun l ↦ quotientDegreeLE_mono J hMM' (hb l), rfl⟩
  have h1 : (1 : MvPolynomial σ k ⧸ I) ∈ T 0 := by
    refine (hmemT 0 1).mpr ⟨Pi.single ⟨1, hone⟩ 1, fun l ↦ ?_, ?_⟩
    · by_cases hl : l = ⟨1, hone⟩
      · subst hl; simpa using one_mem_quotientDegreeLE J 0
      · simp [hl]
    · rw [Finset.sum_eq_single ⟨1, hone⟩ (fun l _ hl ↦ by simp [hl])
        (by simp)]
      simp
  have hmul : ∀ i M t, t ∈ T M → Ideal.Quotient.mk I (X i) * t ∈ T (M + c) := by
    intro i M t ht
    obtain ⟨b, hb, rfl⟩ := (hmemT M _).mp ht
    refine (hmemT (M + c) _).mpr ⟨fun l' ↦ ∑ l, b l * a i l l', fun l' ↦
      Submodule.sum_mem _ fun l _ ↦ mul_mem_quotientDegreeLE (hb l) (ha_mem i l l'), ?_⟩
    calc ∑ l', g (∑ l, b l * a i l l') * (l' : MvPolynomial σ k ⧸ I)
        = ∑ l, g (b l) * ∑ l', g (a i l l') * (l' : MvPolynomial σ k ⧸ I) := by
          simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
      _ = Ideal.Quotient.mk I (X i) * ∑ l, g (b l) * (l : MvPolynomial σ k ⧸ I) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ ↦ ?_
          rw [ha i l]
          ring
  refine ⟨Fintype.card s, c, Fintype.card_pos_iff.mpr ⟨⟨1, hone⟩⟩,
    lt_max_of_lt_left Nat.one_pos, fun N ↦ ?_⟩
  have hle : quotientDegreeLE I N ≤ T (c * N) := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := mem_quotientDegreeLE.mp hx
    have hq' : Ideal.Quotient.mk I q = aeval (fun i ↦ Ideal.Quotient.mk I (X i)) q :=
      DFunLike.congr_fun (aeval_unique (Ideal.Quotient.mkₐ k I)) q
    rw [hq']
    exact aeval_mem_of_forall_mul_mem _ hT h1 hmul hq
  calc affineHilbertFunction I N ≤ Module.finrank k (T (c * N)) := Submodule.finrank_mono hle
    _ ≤ Module.finrank k (s → quotientDegreeLE J (c * N)) := LinearMap.finrank_range_le _
    _ = Fintype.card s * affineHilbertFunction J (c * N) := by
      rw [Module.finrank_pi_fintype, Finset.sum_const, smul_eq_mul, Finset.card_univ]
      rfl

/-- An eventual bound `H(I, N) ≤ m * H(J, c * N)` with `c > 0` gives
`natDegree P_I ≤ natDegree P_J`. The polynomials agree with the Hilbert functions from some degree
on, and `c * N` tends to infinity with `N` because `c > 0`; the conclusion then follows from
`Polynomial.natDegree_le_of_eventually_eval_natCast_le_mul_eval_affine`. The hypothesis `c > 0` is
needed: for `c = 0` the bound only says that `H(I, N)` is bounded. -/
theorem natDegree_affineHilbertPolynomial_le_of_eventually_le_mul [Finite σ] [Finite τ]
    {m c : ℕ} (hc : 0 < c)
    (h : ∀ᶠ N : ℕ in atTop, affineHilbertFunction I N ≤ m * affineHilbertFunction J (c * N)) :
    (affineHilbertPolynomial I).natDegree ≤ (affineHilbertPolynomial J).natDegree := by
  have htend : Tendsto (fun N : ℕ ↦ c * N) atTop atTop :=
    tendsto_atTop_mono (fun N ↦ Nat.le_mul_of_pos_left N hc) tendsto_id
  refine natDegree_le_of_eventually_eval_natCast_le_mul_eval_affine (m := (m : ℚ))
    (c := (c : ℚ)) (d := 0) (eventually_eval_affineHilbertPolynomial_nonneg I) ?_
  filter_upwards [h, eventually_eval_affineHilbertPolynomial I,
    htend.eventually (eventually_eval_affineHilbertPolynomial J)] with N hN hI hJ
  rw [add_zero, hI, show (c : ℚ) * N = ((c * N : ℕ) : ℚ) by push_cast; ring, hJ]
  exact_mod_cast hN

/-- An injective algebra map `MvPolynomial τ k ⧸ J →ₐ[k] MvPolynomial σ k ⧸ I` gives
`natDegree P_J ≤ natDegree P_I`: a subalgebra has no larger dimension. -/
theorem natDegree_affineHilbertPolynomial_le_of_injective [Finite σ] [Finite τ]
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I)) (hg : Function.Injective g) :
    (affineHilbertPolynomial J).natDegree ≤ (affineHilbertPolynomial I).natDegree := by
  obtain ⟨c, hc, h⟩ := exists_affineHilbertFunction_le_of_injective g hg
  exact natDegree_affineHilbertPolynomial_le_of_eventually_le_mul (m := 1) hc
    (Eventually.of_forall fun N ↦ (Nat.one_mul _).symm ▸ h N)

/-- A finite algebra map `MvPolynomial τ k ⧸ J →ₐ[k] MvPolynomial σ k ⧸ I` gives
`natDegree P_I ≤ natDegree P_J`: a finite extension has no larger dimension. Injectivity is not
needed. -/
theorem natDegree_affineHilbertPolynomial_le_of_finite [Finite σ] [Finite τ]
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I)) (hg : g.Finite) :
    (affineHilbertPolynomial I).natDegree ≤ (affineHilbertPolynomial J).natDegree := by
  obtain ⟨m, c, -, hc, h⟩ := exists_affineHilbertFunction_le_mul_of_finite g hg
  exact natDegree_affineHilbertPolynomial_le_of_eventually_le_mul hc (Eventually.of_forall h)

/-- A surjective algebra map `MvPolynomial τ k ⧸ J →ₐ[k] MvPolynomial σ k ⧸ I` gives
`natDegree P_I ≤ natDegree P_J`, since a surjective map is finite. -/
theorem natDegree_affineHilbertPolynomial_le_of_surjective [Finite σ] [Finite τ]
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I)) (hg : Function.Surjective g) :
    (affineHilbertPolynomial I).natDegree ≤ (affineHilbertPolynomial J).natDegree :=
  natDegree_affineHilbertPolynomial_le_of_finite g (AlgHom.Finite.of_surjective g hg)

/-- A finite injective algebra map `MvPolynomial τ k ⧸ J →ₐ[k] MvPolynomial σ k ⧸ I` preserves
the natural degree of the affine Hilbert polynomial. Both hypotheses are needed: the inclusion of
`k[x]` into `k[x, y]` is injective but not finite, and the quotient map `k[x] → k[x] ⧸ (x)` is
finite but not injective. -/
theorem natDegree_affineHilbertPolynomial_eq_of_finite_of_injective [Finite σ] [Finite τ]
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I)) (hfin : g.Finite)
    (hinj : Function.Injective g) :
    (affineHilbertPolynomial I).natDegree = (affineHilbertPolynomial J).natDegree :=
  le_antisymm (natDegree_affineHilbertPolynomial_le_of_finite g hfin)
    (natDegree_affineHilbertPolynomial_le_of_injective g hinj)

end MvPolynomial
