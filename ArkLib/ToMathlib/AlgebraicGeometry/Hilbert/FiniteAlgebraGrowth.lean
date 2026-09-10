/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Polynomial
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.PolynomialGrowthRescaling

/-!
# Filtration growth under finite injective affine algebra maps
-/

@[expose] public section

noncomputable section

open MvPolynomial

namespace AffineHilbert

private theorem totalDegree_eval₂_le {F σ τ : Type*} [Field F] [Finite τ]
    (p : τ → MvPolynomial σ F) {c N : ℕ} (hp : ∀ i, (p i).totalDegree ≤ c)
    {q : MvPolynomial τ F} (hq : q.totalDegree ≤ N) :
    (MvPolynomial.eval₂ (MvPolynomial.C : F →+* MvPolynomial σ F) p q).totalDegree ≤
      c * N := by
  let _ : Fintype τ := Fintype.ofFinite τ
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i ∈ e.support, (p i ^ e i).totalDegree ≤
        ∑ i ∈ e.support, e i * c := by
      apply Finset.sum_le_sum
      intro i _
      exact (MvPolynomial.totalDegree_pow (p i) (e i)).trans
        (Nat.mul_le_mul_left _ (hp i))
    _ = c * e.degree := by
      rw [Finsupp.degree_eq_sum, ← Finsupp.sum_fintype e (fun _ n ↦ n) (fun _ ↦ rfl)]
      simp [Finsupp.sum, Finset.mul_sum, Nat.mul_comm]
    _ ≤ c * N := Nat.mul_le_mul_left c
      ((Finset.le_sup he).trans hq)

/-- An injective affine-algebra map sends the source degree filtration into a
linearly rescaled target filtration. The rescaling constant is extracted from
polynomial representatives of the images of the source coordinates. -/
theorem hilbertFunction_le_rescaled_of_injective_algHom
    {F σ τ : Type*} [Field F] [Finite σ] [Finite τ]
    {I : Ideal (MvPolynomial σ F)} {J : Ideal (MvPolynomial τ F)}
    (g : (MvPolynomial τ F ⧸ J) →ₐ[F] (MvPolynomial σ F ⧸ I))
    (hg : Function.Injective g) :
    ∃ c > 0, ∀ N, hilbertFunction J N ≤ hilbertFunction I (c * N) := by
  classical
  let _ : Fintype τ := Fintype.ofFinite τ
  have hrep : ∀ i : τ, ∃ p : MvPolynomial σ F,
      Ideal.Quotient.mkₐ F I p = g (Ideal.Quotient.mkₐ F J (MvPolynomial.X i)) :=
    fun i ↦ Ideal.Quotient.mkₐ_surjective F I _
  choose p hp using hrep
  let c := max 1 (Finset.univ.sup fun i ↦ (p i).totalDegree)
  have hc : 0 < c := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  refine ⟨c, hc, fun N ↦ ?_⟩
  have hpdeg : ∀ i, (p i).totalDegree ≤ c := by
    intro i
    exact (Finset.le_sup (f := fun j : τ ↦ (p j).totalDegree)
      (Finset.mem_univ i)).trans (le_max_right _ _)
  let φ : MvPolynomial τ F →ₐ[F] MvPolynomial σ F :=
    MvPolynomial.aeval p
  have hφ : (Ideal.Quotient.mkₐ F I).comp φ = g.comp (Ideal.Quotient.mkₐ F J) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [AlgHom.comp_apply, φ, MvPolynomial.aeval_X] using hp i
  let L : quotientDegreeLE J N →ₗ[F] quotientDegreeLE I (c * N) :=
    (g.toLinearMap.domRestrict (quotientDegreeLE J N)).codRestrict
      (quotientDegreeLE I (c * N)) (fun x ↦ by
        obtain ⟨q, hq, hqx⟩ := x.property
        refine ⟨φ q, ?_, ?_⟩
        · apply (MvPolynomial.mem_restrictTotalDegree σ (c * N) (φ q)).mpr
          simpa only [φ, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq] using
            totalDegree_eval₂_le p hpdeg
            ((MvPolynomial.mem_restrictTotalDegree τ N q).mp hq)
        · change Ideal.Quotient.mkₐ F I (φ q) = g x
          rw [← hqx]
          exact DFunLike.congr_fun hφ q)
  have hL : Function.Injective L := by
    intro x y hxy
    apply Subtype.ext
    apply hg
    exact congrArg Subtype.val hxy
  rw [hilbertFunction, hilbertFunction]
  exact LinearMap.finrank_le_finrank_of_injective hL

/-- An injective map of affine coordinate algebras cannot decrease Hilbert dimension.

The direction is deliberate: if the coordinate algebra of one affine locus injects into
another, the source Hilbert polynomial has degree at most that of the target. -/
theorem hilbertPolynomial_natDegree_le_of_injective_algHom
    {F σ τ : Type*} [Field F] [Finite σ] [Finite τ]
    {I : Ideal (MvPolynomial σ F)} {J : Ideal (MvPolynomial τ F)}
    (g : (MvPolynomial τ F ⧸ J) →ₐ[F] (MvPolynomial σ F ⧸ I))
    (hg : Function.Injective g) (hJ : J ≠ ⊤) :
    (hilbertPolynomial J).natDegree ≤ (hilbertPolynomial I).natDegree := by
  obtain ⟨c, hc, hfun⟩ := hilbertFunction_le_rescaled_of_injective_algHom g hg
  apply natDegree_le_of_eventually_eval_nat_le_rescaled
    (hilbertPolynomial_ne_zero hJ) hc
  · filter_upwards [hilbertPolynomial_eventually_eval J] with N hN
    rw [hN]
    positivity
  · obtain ⟨NI, hI⟩ := hilbertPolynomial_eventually I
    obtain ⟨NJ, hJ⟩ := hilbertPolynomial_eventually J
    filter_upwards [Filter.eventually_ge_atTop (max NI NJ)] with N hN
    rw [hJ N ((le_max_right NI NJ).trans hN),
      hI (c * N) ((le_max_left NI NJ).trans hN |>.trans
        (Nat.le_mul_of_pos_left N hc))]
    exact_mod_cast hfun N

/-- A surjective map of affine coordinate algebras cannot increase Hilbert dimension.

The map is first presented as a further quotient of its source polynomial algebra.  Ideal
antitonicity handles that quotient, while the induced algebra equivalence identifies the target
with the quotient by the composite kernel. -/
theorem hilbertPolynomial_natDegree_le_of_surjective_algHom
    {F σ τ : Type*} [Field F] [Finite σ] [Finite τ]
    {I : Ideal (MvPolynomial σ F)} {J : Ideal (MvPolynomial τ F)}
    (g : (MvPolynomial τ F ⧸ J) →ₐ[F] (MvPolynomial σ F ⧸ I))
    (hg : Function.Surjective g) (hI : I ≠ ⊤) :
    (hilbertPolynomial I).natDegree ≤ (hilbertPolynomial J).natDegree := by
  let f : MvPolynomial τ F →ₐ[F] (MvPolynomial σ F ⧸ I) :=
    g.comp (Ideal.Quotient.mkₐ F J)
  have hf : Function.Surjective f := hg.comp (Ideal.Quotient.mkₐ_surjective F J)
  let e : (MvPolynomial τ F ⧸ RingHom.ker f) ≃ₐ[F]
      (MvPolynomial σ F ⧸ I) := Ideal.quotientKerAlgEquivOfSurjective hf
  have hker : RingHom.ker f ≠ ⊤ := by
    let _ : Nontrivial (MvPolynomial σ F ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    exact RingHom.ker_ne_top f.toRingHom
  have hJker : J ≤ RingHom.ker f := by
    intro p hp
    change g (Ideal.Quotient.mk J p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have hequiv : (hilbertPolynomial I).natDegree ≤
      (hilbertPolynomial (RingHom.ker f)).natDegree :=
    hilbertPolynomial_natDegree_le_of_injective_algHom e.symm.toAlgHom e.symm.injective hI
  exact hequiv.trans (hilbertPolynomial_degree_and_leadingCoeff_antitone hJker hker).1

private theorem exists_one_finset_module_generators
    {B A : Type*} [CommRing B] [CommRing A] [Module B A] [Module.Finite B A] :
    ∃ s : Finset A, 1 ∈ s ∧ Submodule.span B (s : Set A) = ⊤ := by
  classical
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := B) (M := A))
  let s := insert 1 hSfin.toFinset
  refine ⟨s, Finset.mem_insert_self _ _, ?_⟩
  rw [show (s : Set A) = insert 1 S by ext x; simp [s]]
  apply top_unique
  rw [← hSspan]
  exact Submodule.span_mono (Set.subset_insert 1 S)

/-- If the target quotient is finite as a module over the source quotient,
its degree filtration grows at most like a fixed finite multiple of a linear
rescaling of the source filtration. -/
theorem hilbertFunction_le_mul_rescaled_of_finite
    {F σ τ : Type*} [Field F] [Finite σ] [Finite τ]
    {I : Ideal (MvPolynomial σ F)} {J : Ideal (MvPolynomial τ F)}
    [Algebra (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I)]
    [IsScalarTower F (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I)]
    [Module.Finite (MvPolynomial τ F ⧸ J) (MvPolynomial σ F ⧸ I)] :
    ∃ c > 0, ∃ m > 0, ∀ N,
      hilbertFunction I N ≤ m * hilbertFunction J (c * (N + 1)) := by
  classical
  let B := MvPolynomial τ F ⧸ J
  let A := MvPolynomial σ F ⧸ I
  let _ : Fintype σ := Fintype.ofFinite σ
  let _ : Fintype τ := Fintype.ofFinite τ
  obtain ⟨s, hsone, hsspan⟩ :=
    exists_one_finset_module_generators (B := B) (A := A)
  have hcoords : ∀ x : A, ∃ a : s → B, ∑ i, a i • (i : A) = x := by
    intro x
    apply (Submodule.mem_span_range_iff_exists_fun
      (v := fun i : s ↦ (i : A)) (x := x) B).mp
    have hrange : Set.range (fun i : s ↦ (i : A)) = (s : Set A) := by
      ext y
      simp
    rw [hrange, hsspan]
    trivial
  choose a ha using fun j : σ ↦ fun i : s ↦
    hcoords (Ideal.Quotient.mkₐ F I (MvPolynomial.X j) * (i : A))
  have hrep : ∀ (j : σ) (i l : s), ∃ p : MvPolynomial τ F,
      Ideal.Quotient.mkₐ F J p = a j i l := fun j i l ↦
    Ideal.Quotient.mkₐ_surjective F J _
  choose p hp using hrep
  let C₀ := Finset.univ.sup fun j : σ ↦
    Finset.univ.sup fun i : s ↦ Finset.univ.sup fun l : s ↦ (p j i l).totalDegree
  let c := max 1 C₀
  have hc : 0 < c := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hpdeg (j : σ) (i l : s) : (p j i l).totalDegree ≤ c := by
    apply le_trans _ (le_max_right 1 C₀)
    exact (Finset.le_sup (f := fun j : σ ↦
      Finset.univ.sup fun i : s ↦ Finset.univ.sup fun l : s ↦
        (p j i l).totalDegree) (Finset.mem_univ j)).trans' <|
      (Finset.le_sup (f := fun i : s ↦ Finset.univ.sup fun l : s ↦
        (p j i l).totalDegree) (Finset.mem_univ i)).trans' <|
          Finset.le_sup (f := fun l : s ↦ (p j i l).totalDegree) (Finset.mem_univ l)
  have hmonomial : ∀ (e : σ →₀ ℕ) (r : F), ∃ q : s → MvPolynomial τ F,
      (∀ i, (q i).totalDegree ≤ c * (e.degree + 1)) ∧
      Ideal.Quotient.mkₐ F I (MvPolynomial.monomial e r) =
        ∑ i, algebraMap B A (Ideal.Quotient.mkₐ F J (q i)) * (i : A) := by
    intro e r
    obtain ⟨q, hqdeg, hq⟩ := MvPolynomial.induction_on_monomial (motive := fun v ↦
      ∃ q : s → MvPolynomial τ F,
        (∀ i, (q i).totalDegree ≤ c * (v.totalDegree + 1)) ∧
        Ideal.Quotient.mkₐ F I v =
          ∑ i, algebraMap B A (Ideal.Quotient.mkₐ F J (q i)) * (i : A))
      (fun r ↦ by
        let one : s := ⟨1, hsone⟩
        let q : s → MvPolynomial τ F := fun i ↦ if i = one then MvPolynomial.C r else 0
        refine ⟨q, ?_, ?_⟩
        · intro i
          by_cases hi : i = one <;> simp [q, hi]
        · rw [show (∑ i, algebraMap B A (Ideal.Quotient.mkₐ F J (q i)) * (i : A)) =
              algebraMap B A (Ideal.Quotient.mkₐ F J (MvPolynomial.C r)) * (one : A) by
            calc
              _ = ∑ i : s, if i = one then
                    algebraMap B A (Ideal.Quotient.mkₐ F J (MvPolynomial.C r)) * (i : A)
                  else 0 := by
                apply Finset.sum_congr rfl
                intro i _
                by_cases hi : i = one <;> simp [q, hi]
              _ = _ := Fintype.sum_ite_eq' one _]
          simpa [one] using IsScalarTower.algebraMap_apply F B A r)
      (fun v j hv ↦ by
        by_cases hv0 : v = 0
        · subst v
          refine ⟨fun _ ↦ 0, by simp, by simp⟩
        obtain ⟨q, hqdeg, hq⟩ := hv
        let q' : s → MvPolynomial τ F := fun l ↦ ∑ i, q i * p j i l
        refine ⟨q', ?_, ?_⟩
        · intro l
          apply MvPolynomial.totalDegree_finsetSum_le
          intro i _
          exact (MvPolynomial.totalDegree_mul _ _).trans <| calc
            (q i).totalDegree + (p j i l).totalDegree ≤
                c * (v.totalDegree + 1) + c :=
              Nat.add_le_add (hqdeg i) (hpdeg j i l)
            _ = c * ((v * MvPolynomial.X j).totalDegree + 1) := by
              rw [MvPolynomial.totalDegree_mul_of_isDomain hv0
                (MvPolynomial.X_ne_zero j), MvPolynomial.totalDegree_X]
              ring
        · rw [map_mul, hq]
          simp only [q', map_sum, map_mul, hp]
          calc
            (∑ i, algebraMap B A (Ideal.Quotient.mkₐ F J (q i)) * (i : A)) *
                Ideal.Quotient.mkₐ F I (MvPolynomial.X j) =
                ∑ i, algebraMap B A (Ideal.Quotient.mkₐ F J (q i)) *
                  (∑ l, algebraMap B A (a j i l) * (l : A)) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i _
              have hi := ha j i
              simp only [Algebra.smul_def] at hi
              rw [hi]
              ring
            _ = ∑ i, ∑ x, algebraMap B A (Ideal.Quotient.mkₐ F J (q i)) *
                  algebraMap B A (a j i x) * (x : A) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              simp only [mul_assoc]
            _ = ∑ x, ∑ i, algebraMap B A (Ideal.Quotient.mkₐ F J (q i)) *
                  algebraMap B A (a j i x) * (x : A) := Finset.sum_comm
            _ = ∑ x, (∑ i, algebraMap B A (Ideal.Quotient.mkₐ F J (q i)) *
                  algebraMap B A (a j i x)) * (x : A) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [Finset.sum_mul])
      e r
    refine ⟨q, ?_, hq⟩
    intro i
    exact (hqdeg i).trans (Nat.mul_le_mul_left c
      (Nat.add_le_add_right (MvPolynomial.totalDegree_monomial_le e r) 1))
  have hpolynomial : ∀ v : MvPolynomial σ F, ∃ q : s → MvPolynomial τ F,
      (∀ i, (q i).totalDegree ≤ c * (v.totalDegree + 1)) ∧
      Ideal.Quotient.mkₐ F I v =
        ∑ i, algebraMap B A (Ideal.Quotient.mkₐ F J (q i)) * (i : A) := by
    intro v
    choose q hqdeg hq using fun e : σ →₀ ℕ ↦ hmonomial e (MvPolynomial.coeff e v)
    let Q : s → MvPolynomial τ F := fun i ↦ ∑ e ∈ v.support, q e i
    refine ⟨Q, ?_, ?_⟩
    · intro i
      apply MvPolynomial.totalDegree_finsetSum_le
      intro e he
      exact (hqdeg e i).trans (Nat.mul_le_mul_left c
        (Nat.add_le_add_right (Finset.le_sup he) 1))
    · rw [MvPolynomial.as_sum v, map_sum]
      simp only [map_sum, hq, Q]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
  refine ⟨c, hc, s.card, Finset.card_pos.mpr ⟨1, hsone⟩, fun N ↦ ?_⟩
  let K := quotientDegreeLE J (c * (N + 1))
  let ell : s → K →ₗ[F] A := fun i ↦
    (LinearMap.mulRight F (i : A)).comp
      ((IsScalarTower.toAlgHom F B A).toLinearMap.comp K.subtype)
  let L : (s → K) →ₗ[F] A := LinearMap.lsum F (fun _ : s ↦ K) F ell
  have hfiltration : quotientDegreeLE I N ≤ L.range := by
    intro x hx
    obtain ⟨v, hvdeg, hvx⟩ := hx
    obtain ⟨q, hqdeg, hq⟩ := hpolynomial v
    let z : s → K := fun i ↦ ⟨Ideal.Quotient.mkₐ F J (q i), by
      refine ⟨q i, ?_, rfl⟩
      exact (MvPolynomial.mem_restrictTotalDegree τ (c * (N + 1)) (q i)).mpr
        ((hqdeg i).trans (Nat.mul_le_mul_left c (Nat.add_le_add_right
          ((MvPolynomial.mem_restrictTotalDegree σ N v).mp hvdeg) 1)))⟩
    refine ⟨z, ?_⟩
    simpa [L, ell, z] using hq.symm.trans hvx
  rw [hilbertFunction, hilbertFunction]
  calc
    Module.finrank F ↥(quotientDegreeLE I N) ≤ Module.finrank F ↥L.range :=
      Submodule.finrank_mono hfiltration
    _ ≤ Module.finrank F (s → K) := L.finrank_range_le
    _ = ∑ _i : s, Module.finrank F K := Module.finrank_pi_fintype F
    _ = s.card * Module.finrank F K := by simp

end AffineHilbert
