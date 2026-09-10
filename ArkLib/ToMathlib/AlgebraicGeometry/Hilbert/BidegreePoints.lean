/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Bidegree
public import Mathlib.RingTheory.Nullstellensatz

/-!
# Points of the affine bidegree presentation

The affine Segre--Veronese presentation sends a source point to the values of its rectangle
monomials. Polynomial evaluation commutes with `bidegreeMap`, so source hypersurfaces and
bidegree-bounded cuts may be transported to the presentation coordinates.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial

variable {F E σ : Type*} [Field F] [Field E] [Algebra F E]

/-- The point in rectangle coordinates obtained by evaluating every source monomial. -/
def bidegreePoint (a b : ℕ) (x : Option σ → E) : BidegreeIndex a b σ → E :=
  fun m ↦ aeval x (MvPolynomial.monomial m.val 1 : MvPolynomial (Option σ) F)

/-- Evaluation at the lifted point is evaluation after the rectangle presentation map. -/
theorem aeval_bidegreePoint (a b : ℕ) (x : Option σ → E)
    (P : MvPolynomial (BidegreeIndex a b σ) F) :
    aeval (bidegreePoint (F := F) a b x) P = aeval x (bidegreeMap a b P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [bidegreeMap]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => simp [hP, bidegreePoint, bidegreeMap]

/-- A bidegree-bounded source equation and its linear rectangle lift vanish at corresponding
points simultaneously. -/
theorem aeval_bidegreeLift_iff (a b : ℕ) (x : Option σ → E)
    (q : MvPolynomial (Option σ) F)
    (hq : q ∈ restrictBidegree (F := F) (σ := σ) a b) :
    aeval (bidegreePoint (F := F) a b x) (bidegreeLift a b q hq) = 0 ↔
      aeval x q = 0 := by
  rw [aeval_bidegreePoint, bidegreeMap_bidegreeLift]

/-- Every bounded source cut becomes a linear equation upstairs, with identical pointwise
vanishing on the image of the rectangle presentation. -/
theorem bidegreeLift_linear_cut (a b : ℕ) (x : Option σ → E)
    (q : MvPolynomial (Option σ) F)
    (hq : q ∈ restrictBidegree (F := F) (σ := σ) a b) :
    (bidegreeLift a b q hq).totalDegree ≤ 1 ∧
      (aeval (bidegreePoint (F := F) a b x) (bidegreeLift a b q hq) = 0 ↔
        aeval x q = 0) :=
  ⟨bidegreeLift_totalDegree_le_one a b q hq, aeval_bidegreeLift_iff a b x q hq⟩

/-- A source point lies on `g = 0` exactly when its rectangle point lies on the lifted
hypersurface ideal. Positive side lengths supply surjectivity for the reverse implication. -/
theorem mem_zeroLocus_bidegreeHypersurfaceIdeal_iff (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (g : MvPolynomial (Option σ) F) (x : Option σ → E) :
    bidegreePoint (F := F) a b x ∈ zeroLocus E (bidegreeHypersurfaceIdeal a b g) ↔
      aeval x g = 0 := by
  constructor
  · intro hx
    obtain ⟨P, hP⟩ := bidegreeMap_surjective (F := F) a b ha hb g
    have hker : P ∈ bidegreeHypersurfaceIdeal (F := F) a b g := by
      change Ideal.Quotient.mk (Ideal.span {g}) (bidegreeMap a b P) = 0
      rw [hP, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton g)
    have heval := hx P hker
    rw [aeval_bidegreePoint, hP] at heval
    exact heval
  · intro hg P hP
    rw [aeval_bidegreePoint]
    change Ideal.Quotient.mk (Ideal.span {g}) (bidegreeMap a b P) = 0 at hP
    have hmem : bidegreeMap a b P ∈ Ideal.span {g} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hP
    have hspan : Ideal.span ({g} : Set (MvPolynomial (Option σ) F)) ≤
        RingHom.ker (aeval x).toRingHom := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact hg
    exact hspan hmem

/-- Equivalent zero-locus form, including the source principal ideal explicitly. -/
theorem mem_zeroLocus_bidegreeHypersurfaceIdeal_iff_source (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (g : MvPolynomial (Option σ) F) (x : Option σ → E) :
    bidegreePoint (F := F) a b x ∈ zeroLocus E (bidegreeHypersurfaceIdeal a b g) ↔
      x ∈ zeroLocus E (Ideal.span {g}) := by
  rw [mem_zeroLocus_bidegreeHypersurfaceIdeal_iff a b ha hb g x]
  change aeval x g = 0 ↔ Ideal.span {g} ≤ RingHom.ker (aeval x).toRingHom
  rw [Ideal.span_singleton_le_iff_mem]
  rfl

/-- Every point of the rectangle presentation is induced by a source point. -/
theorem exists_bidegreePoint_of_mem_zeroLocus_bidegreeIdeal (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b) (z : BidegreeIndex a b σ → E)
    (hz : z ∈ zeroLocus E (bidegreeIdeal (F := F) (σ := σ) a b)) :
    ∃ x : Option σ → E, bidegreePoint (F := F) a b x = z := by
  let evalz : MvPolynomial (BidegreeIndex a b σ) F →ₐ[F] E := aeval z
  have hker : bidegreeIdeal (F := F) (σ := σ) a b ≤ RingHom.ker evalz.toRingHom := hz
  have hker' : ∀ p, p ∈ bidegreeIdeal (F := F) (σ := σ) a b → evalz p = 0 :=
    fun _ hp ↦ hker hp
  let qeval : (MvPolynomial (BidegreeIndex a b σ) F ⧸ bidegreeIdeal a b) →ₐ[F] E :=
    Ideal.Quotient.liftₐ (bidegreeIdeal a b) evalz hker'
  let e₀ : (MvPolynomial (BidegreeIndex a b σ) F ⧸ bidegreeIdeal a b) ≃ₐ[F]
      MvPolynomial (Option σ) F :=
    Ideal.quotientKerAlgEquivOfSurjective (bidegreeMap_surjective a b ha hb)
  let ψ : MvPolynomial (Option σ) F →ₐ[F] E := qeval.comp e₀.symm.toAlgHom
  let x : Option σ → E := fun i ↦ ψ (MvPolynomial.X i)
  have hψ : aeval x = ψ := by
    ext i
    simp [x]
  refine ⟨x, funext fun m ↦ ?_⟩
  have he₀ : e₀ (Ideal.Quotient.mk (bidegreeIdeal a b)
      (MvPolynomial.X m : MvPolynomial (BidegreeIndex a b σ) F)) =
      bidegreeMap a b (MvPolynomial.X m) :=
    Ideal.quotientKerAlgEquivOfSurjective_mk (bidegreeMap_surjective a b ha hb) _
  have he₀inv : e₀.symm (bidegreeMap a b
      (MvPolynomial.X m : MvPolynomial (BidegreeIndex a b σ) F)) =
      Ideal.Quotient.mk (bidegreeIdeal a b) (MvPolynomial.X m) := by
    apply e₀.injective
    rw [e₀.apply_symm_apply]
    exact he₀.symm
  calc
    bidegreePoint (F := F) a b x m =
        aeval x (bidegreeMap a b (MvPolynomial.X m)) := by
          simpa using (aeval_bidegreePoint (F := F) (E := E) a b x
            (MvPolynomial.X m : MvPolynomial (BidegreeIndex a b σ) F))
    _ = ψ (bidegreeMap a b (MvPolynomial.X m)) := by rw [hψ]
    _ = qeval (Ideal.Quotient.mk (bidegreeIdeal a b) (MvPolynomial.X m)) := by
      change qeval (e₀.symm (bidegreeMap a b (MvPolynomial.X m))) = _
      rw [he₀inv]
    _ = z m := by
      have hc := DFunLike.congr_fun
        (Ideal.Quotient.liftₐ_comp (bidegreeIdeal a b) evalz hker')
        (MvPolynomial.X m)
      simpa [qeval, evalz] using hc

/-- Positive rectangle sides make the source-to-presentation point map injective. -/
theorem bidegreePoint_injective (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Function.Injective (bidegreePoint (F := F) (E := E) (σ := σ) a b) := by
  intro x y hxy
  funext i
  obtain ⟨P, hP⟩ := bidegreeMap_surjective (F := F) a b ha hb
    (MvPolynomial.X i : MvPolynomial (Option σ) F)
  have he := congrArg (fun z ↦ aeval z P) hxy
  rw [aeval_bidegreePoint, aeval_bidegreePoint, hP] at he
  simpa using he

end AffineHilbert
