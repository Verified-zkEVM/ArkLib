/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.TwoJetDegree
public import Mathlib.RingTheory.Nullstellensatz

/-!
# Points of the affine twoJet presentation

The truncated-triangle monomial presentation sends a source point to the values of its two-jet
monomials. Polynomial evaluation commutes with `twoJetMap`, so source hypersurfaces and
twoJet-bounded cuts may be transported to the presentation coordinates.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial

variable {F E σ : Type*} [Field F] [Field E] [Algebra F E]

/-- The point in two-jet coordinates obtained by evaluating every source monomial. -/
def twoJetPoint (b c : ℕ) (x : Fin 2 → E) : CappedTwoJetIndex b c → E :=
  fun m ↦ aeval x (MvPolynomial.monomial m.val 1 : MvPolynomial (Fin 2) F)

/-- Evaluation at the lifted point is evaluation after the two-jet presentation map. -/
theorem aeval_twoJetPoint (b c : ℕ) (x : Fin 2 → E)
    (P : MvPolynomial (CappedTwoJetIndex b c) F) :
    aeval (twoJetPoint (F := F) b c x) P = aeval x (twoJetMap b c P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [twoJetMap]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => simp [hP, twoJetPoint, twoJetMap]

/-- A twoJet-bounded source equation and its linear two-jet lift vanish at corresponding
points simultaneously. -/
theorem aeval_twoJetLift_iff (b c : ℕ) (x : Fin 2 → E)
    (q : MvPolynomial (Fin 2) F)
    (hq : q ∈ restrictTwoJet (F := F) b c) :
    aeval (twoJetPoint (F := F) b c x) (twoJetLift b c q hq) = 0 ↔
      aeval x q = 0 := by
  rw [aeval_twoJetPoint, twoJetMap_twoJetLift]

/-- Every bounded source cut becomes a linear equation upstairs, with identical pointwise
vanishing on the image of the two-jet presentation. -/
theorem twoJetLift_linear_cut (b c : ℕ) (x : Fin 2 → E)
    (q : MvPolynomial (Fin 2) F)
    (hq : q ∈ restrictTwoJet (F := F) b c) :
    (twoJetLift b c q hq).totalDegree ≤ 1 ∧
      (aeval (twoJetPoint (F := F) b c x) (twoJetLift b c q hq) = 0 ↔
        aeval x q = 0) :=
  ⟨twoJetLift_totalDegree_le_one b c q hq, aeval_twoJetLift_iff b c x q hq⟩

/-- A source point lies on `g = 0` exactly when its two-jet point lies on the lifted
hypersurface ideal. Positive side lengths supply surjectivity for the reverse implication. -/
theorem mem_zeroLocus_twoJetHypersurfaceIdeal_iff (b c : ℕ)
    (hb : 0 < b) (hc : 0 < c) (g : MvPolynomial (Fin 2) F) (x : Fin 2 → E) :
    twoJetPoint (F := F) b c x ∈ zeroLocus E (twoJetHypersurfaceIdeal b c g) ↔
      aeval x g = 0 := by
  constructor
  · intro hx
    obtain ⟨P, hP⟩ := twoJetMap_surjective (F := F) b c hb hc g
    have hker : P ∈ twoJetHypersurfaceIdeal (F := F) b c g := by
      change Ideal.Quotient.mk (Ideal.span {g}) (twoJetMap b c P) = 0
      rw [hP, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton g)
    have heval := hx P hker
    rw [aeval_twoJetPoint, hP] at heval
    exact heval
  · intro hg P hP
    rw [aeval_twoJetPoint]
    change Ideal.Quotient.mk (Ideal.span {g}) (twoJetMap b c P) = 0 at hP
    have hmem : twoJetMap b c P ∈ Ideal.span {g} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hP
    have hspan : Ideal.span ({g} : Set (MvPolynomial (Fin 2) F)) ≤
        RingHom.ker (aeval x).toRingHom := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact hg
    exact hspan hmem

/-- Equivalent zero-locus form, including the source principal ideal explicitly. -/
theorem mem_zeroLocus_twoJetHypersurfaceIdeal_iff_source (b c : ℕ)
    (hb : 0 < b) (hc : 0 < c) (g : MvPolynomial (Fin 2) F) (x : Fin 2 → E) :
    twoJetPoint (F := F) b c x ∈ zeroLocus E (twoJetHypersurfaceIdeal b c g) ↔
      x ∈ zeroLocus E (Ideal.span {g}) := by
  rw [mem_zeroLocus_twoJetHypersurfaceIdeal_iff b c hb hc g x]
  change aeval x g = 0 ↔ Ideal.span {g} ≤ RingHom.ker (aeval x).toRingHom
  rw [Ideal.span_singleton_le_iff_mem]
  rfl

/-- Every point of the two-jet presentation is induced by a source point. -/
theorem exists_twoJetPoint_of_mem_zeroLocus_twoJetIdeal (b c : ℕ)
    (hb : 0 < b) (hc : 0 < c) (z : CappedTwoJetIndex b c → E)
    (hz : z ∈ zeroLocus E (twoJetIdeal (F := F) b c)) :
    ∃ x : Fin 2 → E, twoJetPoint (F := F) b c x = z := by
  let evalz : MvPolynomial (CappedTwoJetIndex b c) F →ₐ[F] E := aeval z
  have hker : twoJetIdeal (F := F) b c ≤ RingHom.ker evalz.toRingHom := hz
  have hker' : ∀ p, p ∈ twoJetIdeal (F := F) b c → evalz p = 0 :=
    fun _ hp ↦ hker hp
  let qeval : (MvPolynomial (CappedTwoJetIndex b c) F ⧸ twoJetIdeal b c) →ₐ[F] E :=
    Ideal.Quotient.liftₐ (twoJetIdeal b c) evalz hker'
  let e₀ : (MvPolynomial (CappedTwoJetIndex b c) F ⧸ twoJetIdeal b c) ≃ₐ[F]
      MvPolynomial (Fin 2) F :=
    Ideal.quotientKerAlgEquivOfSurjective (twoJetMap_surjective b c hb hc)
  let ψ : MvPolynomial (Fin 2) F →ₐ[F] E := qeval.comp e₀.symm.toAlgHom
  let x : Fin 2 → E := fun i ↦ ψ (MvPolynomial.X i)
  have hψ : aeval x = ψ := by
    ext i
    simp [x]
  refine ⟨x, funext fun m ↦ ?_⟩
  have he₀ : e₀ (Ideal.Quotient.mk (twoJetIdeal b c)
      (MvPolynomial.X m : MvPolynomial (CappedTwoJetIndex b c) F)) =
      twoJetMap b c (MvPolynomial.X m) :=
    Ideal.quotientKerAlgEquivOfSurjective_mk (twoJetMap_surjective b c hb hc) _
  have he₀inv : e₀.symm (twoJetMap b c
      (MvPolynomial.X m : MvPolynomial (CappedTwoJetIndex b c) F)) =
      Ideal.Quotient.mk (twoJetIdeal b c) (MvPolynomial.X m) := by
    apply e₀.injective
    rw [e₀.apply_symm_apply]
    exact he₀.symm
  calc
    twoJetPoint (F := F) b c x m =
        aeval x (twoJetMap b c (MvPolynomial.X m)) := by
          simpa using (aeval_twoJetPoint (F := F) (E := E) b c x
            (MvPolynomial.X m : MvPolynomial (CappedTwoJetIndex b c) F))
    _ = ψ (twoJetMap b c (MvPolynomial.X m)) := by rw [hψ]
    _ = qeval (Ideal.Quotient.mk (twoJetIdeal b c) (MvPolynomial.X m)) := by
      change qeval (e₀.symm (twoJetMap b c (MvPolynomial.X m))) = _
      rw [he₀inv]
    _ = z m := by
      have hc := DFunLike.congr_fun
        (Ideal.Quotient.liftₐ_comp (twoJetIdeal b c) evalz hker')
        (MvPolynomial.X m)
      simpa [qeval, evalz] using hc

/-- Positive two-jet sides make the source-to-presentation point map injective. -/
theorem twoJetPoint_injective (b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    Function.Injective (twoJetPoint (F := F) (E := E) b c) := by
  intro x y hxy
  funext i
  obtain ⟨P, hP⟩ := twoJetMap_surjective (F := F) b c hb hc
    (MvPolynomial.X i : MvPolynomial (Fin 2) F)
  have he := congrArg (fun z ↦ aeval z P) hxy
  rw [aeval_twoJetPoint, aeval_twoJetPoint, hP] at he
  simpa using he

end AffineHilbert
