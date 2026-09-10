/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.DerivativeBidegree
public import Mathlib.RingTheory.Nullstellensatz

/-! Pointwise transport for the capped challenge/jet presentation. -/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

def derivativeBidegreePoint (a b c : ℕ) (x : Option (Fin 2) → E) :
    DerivativeBidegreeIndex a b c → E :=
  fun m ↦ aeval x (MvPolynomial.monomial m.val 1 : MvPolynomial (Option (Fin 2)) F)

theorem aeval_derivativeBidegreePoint (a b c : ℕ) (x : Option (Fin 2) → E)
    (P : MvPolynomial (DerivativeBidegreeIndex a b c) F) :
    aeval (derivativeBidegreePoint (F := F) a b c x) P =
      aeval x (derivativeBidegreeMap a b c P) := by
  induction P using MvPolynomial.induction_on with
  | C d => simp [derivativeBidegreeMap]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP => simp [hP, derivativeBidegreePoint, derivativeBidegreeMap]

theorem aeval_derivativeBidegreeLift_iff (a b c : ℕ) (x : Option (Fin 2) → E)
    (q : MvPolynomial (Option (Fin 2)) F)
    (hq : q ∈ restrictDerivativeBidegree (F := F) a b c) :
    aeval (derivativeBidegreePoint (F := F) a b c x)
        (derivativeBidegreeLift a b c q hq) = 0 ↔ aeval x q = 0 := by
  rw [aeval_derivativeBidegreePoint, derivativeBidegreeMap_derivativeBidegreeLift]

theorem mem_zeroLocus_derivativeBidegreeHypersurfaceIdeal_iff
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (g : MvPolynomial (Option (Fin 2)) F) (x : Option (Fin 2) → E) :
    derivativeBidegreePoint (F := F) a b c x ∈
        zeroLocus E (derivativeBidegreeHypersurfaceIdeal a b c g) ↔
      aeval x g = 0 := by
  constructor
  · intro hx
    obtain ⟨P, hP⟩ := derivativeBidegreeMap_surjective (F := F) a b c ha hb hc g
    have hker : P ∈ derivativeBidegreeHypersurfaceIdeal (F := F) a b c g := by
      change Ideal.Quotient.mk (Ideal.span {g}) (derivativeBidegreeMap a b c P) = 0
      rw [hP, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton g)
    have heval := hx P hker
    rw [aeval_derivativeBidegreePoint, hP] at heval
    exact heval
  · intro hg P hP
    rw [aeval_derivativeBidegreePoint]
    change Ideal.Quotient.mk (Ideal.span {g}) (derivativeBidegreeMap a b c P) = 0 at hP
    have hmem : derivativeBidegreeMap a b c P ∈ Ideal.span {g} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hP
    have hspan : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 2)) F)) ≤
        RingHom.ker (aeval x).toRingHom := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact hg
    exact hspan hmem

theorem exists_derivativeBidegreePoint_of_mem_zeroLocus_derivativeBidegreeIdeal
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (z : DerivativeBidegreeIndex a b c → E)
    (hz : z ∈ zeroLocus E (derivativeBidegreeIdeal (F := F) a b c)) :
    ∃ x : Option (Fin 2) → E, derivativeBidegreePoint (F := F) a b c x = z := by
  let evalz : MvPolynomial (DerivativeBidegreeIndex a b c) F →ₐ[F] E := aeval z
  have hker : derivativeBidegreeIdeal (F := F) a b c ≤ RingHom.ker evalz.toRingHom := hz
  have hker' : ∀ p, p ∈ derivativeBidegreeIdeal (F := F) a b c → evalz p = 0 :=
    fun _ hp ↦ hker hp
  let qeval : (MvPolynomial (DerivativeBidegreeIndex a b c) F ⧸
      derivativeBidegreeIdeal a b c) →ₐ[F] E :=
    Ideal.Quotient.liftₐ (derivativeBidegreeIdeal a b c) evalz hker'
  let e₀ : (MvPolynomial (DerivativeBidegreeIndex a b c) F ⧸
      derivativeBidegreeIdeal a b c) ≃ₐ[F] MvPolynomial (Option (Fin 2)) F :=
    Ideal.quotientKerAlgEquivOfSurjective
      (derivativeBidegreeMap_surjective a b c ha hb hc)
  let ψ : MvPolynomial (Option (Fin 2)) F →ₐ[F] E := qeval.comp e₀.symm.toAlgHom
  let x : Option (Fin 2) → E := fun i ↦ ψ (MvPolynomial.X i)
  have hψ : aeval x = ψ := by
    ext i
    simp [x]
  refine ⟨x, funext fun m ↦ ?_⟩
  have he₀ : e₀ (Ideal.Quotient.mk (derivativeBidegreeIdeal a b c)
      (MvPolynomial.X m : MvPolynomial (DerivativeBidegreeIndex a b c) F)) =
      derivativeBidegreeMap a b c (MvPolynomial.X m) :=
    Ideal.quotientKerAlgEquivOfSurjective_mk
      (derivativeBidegreeMap_surjective a b c ha hb hc) _
  have he₀inv : e₀.symm (derivativeBidegreeMap a b c
      (MvPolynomial.X m : MvPolynomial (DerivativeBidegreeIndex a b c) F)) =
      Ideal.Quotient.mk (derivativeBidegreeIdeal a b c) (MvPolynomial.X m) := by
    apply e₀.injective
    rw [e₀.apply_symm_apply]
    exact he₀.symm
  calc
    derivativeBidegreePoint (F := F) a b c x m =
        aeval x (derivativeBidegreeMap a b c (MvPolynomial.X m)) := by
          simpa using aeval_derivativeBidegreePoint (F := F) (E := E) a b c x
            (MvPolynomial.X m : MvPolynomial (DerivativeBidegreeIndex a b c) F)
    _ = ψ (derivativeBidegreeMap a b c (MvPolynomial.X m)) := by rw [hψ]
    _ = qeval (Ideal.Quotient.mk (derivativeBidegreeIdeal a b c)
        (MvPolynomial.X m)) := by
      change qeval (e₀.symm (derivativeBidegreeMap a b c (MvPolynomial.X m))) = _
      rw [he₀inv]
    _ = z m := by
      have he := DFunLike.congr_fun
        (Ideal.Quotient.liftₐ_comp (derivativeBidegreeIdeal a b c) evalz hker')
        (MvPolynomial.X m)
      simpa [qeval, evalz] using he

theorem derivativeBidegreePoint_injective (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Function.Injective (derivativeBidegreePoint (F := F) (E := E) a b c) := by
  intro x y hxy
  funext i
  obtain ⟨P, hP⟩ := derivativeBidegreeMap_surjective (F := F) a b c ha hb hc
    (MvPolynomial.X i : MvPolynomial (Option (Fin 2)) F)
  have he := congrArg (fun z ↦ aeval z P) hxy
  rw [aeval_derivativeBidegreePoint, aeval_derivativeBidegreePoint, hP] at he
  simpa using he

end AffineHilbert
