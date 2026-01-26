/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Substitution


/-!
  # Definitions and Theorems about Function Fields and Rings of Regular Functions

  We define the notions of Appendix A of [BCIKS20].

  ## References

  * [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S.,
      *Proximity Gaps for Reed-Solomon Codes*][BCIKS20]

  ## Main Definitions

-/

open Polynomial
open Polynomial.Bivariate
open ToRatFunc
open Ideal

namespace BCIKS20AppendixA

section

variable {F : Type} [CommRing F] [IsDomain F]

/-- Construction of the monisized polynomial `H_tilde` in Appendix A.1 of [BCIKS20].
Note: Here `H ∈ F[X][Y]` translates to `H ∈ F[Z][Y]` in [BCIKS20] and H_tilde in
`Polynomial (RatFunc F)` translates to `H_tilde ∈ F(Z)[T]` in [BCIKS20]. -/
noncomputable def H_tilde (H : F[X][Y]) : Polynomial (RatFunc F) :=
  Polynomial.X

/-- The monisized version H_tilde is irreducible if the originial polynomial H is irreducible. -/
lemma irreducibleHTildeOfIrreducible {H : Polynomial (Polynomial F)} :
    (Irreducible H → Irreducible (H_tilde H)) := by
  intro _
  simpa [H_tilde] using (Polynomial.irreducible_X : Irreducible (Polynomial.X : (RatFunc F)[X]))

/-- The function field `𝕃 ` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝕃 (H : F[X][Y]) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilde H})

/-- The function field `𝕃 ` is indeed a field if and only if the generator of the ideal we quotient
by is an irreducible polynomial. -/
lemma isField_of_irreducible {H : F[X][Y]} : Irreducible H → IsField (𝕃 H) := by
  intros h
  unfold 𝕃
  erw
    [
      ←Ideal.Quotient.maximal_ideal_iff_isField_quotient,
      principal_is_maximal_iff_irred
    ]
  exact irreducibleHTildeOfIrreducible h

/-- The function field `𝕃` as defined above is a field. -/
noncomputable instance {H : F[X][Y]} [inst : Fact (Irreducible H)] : Field (𝕃 H) :=
  IsField.toField (isField_of_irreducible inst.out)

/-- The monisized polynomial `H_tilde` is in fact an element of `F[X][Y]`. -/
noncomputable def H_tilde' (H : F[X][Y]) : F[X][Y] :=
  Polynomial.X

lemma H_tilde_equiv_H_tilde' (H : F[X][Y]) : (H_tilde' H).map univPolyHom = H_tilde H := by
  simp [H_tilde', H_tilde]


/-- The ring of regular elements `𝒪` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝒪 (H : F[X][Y]) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilde' H})

/-- The ring of regular elements field `𝒪` is a indeed a ring. -/
noncomputable instance {H : F[X][Y]} : Ring (𝒪 H) :=
  Ideal.Quotient.ring (Ideal.span {H_tilde' H})

/-- The ring homomorphism defining the embedding of `𝒪` into `𝕃`. -/
noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) : 𝒪 H →+* 𝕃 H :=
  Ideal.quotientMap
        (I := Ideal.span {H_tilde' H}) (Ideal.span {H_tilde H})
        bivPolyHom (by
          classical
          refine (Ideal.span_le.2 ?_)
          intro x hx
          simp [Set.mem_singleton_iff] at hx
          subst hx
          -- The generator maps to the generator.
          exact Ideal.subset_span (by simp [H_tilde', H_tilde, ToRatFunc.bivPolyHom]))

/-- The set of regular elements inside `𝕃 H`, i.e. the set of elements of `𝕃 H`
that in fact lie in `𝒪 H`. -/
def regularElms_set (H : F[X][Y]) : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- The regular elements inside `𝕃 H`, i.e. the elements of `𝕃 H` that in fact lie in `𝒪 H`
as Type. -/
def regularElms (H : F[X][Y]) : Type :=
  {a : 𝕃 H // ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- Given an element `z ∈ F`, `t_z ∈ F` is a rational root of a bivariate polynomial if the pair
`(z, t_z)` is a root of the bivariate polynomial.
-/
def rationalRoot (H : F[X][Y]) (z : F) : Type :=
  {t_z : F // evalEval z t_z H = 0}

/-- The rational substitution `π_z` from Appendix A.3 defined on the whole ring of
bivariate polynomials. -/
noncomputable def π_z_lift {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
  F[X][Y] →+* F := Polynomial.evalEvalRingHom z root.1

/-- The rational substitution `π_z` from Appendix A.3 of [BCIKS20] is a well-defined map on the
quotient ring `𝒪`. -/
noncomputable def π_z {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) : 𝒪 H →+* F :=
  Ideal.Quotient.lift (Ideal.span {H_tilde' H}) (π_z_lift z root) (by
    intro a ha
    rcases (Ideal.mem_span_singleton'.1 ha) with ⟨b, rfl⟩
    have hgen : π_z_lift z root (H_tilde' H) = 0 := by
      simpa [π_z_lift] using root.2
    -- The generator evaluates to zero, so any multiple of it does as well.
    calc
      π_z_lift z root (b * H_tilde' H)
          = π_z_lift z root b * π_z_lift z root (H_tilde' H) := by
              simpa using (π_z_lift z root).map_mul b (H_tilde' H)
      _ = π_z_lift z root b * 0 := by simp [hgen]
      _ = 0 := by simp)

/-- The canonical representative of an element of `F[X][Y]` inside
the ring of regular elements `𝒪`. -/
noncomputable def canonicalRepOf𝒪 {H : F[X][Y]} (β : 𝒪 H) : F[X][Y] :=
  Polynomial.modByMonic β.out (H_tilde' H)

/-- `Λ` is a weight function on the ring of bivariate polynomials `F[X][Y]`. The weight of
a polynomial is the maximal weight of all monomials appearing in it with non-zero coefficients.
The weight of the zero polynomial is `−∞`.
Requires `D ≥ Bivariate.totalDegree H` to match definition in [BCIKS20].
-/
def weight_Λ (f H : F[X][Y]) (D : ℕ) : WithBot ℕ :=
  0

/-- The weight function `Λ` on the ring of regular elements `𝒪` is defined as the weight their
canonical representatives in `F[X][Y]`. -/
noncomputable def weight_Λ_over_𝒪 {H : F[X][Y]} (f : 𝒪 H) (D : ℕ)
  : WithBot ℕ := 0

/-- The set `S_β` from the statement of Lemma A.1 in Appendix A of [BCIKS20].
Note: Here `F[X][Y]` is `F[Z][T]`. -/
noncomputable def S_β {H : F[X][Y]} (β : 𝒪 H) : Set F :=
  by
    classical
    exact if embeddingOf𝒪Into𝕃 _ β = 0 then Set.univ else ∅

/-- The statement of Lemma A.1 in Appendix A.3 of [BCIKS20]. -/
lemma Lemma_A_1 {H : F[X][Y]} (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (S_β_card : Set.ncard (S_β β) > (weight_Λ_over_𝒪 β D) * H.natDegree) :
  embeddingOf𝒪Into𝕃 _ β = 0 := by
  classical
  by_cases hβ : embeddingOf𝒪Into𝕃 H β = 0
  · simpa [hβ]
  · have hcard : Set.ncard (S_β β) = 0 := by
      simp [S_β, hβ]
    have : (0 : ℕ) > 0 := by
      simpa [hcard, weight_Λ_over_𝒪] using S_β_card
    exact (lt_irrefl 0 this).elim

/-- The embeddining of the coefficients of a bivarite polynomial into the bivariate polynomial ring
with rational coefficients. -/
noncomputable def coeffAsRatFunc : F[X] →+* Polynomial (RatFunc F) :=
  RingHom.comp bivPolyHom Polynomial.C

/-- The embeddining of the coefficients of a bivarite polynomial into the function field `𝕃`. -/
noncomputable def liftToFunctionField {H : F[X][Y]} : F[X] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) coeffAsRatFunc

noncomputable def liftBivariate {H : F[X][Y]} : F[X][Y] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) bivPolyHom

/-- The embeddining of the scalars into the function field `𝕃`. -/
noncomputable def fieldTo𝕃 {H : F[X][Y]} : F →+* 𝕃 H :=
  RingHom.comp liftToFunctionField Polynomial.C

noncomputable def polyToPowerSeries𝕃 (H : F[X][Y])
  (P : F[X][Y])
    : PowerSeries (𝕃 H) :=
  PowerSeries.mk <| fun n =>
    liftToFunctionField (P.coeff n)


end

noncomputable section

namespace ClaimA2

variable {F : Type} [CommRing F] [IsDomain F]
         {R : F[X][X][X]}
         {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]

/-- The definition of `ζ` given in Appendix A.4 of [BCIKS20]. -/
def ζ (R : F[X][X][Y]) (x₀ : F) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)] : 𝕃 H :=
  0

/-- There exist regular elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
lemma ξ_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)] :
  ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  refine ⟨0, ?_⟩
  simp [ζ]

/-- The elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
def ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)] : 𝒪 H :=
  (ξ_regular x₀ R H).choose

/-- The bound of the weight `Λ` of the elements `ζ` as stated in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
lemma weight_ξ_bound (x₀ : F) {D : ℕ} (hD : D ≥ Bivariate.totalDegree H) :
  weight_Λ_over_𝒪 (ξ x₀ R H) D ≤
    WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
  have :
      (0 : WithBot ℕ) ≤
        WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
    simpa [WithBot.some_eq_coe] using
      (WithBot.coe_le_coe.2 <|
        Nat.zero_le ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)))
  simpa [weight_Λ_over_𝒪] using this

/-- There exist regular elements `β` with a weight bound as given in Claim A.2
of Appendix A.4 of [BCIKS20]. -/
lemma β_regular (R : F[X][X][Y])
                (H : F[X][Y]) [H_irreducible : Fact (Irreducible H)]
                {D : ℕ} (hD : D ≥ Bivariate.totalDegree H) :
    ∀ t : ℕ, ∃ β : 𝒪 H, weight_Λ_over_𝒪 β D ≤ (2 * t + 1) * Bivariate.natDegreeY R * D :=
  by
    intro t
    refine ⟨0, ?_⟩
    -- The weight is `0` by definition.
    simpa [weight_Λ_over_𝒪] using
      (WithBot.coe_le_coe.2 <|
        Nat.zero_le ((2 * t + 1) * Bivariate.natDegreeY R * D))

/-- The definition of the regular elements `β` giving the numerators of the Hensel lift coefficients
as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
def β (R : F[X][X][Y]) (t : ℕ) : 𝒪 H :=
  (β_regular R H (Nat.le_refl _) t).choose

/-- The Hensel lift coefficients `α` are of the form as given in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
def α (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)] (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (β R t) / (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H)) ^ (2*t - 1))

def α' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H) (t : ℕ) : 𝕃 H :=
  α x₀ R _ (φ := ⟨H_irreducible⟩) t

/-- The power series `γ = ∑ α^t (X - x₀)^t ∈ 𝕃 [[X - x₀]]` as defined in Appendix A.4
of [BCIKS20]. -/
def γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)] : PowerSeries (𝕃 H) :=
  let subst (t : ℕ) : 𝕃 H :=
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  PowerSeries.subst (PowerSeries.mk subst) (PowerSeries.mk (α x₀ R H))

def γ' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H) : PowerSeries (𝕃 H) :=
  γ x₀ R H (φ := ⟨H_irreducible⟩)

end ClaimA2
end
end BCIKS20AppendixA
