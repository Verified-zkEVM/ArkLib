/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.JetPrefix
public import ArkLib.ToMathlib.MvPolynomial.UnivariateSpecialization

/-!
# Counting regular jets

Let `Q(X, Y₀, ..., Y_d)` be a differential polynomial over a domain `F` and fix a jet variable
`Y_s`. A regular jet at a point `a` is a scalar jet on `Q = 0` at which the separant `∂Q/∂Y_s`
does not vanish (`IsRegularJet`). Fixing `a` and the jet coordinates other than `Y_s` leaves a
nonzero univariate polynomial in `Y_s` of degree at most `jetDegree Q s`, so:

* for a finite set `B ⊆ F`, at most `jetDegree Q s * #B ^ d` jets with all coordinates in `B` are
  regular at `a`;
* for finite sets `A, B ⊆ F`, at most `jetDegree Q s * (#A * #B ^ d)` pairs of a point in `A` and a
  jet with coordinates in `B` are regular.

Over a finite field, taking `A = B = F` bounds `Nat.card` of the regular jets at a point by
`jetDegree Q s * q ^ d` and of all regular point-jet pairs by `q * jetDegree Q s * q ^ d`, where
`q = Nat.card F`. No characteristic hypothesis is needed. The domain hypothesis is needed for the
root count: over `ZMod 4` with `d = 0`, the equation `2 Y₀ = 0` has the two regular jets `0` and `2`
at every point, while `jetDegree = 1`.

## Main statements

* `jetAssignment` and `jetEvaluation_eq_eval`: a point and a jet as one assignment of the
  variables `X, Y₀, ..., Y_d`.
* `card_filter_isRegularJet_le`: regular jets at one point with coordinates in `B`.
* `card_filter_isRegularJet_product_le`: regular point-jet pairs in `A ×ˢ Bᵈ⁺¹`.
* `natCard_regularJetAt_le` and `natCard_regularJet_le`: the finite-field counts.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Finset

variable {F : Type*} {d : ℕ}

/-! ### Points and jets as assignments -/

/-- The assignment of `a` to `X` and of `jet j` to `Y_j`. -/
def jetAssignment (a : F) (jet : Fin (d + 1) → F) : JetVariable d → F
  | none => a
  | some j => jet j

/-- `jetAssignment a jet` assigns `a` to `X`. -/
@[simp]
theorem jetAssignment_none (a : F) (jet : Fin (d + 1) → F) : jetAssignment a jet none = a :=
  rfl

/-- `jetAssignment a jet` assigns `jet j` to `Y_j`. -/
@[simp]
theorem jetAssignment_some (a : F) (jet : Fin (d + 1) → F) (j : Fin (d + 1)) :
    jetAssignment a jet (some j) = jet j :=
  rfl

/-- A jet is determined by its assignment at a fixed point. -/
theorem jetAssignment_injective (a : F) : Function.Injective (jetAssignment (d := d) a) :=
  fun _ _ h ↦ funext fun j ↦ congrFun h (some j)

/-- Jet evaluation is multivariate evaluation at `jetAssignment a jet`. -/
theorem jetEvaluation_eq_eval [CommSemiring F] (Q : DifferentialPolynomial F d) (a : F)
    (jet : Fin (d + 1) → F) :
    jetEvaluation Q a jet = MvPolynomial.eval (jetAssignment a jet) Q :=
  rfl

/-- Regularity of a jet is decidable when equality in `F` is. -/
instance decidableIsRegularJet [CommSemiring F] [DecidableEq F] (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (a : F) (jet : Fin (d + 1) → F) : Decidable (IsRegularJet Q s a jet) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The product of the box sizes other than `Y_s`, when `X` ranges over one point and each jet
coordinate over `B`, is `#B ^ d`. -/
private theorem prod_card_erase_some (a : F) (B : Finset F) (s : Fin (d + 1)) :
    ∏ v ∈ (univ : Finset (JetVariable d)).erase (some s),
        (Option.elim v {a} fun _ ↦ B : Finset F).card = B.card ^ d := by
  classical
  have hset : (univ : Finset (JetVariable d)).erase (some s) =
      insert none ((univ.erase s).map Function.Embedding.some) := by
    ext v
    cases v <;> simp
  rw [hset, prod_insert (by simp), prod_map]
  simp [card_erase_of_mem]

/-! ### Regular jets with coordinates in finite sets -/

/-- **Regular jets at a point.** Over a domain, at most `jetDegree Q s * #B ^ d` jets with every
coordinate in the finite set `B` are regular for `Q` in `Y_s` at the point `a`.

Once the coordinates other than `Y_s` are fixed, the separant condition makes the specialization
of `Q` in `Y_s` a nonzero polynomial of degree at most `jetDegree Q s`, whose roots are the
possible values of `Y_s`. The domain hypothesis bounds the number of roots by the degree. At
`d = 0` the bound is `jetDegree Q s`. -/
theorem card_filter_isRegularJet_le [CommRing F] [IsDomain F] [DecidableEq F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (a : F) (B : Finset F) :
    #{jet ∈ Fintype.piFinset (fun _ : Fin (d + 1) ↦ B) | IsRegularJet Q s a jet} ≤
      jetDegree Q s * B.card ^ d := by
  set T := {jet ∈ Fintype.piFinset (fun _ : Fin (d + 1) ↦ B) | IsRegularJet Q s a jet}
  rw [← card_image_of_injective T (jetAssignment_injective a), ← prod_card_erase_some a B s]
  refine MvPolynomial.card_le_degreeOf_mul_prod_of_eval_pderiv_ne_zero _ (some s) Q _
    fun x hx ↦ ?_
  obtain ⟨jet, hjet, rfl⟩ := mem_image.mp hx
  obtain ⟨hbox, hzero, hsep⟩ := mem_filter.mp hjet
  refine ⟨Fintype.mem_piFinset.mpr fun v ↦ ?_, ?_, ?_⟩
  · cases v with
    | none => simp
    | some j => simpa using Fintype.mem_piFinset.mp hbox j
  · rwa [← jetEvaluation_eq_eval]
  · rwa [← jetEvaluation_eq_eval]

/-- **Regular point-jet pairs.** Over a domain, at most `jetDegree Q s * (#A * #B ^ d)` pairs of
a point in `A` and a jet with every coordinate in `B` are regular for `Q` in `Y_s`.

This sums `card_filter_isRegularJet_le` over the points of `A`. -/
theorem card_filter_isRegularJet_product_le [CommRing F] [IsDomain F] [DecidableEq F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (A B : Finset F) :
    #{z ∈ A ×ˢ Fintype.piFinset (fun _ : Fin (d + 1) ↦ B) | IsRegularJet Q s z.1 z.2} ≤
      jetDegree Q s * (A.card * B.card ^ d) := by
  rw [mul_left_comm, mul_comm A.card]
  refine card_le_mul_card_image_of_maps_to (f := Prod.fst) (fun z hz ↦ ?_) _ fun a _ ↦ ?_
  · exact (mem_product.mp (mem_filter.mp hz).1).1
  refine le_trans ?_ (card_filter_isRegularJet_le Q s a B)
  refine card_le_card_of_injOn Prod.snd (fun z hz ↦ ?_) fun z hz z' hz' h ↦ ?_
  · have hfibre := mem_filter.mp hz
    obtain ⟨hbox, hreg⟩ := mem_filter.mp hfibre.1
    rw [← hfibre.2]
    exact mem_filter.mpr ⟨(mem_product.mp hbox).2, hreg⟩
  · have ha := (mem_filter.mp hz).2
    have ha' := (mem_filter.mp hz').2
    exact Prod.ext (ha.trans ha'.symm) h

/-! ### Finite coefficient domains -/

/-- **Regular jets at a point over a finite domain.** At most `jetDegree Q s * q ^ d` jets are
regular for `Q` in `Y_s` at the point `a`, where `q = Nat.card F`. -/
theorem natCard_regularJetAt_le [CommRing F] [IsDomain F] [Finite F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (a : F) :
    Nat.card {jet : Fin (d + 1) → F // IsRegularJet Q s a jet} ≤
      jetDegree Q s * Nat.card F ^ d := by
  classical
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Fintype.piFinset_univ,
    Nat.card_eq_fintype_card, ← card_univ]
  exact card_filter_isRegularJet_le Q s a univ

/-- **Regular point-jet pairs over a finite domain.** At most `q * jetDegree Q s * q ^ d` pairs of
a point and a jet are regular for `Q` in `Y_s`, where `q = Nat.card F`. -/
theorem natCard_regularJet_le [CommRing F] [IsDomain F] [Finite F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    Nat.card (RegularJet Q s) ≤ Nat.card F * jetDegree Q s * Nat.card F ^ d := by
  classical
  have := Fintype.ofFinite F
  unfold RegularJet
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← univ_product_univ,
    ← Fintype.piFinset_univ, Nat.card_eq_fintype_card, ← card_univ, mul_comm (#univ),
    mul_assoc]
  exact card_filter_isRegularJet_product_le Q s univ univ

end

end PolynomialDifferential
