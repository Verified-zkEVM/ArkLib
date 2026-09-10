/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.DegreeTruncationSemantics
public import CompPoly.Univariate.DivisionCorrectness
public import CompPoly.Univariate.ToPoly.Equiv
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Finite representations of candidate message polynomials

The paper's common recovery lemma starts with a monic squarefree polynomial `h(U)` and a
polynomial `C(X)` over `E[U]/(h)`. This file stores them as executable coefficient data: a
`CPolynomial E` modulus and a descending list of coefficient polynomials in `U`.

A root `θ` of the modulus in an extension field specializes every coefficient and therefore
specifies a message polynomial. Neither the root nor the extension field is part of the runtime
data. Different roots may specify the same message, and constructors may represent extra
messages. Later agreement recovery decides which messages meet the requested threshold.

`specialize` and `WellFormed` describe this interpretation. `residual` computes the agreement
equation modulo the modulus. The theorem `residual_eq_zero_iff` identifies its roots with the
specializations that agree at a received position. This is the equation used by gcd splitting.

The coefficient list has the same descending convention as the decoder's physical output.
Consequently its length bounds the message degree even when leading coefficients vanish.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding

open Polynomial Polynomial.JetHornerMachine CompPoly

/-- Coefficient data for the paper's pair `(h,C)`. The variable of each stored polynomial is
the representation parameter `U`; list order is descending in the message variable `X`. -/
structure FiniteRepresentation (E : Type*) [Field E] [BEq E] [LawfulBEq E] where
  /-- The polynomial whose roots index the represented candidates. -/
  modulus : CPolynomial E
  /-- The coefficients of the message polynomial, in descending order. -/
  coefficients : List (CPolynomial E)

namespace FiniteRepresentation

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Every stored coefficient is the canonical representative of its residue class modulo `h`.
This bounds the amount of coefficient data materialized by a constructor. -/
def Reduced (r : FiniteRepresentation E) : Prop :=
  ∀ c ∈ r.coefficients, c.toPoly.degree < r.modulus.toPoly.degree

/-- A materialized pair with `k` reduced coefficients. An empty root set (`h = 1`) is allowed
and can be discarded by the caller. Recovery keeps this original pair fixed while it splits
its modulus into live divisors, so it need not copy coefficient data at every split. -/
def WellFormed (r : FiniteRepresentation E) (k : ℕ) : Prop :=
  r.modulus.toPoly.Monic ∧ Squarefree r.modulus.toPoly ∧
    r.coefficients.length = k ∧ r.Reduced

/-- Evaluate the coefficient list in the message variable, leaving `U` as a polynomial variable.
The exponent is the number of coefficients still to the right of the current coefficient. -/
def evaluateCoefficients (x : E) : List (CPolynomial E) → CPolynomial E
  | [] => 0
  | c :: cs => c * CPolynomial.C (x ^ cs.length) + evaluateCoefficients x cs

/-- The agreement residual `C(x)-y` in `E[U]/(h)`. Only polynomial arithmetic on stored
coefficients is executed; no root of `h` is chosen. -/
def residual (r : FiniteRepresentation E) (x y : E) : CPolynomial E :=
  (evaluateCoefficients x r.coefficients - CPolynomial.C y).modByMonic r.modulus

noncomputable section

variable {L : Type*} [Field L]

/-- Interpret the stored message at an arbitrary parameter value in an extension field.
For a represented candidate, this value is a root of `modulus`. -/
def specialize (r : FiniteRepresentation E) (ι : E →+* L) (θ : L) : L[X] :=
  coefficientPolynomial (r.coefficients.map fun c => c.toPoly.eval₂ ι θ)

/-- A parameter root represents a given extension-field polynomial. Extra parameter roots and
repeated images are allowed; the representation is a finite cover, not a unique encoding. -/
def Represents (r : FiniteRepresentation E) (ι : E →+* L) (θ : L) (p : L[X]) : Prop :=
  r.modulus.toPoly.eval₂ ι θ = 0 ∧ r.specialize ι θ = p

/-- Constructor-side coverage of a wanted set of base-field messages. The two embeddings
express the tower from the base field through the coefficient field into a field containing
the parameter roots. This predicate is proof-only and is never an executable solver input. -/
def Covers {F : Type*} [Field F] (representations : List (FiniteRepresentation E))
    (base : F →+* E) (ι : E →+* L) (wanted : Set F[X]) : Prop :=
  ∀ p ∈ wanted, ∃ r ∈ representations, ∃ θ : L, r.Represents ι θ (p.map (ι.comp base))

/-- The physical coefficient width bounds every specialization, including the zero polynomial. -/
theorem degree_specialize_lt (r : FiniteRepresentation E) (ι : E →+* L) (θ : L)
    {k : ℕ} (hwidth : r.coefficients.length = k) :
    (r.specialize ι θ).degree < k := by
  simpa only [specialize, List.length_map, hwidth] using
    degree_coefficientPolynomial_lt_length
      (r.coefficients.map fun c => c.toPoly.eval₂ ι θ)

/-- Evaluating first in `X` and then in `U` gives the same value as specializing the message
first. The two variables play different roles, and this identity is their compatibility law. -/
theorem evaluateCoefficients_specialize (cs : List (CPolynomial E))
    (ι : E →+* L) (θ : L) (x : E) :
    (evaluateCoefficients x cs).toPoly.eval₂ ι θ =
      (coefficientPolynomial (cs.map fun c => c.toPoly.eval₂ ι θ)).eval (ι x) := by
  induction cs with
  | nil => simp [evaluateCoefficients, coefficientPolynomial, CPolynomial.toPoly_zero]
  | cons c cs ih =>
      simp [evaluateCoefficients, coefficientPolynomial_cons, CPolynomial.toPoly_add,
        CPolynomial.toPoly_mul, CPolynomial.C_toPoly, Polynomial.eval₂_pow, ih]

/-- Reducing the residual modulo `h` does not change its value at a root of `h`. Thus gcd
splitting by this residual tests precisely agreement at the received pair `(x,y)`. -/
theorem residual_specialize (r : FiniteRepresentation E) (ι : E →+* L) (θ : L)
    (hmonic : r.modulus.toPoly.Monic) (hroot : r.modulus.toPoly.eval₂ ι θ = 0)
    (x y : E) :
    (r.residual x y).toPoly.eval₂ ι θ = (r.specialize ι θ).eval (ι x) - ι y := by
  rw [residual, CPolynomial.modByMonic_toPoly_eq_modByMonic _ _
    ((CPolynomial.monic_toPoly_iff _).mpr hmonic)]
  rw [Polynomial.eval₂_modByMonic_eq_self_of_root hroot]
  simp [specialize, CPolynomial.toPoly_sub, CPolynomial.C_toPoly,
    evaluateCoefficients_specialize]

/-- A represented root lies on the zero branch of an agreement split exactly when its message
agrees with the received value. This equivalence supplies both directions needed for recovery. -/
theorem residual_eq_zero_iff (r : FiniteRepresentation E) (ι : E →+* L) (θ : L)
    (hmonic : r.modulus.toPoly.Monic) (hroot : r.modulus.toPoly.eval₂ ι θ = 0)
    (x y : E) :
    (r.residual x y).toPoly.eval₂ ι θ = 0 ↔ (r.specialize ι θ).eval (ι x) = ι y := by
  rw [residual_specialize r ι θ hmonic hroot, sub_eq_zero]

/-- After `k` shared agreements, every specialization in a live block is the same polynomial.
The block itself need not be linear: uniqueness comes from the message degree bound and the
distinct evaluation points, not from the degree of its parameter polynomial. -/
theorem specialize_eq_of_shared_agreements (r : FiniteRepresentation E)
    (ι : E →+* L) (θ ψ : L) {index : Type*} (positions : Finset index)
    (domain received : index → E) (hdomain : Set.InjOn domain positions)
    (hwidth : r.coefficients.length = positions.card)
    (hθ : ∀ i ∈ positions, (r.specialize ι θ).eval (ι (domain i)) = ι (received i))
    (hψ : ∀ i ∈ positions, (r.specialize ι ψ).eval (ι (domain i)) = ι (received i)) :
    r.specialize ι θ = r.specialize ι ψ := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq positions
    (v := fun i => ι (domain i))
  · intro i hi j hj h
    exact hdomain hi hj (ι.injective h)
  · exact degree_specialize_lt r ι θ hwidth
  · exact degree_specialize_lt r ι ψ hwidth
  · intro i hi
    rw [hθ i hi, hψ i hi]

/-- Interpolation at `k` recorded received pairs recovers a polynomial over the coefficient
field itself. If `p` is that interpolant, every agreeing specialization is its image in the
extension field. No membership test for unknown extension-field coefficients is needed. -/
theorem specialize_eq_map_of_shared_agreements (r : FiniteRepresentation E)
    (ι : E →+* L) (θ : L) {index : Type*} (positions : Finset index)
    (domain received : index → E) (hdomain : Set.InjOn domain positions)
    (hwidth : r.coefficients.length = positions.card)
    (p : E[X]) (hdegree : p.degree < positions.card)
    (hp : ∀ i ∈ positions, p.eval (domain i) = received i)
    (hθ : ∀ i ∈ positions, (r.specialize ι θ).eval (ι (domain i)) = ι (received i)) :
    r.specialize ι θ = p.map ι := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq positions
    (v := fun i => ι (domain i))
  · intro i hi j hj h
    exact hdomain hi hj (ι.injective h)
  · exact degree_specialize_lt r ι θ hwidth
  · exact (Polynomial.degree_map_le).trans_lt hdegree
  · intro i hi
    rw [hθ i hi, Polynomial.eval_map, Polynomial.eval₂_at_apply, hp i hi]

/-- The message recovered from received pairs lies in the original base field `F`, even when
the representation uses an auxiliary field `E`. This is the descent boundary consumed by the
decoder: only `p` is output, while its extension-field image identifies the represented branch. -/
theorem specialize_eq_base_map_of_shared_agreements {F : Type*} [Field F]
    (r : FiniteRepresentation E) (base : F →+* E) (ι : E →+* L) (θ : L)
    {index : Type*} (positions : Finset index) (domain received : index → F)
    (hdomain : Set.InjOn domain positions) (hwidth : r.coefficients.length = positions.card)
    (p : F[X]) (hdegree : p.degree < positions.card)
    (hp : ∀ i ∈ positions, p.eval (domain i) = received i)
    (hθ : ∀ i ∈ positions,
      (r.specialize ι θ).eval (ι (base (domain i))) = ι (base (received i))) :
    r.specialize ι θ = p.map (ι.comp base) := by
  rw [← Polynomial.map_map]
  apply specialize_eq_map_of_shared_agreements r ι θ positions
    (fun i => base (domain i)) (fun i => base (received i))
  · intro i hi j hj h
    exact hdomain hi hj (base.injective h)
  · exact hwidth
  · exact Polynomial.degree_map_le.trans_lt hdegree
  · intro i hi
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hp i hi]
  · exact hθ

end
end FiniteRepresentation
end ReedSolomon.ListDecoding
