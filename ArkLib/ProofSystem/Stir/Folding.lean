/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Stir.ProximityBound

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.MvPolynomial.Groebner

/-! Section 4.4, [ACFY24stir]

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
* [Sudan, M., *Reed-Solomon codes and polynomial reconstruction*][STIR2005]
* [Ben-Sasson, E. and Sudan, M., *Short PCPs with polylog query complexity*][BSS08]
-/

open Polynomial NNReal ReedSolomon LinearMap Finset ListDecodable STIR

namespace Domain

variable {ι F : Type*} [Field F] [Fintype F] [DecidableEq F] [DecidableEq ι]

/-- The image of a finite set `S` under the map `x ↦ (φ x)ᵏ` -/
def indexPow (S : Finset ι) (φ : ι ↪ F) (k : ℕ) : Finset F :=
  S.image (fun x => (φ x) ^ k)

/-- The k-th power domain `ιᵏ ↪ F` for a given domain `ι ↪ F`. -/
def pow (S : Finset ι) (φ : ι ↪ F) (k : ℕ) : indexPow S φ k ↪ F :=
    Function.Embedding.subtype fun y => y ∈ indexPow S φ k

/-- The fiber over a point `y` under the map `x ↦ (φ x)ᵏ` -/
def powFiber (S : Finset ι) (φ : ι ↪ F) (k : ℕ) (y : indexPow S φ k) : Finset ι :=
  S.filter (fun x => (φ x) ^ k = y)

end Domain

namespace Folding

variable {F : Type*} [Field F] [Fintype F]

/- 𝔽[X,Y] is not an Euclidean Domain, but fixing an order on monomials still allows
   to show existance of bivariate polynomials Q', Q ∈ 𝔽[X,Y] such that
   P = Q' * P' + Q for all P,P' ∈ 𝔽[X,Y] with P' having an invertible leading coefficient
   (which on a field is equivalent to P' not being the zero polynomial).

   This is MonomialOrder.div from Mathlib.RingTheory.MvPolynomial.Groebner

   Using the usual lexicographic order x₀ > x₁ is equal to proposition 6.3 in [BSS08]
   under the substitution z = x₀ and y = x₁, hence the following definition constructs
   Q ∈ 𝔽[Z,Y] with P(z,y) = Q'(z,y) * R(z,y) + Q(z,y)

   Below we present Fact 4.6.1 from STIR -/

/-- Given `P, P' ∈ 𝔽[Z,Y]`, `P' ≠ 0`, computes `Q ∈ 𝔽[Z,Y]`,
with `P(z,y) = Q'(z,y) * P'(z,y) + Q(z,y)` for some `Q' ∈ 𝔽[Z,Y]` -/
noncomputable def modBivar (P P' : MvPolynomial (Fin 2) F)
    (hlg : IsUnit ((MonomialOrder.lex).leadingCoeff P')) : MvPolynomial (Fin 2) F :=
      -- Lexicographic order on `Fin 2`.
      let ord : MonomialOrder (Fin 2) := MonomialOrder.lex
      -- Wrap the single divisor into a family indexed by `Unit`.
      let b : Unit → MvPolynomial (Fin 2) F := fun _ => P'
      -- Unit leading-coeff proof for every index (there is only one).
      have hb : ∀ i : Unit, IsUnit (ord.leadingCoeff (b i)) := by
        intro _; simpa [b, ord] using hlg
      -- Apply Groebner-basis division:
      -- hdiv : ∃ Q', ∃ Q, P =  P' * Q' + Q ∧ (side conditions)
      have hdiv := ord.div (b := b) hb P
      -- Peel off the two nested existentials and return the chosen remainder `r`.
      Classical.choose (Classical.choose_spec hdiv)

/-- maps the univariate polynomial P∈𝔽[Z] to the bivariate polynomial P'∈ 𝔽[Z,Y] with
    P'(z,y) = P(z) -/
noncomputable def uni2bi (p : Polynomial F) : MvPolynomial (Fin 2) F :=
  Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) p

/-- Computes Q(z,y) with P(z) = Q'(z,y) * (y- q(z)) + Q(z,y) as in
    proposition 6.3 from [BSS08] -/
noncomputable def polyQ (P q : Polynomial F) : MvPolynomial (Fin 2) F :=
  -- Pbi(z,y):= P(z)
  let Pbi : MvPolynomial (Fin 2) F := uni2bi P
  -- P'(z,y) := (y - q(z))
  let P' : MvPolynomial (Fin 2) F := (MvPolynomial.X 1) - uni2bi q
  -- proof that leading coefficient f q is not zero
  have h_unit : IsUnit ((MonomialOrder.lex).leadingCoeff P') := sorry
  modBivar Pbi P' h_unit

/-- Helper For Readability: Evaluate a bivariate polynomial Q at (a, b) ∈ F×F -/
def evalBivar
  (Q : MvPolynomial (Fin 2) F) (a b : F) : F := MvPolynomial.eval (Fin.cases a (fun _ ↦ b)) Q

/-- The STIR paper assumes that the polynomials fPoly(.) and Q(qPoly(.),.) are
    fully determined by their evaluations on F. This is not necessarily true
    for arbitrary polynomials of degrees larger than |F|. So we include an
    assumption in what follows that qPoly has degree < |F| from which the
    uniqueness of fPoly and Q can be derived from their evaluation on F.
    Alternatively we could use the identity of polynomials
    fPoly(.) = Q(qPoly(.), .) instead.

    Below we present Fact 4.6.1 from STIR -/
lemma exists_unique_bivariate
  (qPoly : Polynomial F) (hdeg_q_min : qPoly.natDegree > 0)
  (hdeg_q_max : qPoly.natDegree < Fintype.card F) (fPoly : Polynomial F) :
    -- Q ∈ 𝔽[X,Y]
    ∃! Q : MvPolynomial (Fin 2) F,
      -- deg_x(Q) = Floor ( deg(fPoly) / deg(qPoly) )
      -- This is natural number division towards zero, which is floor
      (MvPolynomial.degreeOf 0 Q = (Polynomial.natDegree fPoly) / (Polynomial.natDegree qPoly)) ∧
      -- deg_y(Q) < deg (q)
      (MvPolynomial.degreeOf 1 Q < Polynomial.natDegree qPoly) ∧
      -- point‑wise equality on F: f(z) = Q(q(z), z)
      (∀ z : F, Polynomial.eval z fPoly = evalBivar Q (Polynomial.eval z qPoly) z) ∧
      (∀ t : ℕ, fPoly.natDegree < t * qPoly.natDegree → MvPolynomial.degreeOf 0 Q < t) :=
  /- The proof can follow `def polyQ` using the properties guranteed
  from MonomialOrder.div from Mathlib.RingTheory.MvPolynomial.Groebner -/
  by sorry

/-- Fact 4.6.2 in STIR -/
lemma degree_bound_bivariate
  (qPoly : Polynomial F)
  (hdeg_q_min : qPoly.natDegree > 0)
  (hdeg_q_max : qPoly.natDegree < Fintype.card F)
  {t : ℕ} (Q : MvPolynomial (Fin 2) F)
  (hdegX : MvPolynomial.degreeOf 0 Q < t)
  (hdegY : MvPolynomial.degreeOf 1 Q < qPoly.natDegree) :
  (MvPolynomial.eval₂Hom (Polynomial.C : F →+* Polynomial F)
      (fun i : Fin 2 => if i = 0 then qPoly else Polynomial.X) Q).natDegree < t * qPoly.natDegree :=
    by sorry

/-- Definition 4.7
  `polyFold(f, k, r)` "folds" the polynomial `f`
  producing a new polynomial of deree  `< degree(f)/k`. -/
noncomputable def polyFold
  [DecidableEq F] (fPoly : Polynomial F)
  (k : ℕ) (hk0 : 0 < k) (hkfin : k < Fintype.card F)
  (r : F) : Polynomial F :=
    let qPoly : Polynomial F := Polynomial.X ^ k
    let hdeg_q_min : qPoly.natDegree > 0 := sorry
    let hdeg_q_max : qPoly.natDegree < Fintype.card F := sorry
  -- choose the unique bivariate lift Q
    let Q : MvPolynomial (Fin 2) F := polyQ fPoly qPoly
    MvPolynomial.eval₂Hom
      (Polynomial.C : F →+* Polynomial F)
      (fun i : Fin 2 => if i = 0 then Polynomial.X else Polynomial.C r) Q

open Domain

variable {ι F : Type*} [Field F] [Fintype F] [DecidableEq F] [DecidableEq ι]

/-- Definition 4.8
  For x ∈ ιᵏ, p_x ∈ 𝔽[X] is the degree < k polynomial
  where p_x(y) = f(y) for every y ∈ ι such that yᵏ = x. -/
noncomputable def xPoly
  {S : Finset ι} (f : ι → F) (φ : ι ↪ F) (k : ℕ) (x : indexPow S φ k) : Polynomial F :=
  let dom := powFiber S φ k x
  let emb : { y // y ∈ dom } → F := φ ∘ Subtype.val
  let g : { y // y ∈ dom } → F := f ∘ Subtype.val
  Lagrange.interpolate univ emb g

/-- Definition 4.8
  Fold(f,k,α) : ιᵏ → 𝔽 such that  Fold(f, k, α)(x) := p_x(α) -/
noncomputable def fold
  {S : Finset ι} (φ : ι ↪ F) (f : ι → F) (k : ℕ) (α : F) : indexPow S φ k → F :=
    fun x => (xPoly f φ k x).eval α

/-- min{δᵣ(f, RSC[F, ι, degree]), 1 − B^⋆(ρ)} -/
noncomputable def foldingDistRange
   (degree : ℕ) [Fintype ι] [Nonempty ι] (φ : ι ↪ F) (f : ι → F) : ℝ≥0 :=
    let C : Set (ι → F) := code φ degree
    letI : Nonempty C := by exact Zero.instNonempty
    letI : Fintype C := by exact Fintype.ofFinite ↑C
    min δᵣ'(f, C) (1 - Bstar (LinearCode.rate (code φ degree)))

open ProbabilityTheory

variable {ι F : Type} [Field F] [Fintype F] [DecidableEq F] [DecidableEq ι]

/-- Lemma 4.9
  For every function `f : ι → F`, `degree`, folding parameter `k`, and
  `δ ∈ (0, foldingDistRange)`
  `Pr_{r ← F} [ δᵣ(fold(f, k, α), RS[F, ιᵏ, degree/k)] < δ] ≤ err'(degree/k, ρ, δ, k)` -/
lemma folding
  [Nonempty ι] {S : Finset ι} [Fintype ι]
  (φ : ι ↪ F) (f : ι → F) (k : ℕ)
  [Nonempty (indexPow S φ k)]
  {degree : ℕ} (δ : ℝ≥0) (hδPos : δ > 0)
  (hδLt : δ < foldingDistRange degree φ f) :
  let C : Set ((indexPow S φ k) → F) := code (pow S φ k) (degree / k)
  Pr_{ let r ← $ᵖ F }[ δᵣ((fold φ f k r), C) ≤ δ]
    ≤ proximityError F (degree / k) (LinearCode.rate (code φ degree)) δ k :=
by sorry

end Folding
