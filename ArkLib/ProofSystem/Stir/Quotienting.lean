/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.CodingTheory.ListDecodability
public import CompPoly.Data.MvPolynomial.Notation

/-!
# ArkLib.ProofSystem.Stir.Quotienting

Definitions and results for this component of ArkLib.
-/

@[expose] public section

open Polynomial NNReal ReedSolomon Code

namespace Quotienting

variable {F : Type*} [Field F] [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- Let `Ans : S → F`, `ansPoly(Ans, S)` is the unique interpolating polynomial of degree < |S|
    with `AnsPoly(s) = Ans(s)` for each s ∈ S.

    Note: For S=∅ we get Ans'(x) = 0 (the zero polynomial) -/
noncomputable def ansPoly (S : Finset F) (Ans : S → F) : Polynomial F :=
  Lagrange.interpolate S.attach (fun i => (i : F)) Ans

/-- VanishingPoly is the vanishing polynomial on S, i.e. the unique polynomial of degree |S|+1
    that is 0 at each s ∈ S and is not the zero polynomial. That is V(X) = ∏(s ∈ S) (X - s). -/
noncomputable def vanishingPoly (S : Finset F) : Polynomial F :=
  ∏ s ∈ S, (Polynomial.X - Polynomial.C s)

/-- Definition 4.2
  funcQuotient is the quotient function that outputs
  if `domain x ∈ S`,  Fill(domain x).
  else                (f(x) - Ans'(domain x)) / V(domain x).
  Note here that, V(s) = 0 ∀ s ∈ S, otherwise V(s) ≠ 0.

  The evaluation points are the points `domain x` of the code's evaluation domain, as in
  `ReedSolomon.code domain`. -/
noncomputable def funcQuotient (domain : ι ↪ F) (f : ι → F) (S : Finset F) (Ans Fill : S → F) :
    ι → F :=
  fun x =>
    if hx : domain x ∈ S then Fill ⟨domain x, hx⟩ -- if domain x ∈ S,  Fill(domain x).
    else (f x - (ansPoly S Ans).eval (domain x)) / (vanishingPoly S).eval (domain x)

/-- Definition 4.3
  polyQuotient is the polynomial derived from the polynomials fPoly, Ans' and V, where
  Ans' is a polynomial s.t. Ans'(x) = fPoly(x) for x ∈ S, and
  V is the vanishing polynomial on S as before.
  Then, polyQuotient = (fPoly - Ans') / V, where
  polyQuotient.degree < (fPoly.degree - ι.card) -/
noncomputable def polyQuotient (S : Finset F) (fPoly : F[X]) : F[X] :=
    (fPoly - (ansPoly S (fun s => fPoly.eval s))) / (vanishingPoly S)

/-- We define the set disagreementSet(f,ι,S,Ans) as the set of all points `x ∈ ι` whose
evaluation point `domain x` lies in `S` such that the Ans' disagrees with `f`, we have
disagreementSet := { x ∈ ι | domain x ∈ S ∧ Ans'(domain x) ≠ f x }. -/
noncomputable def disagreementSet (domain : ι ↪ F) (f : ι → F) (S : Finset F) (Ans : S → F) :
    Finset ι :=
  Finset.univ.filter fun x => domain x ∈ S ∧ (ansPoly S Ans).eval (domain x) ≠ f x

/-- Quotienting Lemma 4.4
  Let `f : ι → F` be a function, `degree` a degree parameter, `δ ∈ (0,1)` be a distance parameter
  `S` be a set with |S| < degree, `Ans, Fill : S → F`. Suppose for all `u ∈ Λ(code, f, δ)`,
  there exists `x : S`, such that `uPoly(x) ≠ Ans(x)` then
  `δᵣ(funcQuotient(f, S, Ans, Fill), code[ι, F, degree - |S|]) + |T|/|ι| > δ`,
  where T is the disagreementSet as defined above -/
lemma quotienting {degree : ℕ} {domain : ι ↪ F} [Nonempty ι] [DecidableEq ι]
    (S : Finset F) (hS_lt : S.card < degree) (r : F)
  (f : ι → F) (Ans Fill : S → F) (δ : ℝ≥0) (hδPos : δ > 0) (hδLt : δ < 1)
  (h : ∀ u : code domain degree, u.val ∈ closeCodewordsRel ↑(code domain degree) f δ →
    ∃ x : S, ((toPolynomialLT u) : F[X]).eval x.val ≠ Ans x) :
    δᵣ((funcQuotient domain f S Ans Fill), (code domain (degree - S.card))) +
      ((disagreementSet domain f S Ans).card) / (Fintype.card ι) > δ := by
  sorry

end Quotienting
