/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.MvPolynomial.Notation

open Polynomial ReedSolomon ListDecodable

namespace Quotienting

variable {n : ℕ}
         {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Finset F}

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
  if x ∈ S,  Fill(x).
  else       (f(x) - Ans'(x)) / V(x).
  Note here that, V(x) = 0 ∀ x ∈ S, otherwise V(x) ≠ 0. -/
noncomputable def funcQuotient (f : ι → F) (S : Finset F) (Ans Fill : S → F) : ι → F :=
  fun x =>
    if hx : x.val ∈ S then Fill ⟨x.val, hx⟩ -- if x ∈ S,  Fill(x).
    else (f x - (ansPoly S Ans).eval x.val) / (vanishingPoly S).eval x.val

/-- Definition 4.3
  polyQuotient is the polynomial derived from the polynomials fPoly, Ans' and V, where
  Ans' is a polynomial s.t. Ans'(x) = fPoly(x) for x ∈ S, and
  V is the vanishing polynomial on S as before.
  Then, polyQuotient = (fPoly - Ans') / V, where
  polyQuotient.degree < (fPoly.degree - ι.card) -/
noncomputable def polyQuotient (S : Finset F) (fPoly : F[X]) : F[X] :=
    (fPoly - (ansPoly S (fun s => fPoly.eval s))) / (vanishingPoly S)

/-- We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S
such that the Ans' disagrees with f, we have
disagreementSet := { x ∈ ι ∩ S ∧ AnsPoly x ≠ f x }. -/
noncomputable def disagreementSet (f : ι → F) (S : Finset F) (Ans : S → F) : Finset F :=
  Set.toFinset ({x : ι | x.val ∈ S ∧ (ansPoly S Ans).eval x.val ≠ f x}.image Subtype.val)

/-- Quotienting Lemma 4.4
  Let `f : ι → F` be a function, `degree` a degree parameter, `δ ∈ (0,1)` be a distance parameter
  `S` be a set with |S| < degree, `Ans, Fill : S → F`. Suppose for all `u ∈ Λ(code, f, δ)`,
  there exists `x : S`, such that `uPoly(x) ≠ Ans(x)` then
  `δᵣ(funcQuotient(f, S, Ans, Fill), code[ι, F, degree - |S|]) + |T|/|ι| > δ`,
  where T is the disagreementSet as defined above -/
lemma quotienting [DecidableEq F] {degree : ℕ} {domain : ι ↪ F} [Nonempty ι]
  (S : Finset F) (hS_lt : S.card < degree) (r : F)
  (f : ι → F) (Ans Fill : S → F) (δ : ℝ) (hδPos : δ > 0) (hδLt : δ < 1)
  (h : ∀ u : code domain degree, u.val ∈ (relHammingBall ↑(code domain degree) f δ) →
    ∃ (x : S) (hx : x.val ∈ S), ((decodeLT u) : F[X]).eval x.val ≠ Ans ⟨x.val, hx⟩) :
    δᵣ((funcQuotient f S Ans Fill), (code domain (degree - S.card))) +
      ((disagreementSet f S Ans).card : ℝ) / (ι.card : ℝ) > δ := by
  sorry

end Quotienting
