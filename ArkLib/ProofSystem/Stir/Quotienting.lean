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
         {ι : Type*}

/-- Let `Ans : S → F`, `ansPoly(Ans, S)` is the unique interpolating polynomial of degree < |S|
    with `AnsPoly(s) = Ans(s)` for each s ∈ S.

    Note: For S=∅ we get Ans'(x) = 0 (the zero polynomial) -/
noncomputable def ansPoly (S : Finset F) (Ans : S → F) : Polynomial F :=
  Lagrange.interpolate S.attach (fun i => (i : F)) Ans

/-- VanishingPoly is the vanishing polynomial on S, i.e. the unique polynomial of degree |S|+1
    that is 0 at each s ∈ S and is not the zero polynomial. That is V(X) = ∏(s ∈ S) (X - s). -/
noncomputable def vanishingPoly (S : Finset F) : Polynomial F :=
  ∏ s ∈ S, (Polynomial.X - Polynomial.C s)

/-- `ansPoly S Ans` interpolates `Ans` on `S`. -/
lemma eval_ansPoly_of_mem (S : Finset F) (Ans : S → F) (s : S) :
    (ansPoly S Ans).eval (s : F) = Ans s := by
  unfold ansPoly
  exact Lagrange.eval_interpolate_at_node Ans Subtype.val_injective.injOn (Finset.mem_attach S s)

/-- The answer polynomial has degree less than `|S|`. -/
lemma degree_ansPoly_lt (S : Finset F) (Ans : S → F) : (ansPoly S Ans).degree < S.card := by
  unfold ansPoly
  simpa using Lagrange.degree_interpolate_lt (s := S.attach) (v := fun i : S => (i : F)) Ans
    Subtype.val_injective.injOn

section VanishingPoly

omit [DecidableEq F]

/-- The vanishing polynomial of `S` vanishes exactly on `S`. -/
lemma eval_vanishingPoly_eq_zero_iff (S : Finset F) (x : F) :
    (vanishingPoly S).eval x = 0 ↔ x ∈ S := by
  simp [vanishingPoly, Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

lemma eval_vanishingPoly_of_mem {S : Finset F} {x : F} (hx : x ∈ S) :
    (vanishingPoly S).eval x = 0 :=
  (eval_vanishingPoly_eq_zero_iff S x).2 hx

lemma eval_vanishingPoly_ne_zero {S : Finset F} {x : F} (hx : x ∉ S) :
    (vanishingPoly S).eval x ≠ 0 :=
  fun h => hx ((eval_vanishingPoly_eq_zero_iff S x).1 h)

lemma monic_vanishingPoly (S : Finset F) : (vanishingPoly S).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun s _ => Polynomial.monic_X_sub_C s

lemma natDegree_vanishingPoly (S : Finset F) : (vanishingPoly S).natDegree = S.card := by
  rw [vanishingPoly, Polynomial.natDegree_prod_of_monic _ _ fun s _ => Polynomial.monic_X_sub_C s]
  simp

end VanishingPoly

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

lemma funcQuotient_of_mem {domain : ι ↪ F} {f : ι → F} {S : Finset F} {Ans Fill : S → F} {x : ι}
    (hx : domain x ∈ S) : funcQuotient domain f S Ans Fill x = Fill ⟨domain x, hx⟩ := by
  simp [funcQuotient, hx]

lemma funcQuotient_of_not_mem {domain : ι ↪ F} {f : ι → F} {S : Finset F} {Ans Fill : S → F}
    {x : ι} (hx : domain x ∉ S) : funcQuotient domain f S Ans Fill x =
      (f x - (ansPoly S Ans).eval (domain x)) / (vanishingPoly S).eval (domain x) := by
  simp [funcQuotient, hx]

/-- Off `S`, multiplying the quotient back by `V_S` and adding `Ans'` recovers `f`. -/
lemma eval_vanishingPoly_mul_funcQuotient_add_ansPoly {domain : ι ↪ F} {f : ι → F}
    {S : Finset F} {Ans Fill : S → F} {x : ι} (hx : domain x ∉ S) :
    (vanishingPoly S).eval (domain x) * funcQuotient domain f S Ans Fill x +
      (ansPoly S Ans).eval (domain x) = f x := by
  rw [funcQuotient_of_not_mem hx]
  field_simp [eval_vanishingPoly_ne_zero hx]
  ring

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
noncomputable def disagreementSet [Fintype ι] (domain : ι ↪ F) (f : ι → F) (S : Finset F)
    (Ans : S → F) : Finset ι :=
  Finset.univ.filter fun x => domain x ∈ S ∧ (ansPoly S Ans).eval (domain x) ≠ f x

/-- The "unquotiented" polynomial `V_S * g + Ans'` of Lemma 4.4. -/
noncomputable def unquotient (S : Finset F) (Ans : S → F) (g : F[X]) : F[X] :=
  vanishingPoly S * g + ansPoly S Ans

/-- On `S` the unquotiented polynomial takes the answer values, whatever `g` is. -/
lemma eval_unquotient_of_mem (S : Finset F) (Ans : S → F) (g : F[X]) (s : S) :
    (unquotient S Ans g).eval (s : F) = Ans s := by
  simp [unquotient, eval_vanishingPoly_of_mem s.2, eval_ansPoly_of_mem]

/-- The unquotiented polynomial of a polynomial of degree less than `d - |S|` has degree less than
`d`. -/
lemma degree_unquotient_lt {S : Finset F} {Ans : S → F} {g : F[X]} {d : ℕ} (hS : S.card < d)
    (hg : g.degree < ((d - S.card : ℕ) : WithBot ℕ)) : (unquotient S Ans g).degree < d := by
  have hmul : (vanishingPoly S * g).degree < d := by
    by_cases hg0 : g = 0
    · simp [hg0]
    · have hVne : vanishingPoly S ≠ 0 := (monic_vanishingPoly S).ne_zero
      have hgnat : g.natDegree < d - S.card := (natDegree_lt_iff_degree_lt hg0).2 hg
      have hne : vanishingPoly S * g ≠ 0 := mul_ne_zero hVne hg0
      rw [← natDegree_lt_iff_degree_lt hne, natDegree_mul hVne hg0, natDegree_vanishingPoly]
      omega
  have hans : (ansPoly S Ans).degree < d :=
    (degree_ansPoly_lt S Ans).trans (by exact_mod_cast hS)
  exact (degree_add_le _ _).trans_lt (max_lt hmul hans)

/-- Away from the disagreement set, the unquotiented polynomial of a polynomial agreeing with the
quotient at `domain x` agrees with `f` at `x`. -/
lemma eval_unquotient_eq_of_not_mem_disagreementSet [Fintype ι] {domain : ι ↪ F} {f : ι → F}
    {S : Finset F} {Ans Fill : S → F} {g : F[X]} {x : ι}
    (hxT : x ∉ disagreementSet domain f S Ans)
    (hg : g.eval (domain x) = funcQuotient domain f S Ans Fill x) :
    (unquotient S Ans g).eval (domain x) = f x := by
  by_cases hx : domain x ∈ S
  · have hT : (ansPoly S Ans).eval (domain x) = f x := by
      by_contra hne
      exact hxT (by simp [disagreementSet, hx, hne])
    simp [unquotient, eval_vanishingPoly_of_mem hx, hT]
  · rw [unquotient, eval_add, eval_mul, hg]
    exact eval_vanishingPoly_mul_funcQuotient_add_ansPoly hx

/-- The unquotiented polynomial of `g` disagrees with `f` only on the disagreement set and on the
points where `g` disagrees with the quotient. -/
lemma hammingDist_le_card_disagreementSet_add [Fintype ι] (domain : ι ↪ F) (f : ι → F)
    (S : Finset F) (Ans Fill : S → F) (g : F[X]) :
    hammingDist f (evalOnPoints domain (unquotient S Ans g)) ≤
      (disagreementSet domain f S Ans).card +
        hammingDist (funcQuotient domain f S Ans Fill) (evalOnPoints domain g) := by
  classical
  unfold hammingDist
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
  by_contra hcon
  push Not at hcon
  exact hx (by
    have := eval_unquotient_eq_of_not_mem_disagreementSet (Fill := Fill) (g := g) hcon.1
      (by simpa [evalOnPoints] using (hcon.2).symm)
    simpa [evalOnPoints] using this.symm)

/-- Some polynomial of degree less than `d` has a codeword at exactly the distance from `u` to the
Reed-Solomon code. -/
lemma exists_polynomial_hammingDist_eq_distFromCode [Fintype ι] (domain : ι ↪ F) (d : ℕ)
    (u : ι → F) :
    ∃ g : F[X], g.degree < d ∧
      (hammingDist u (evalOnPoints domain g) : ℕ∞) =
        Δ₀(u, (code domain d : Set (ι → F))) := by
  have : Nonempty (↑(code domain d : Set (ι → F)) : Set (ι → F)) :=
    ⟨⟨0, Submodule.zero_mem _⟩⟩
  obtain ⟨M, hM, hdist⟩ := exists_closest_codeword_of_Nonempty_Code
    (↑(code domain d) : Set (ι → F)) u
  obtain ⟨g, hg, rfl⟩ := mem_code_iff_exists_polynomial.1 hM
  exact ⟨g, hg, hdist⟩

/-- The codeword of the unquotiented polynomial of a polynomial of degree less than `d - |S|` is a
codeword of `RS[F, ι, d]`. -/
lemma evalOnPoints_unquotient_mem_code (domain : ι ↪ F) {S : Finset F} {Ans : S → F} {g : F[X]}
    {d : ℕ} (hS : S.card < d) (hg : g.degree < ((d - S.card : ℕ) : WithBot ℕ)) :
    evalOnPoints domain (unquotient S Ans g) ∈ code domain d :=
  mem_code_iff_exists_polynomial.2 ⟨_, degree_unquotient_lt hS hg, rfl⟩

omit [DecidableEq F] in
/-- For `d ≤ |ι|`, the interpolant `toPolynomialLT` of the codeword of a polynomial of degree less
than `d` is that polynomial. -/
lemma coe_toPolynomialLT_evalOnPoints [Fintype ι] [DecidableEq ι] {domain : ι ↪ F} {p : F[X]}
    {d : ℕ} (hp : p.degree < d) (hdeg : d ≤ Fintype.card ι)
    (hmem : evalOnPoints domain p ∈ code domain d) :
    ((toPolynomialLT (⟨evalOnPoints domain p, hmem⟩ : code domain d) : degreeLT F d) : F[X]) = p :=
  toPolynomial_evalWord_of_degree_lt hp hdeg

/-- Quotienting Lemma 4.4
  Let `f : ι → F` be a function, `degree` a degree parameter, `δ` a distance parameter
  `S` be a set with |S| < degree, `Ans, Fill : S → F`. Suppose for all `u ∈ Λ(code, f, δ)`,
  there exists `x : S`, such that `uPoly(x) ≠ Ans(x)` then
  `δᵣ(funcQuotient(f, S, Ans, Fill), code[ι, F, degree - |S|]) + |T|/|ι| > δ`,
  where T is the disagreementSet as defined above.

  The paper takes `δ ∈ (0, 1)`; the argument does not use this, so the lemma is stated for every
  `δ`.

  The hypothesis speaks about `toPolynomialLT u`, the interpolant of the codeword `u`. It is the
  degree-`< degree` polynomial evaluating to `u` only when `degree ≤ |ι|`, i.e. for codes of rate at
  most one as in the paper, so this is assumed. -/
lemma quotienting [Fintype ι] {degree : ℕ} {domain : ι ↪ F} [Nonempty ι]
    [DecidableEq ι]
    (S : Finset F) (hS_lt : S.card < degree) (hdeg : degree ≤ Fintype.card ι)
  (f : ι → F) (Ans Fill : S → F) (δ : ℝ≥0)
  (h : ∀ u : code domain degree, u.val ∈ closeCodewordsRel ↑(code domain degree) f δ →
    ∃ x : S, ((toPolynomialLT u) : F[X]).eval x.val ≠ Ans x) :
    δᵣ((funcQuotient domain f S Ans Fill), (code domain (degree - S.card))) +
      ((disagreementSet domain f S Ans).card) / (Fintype.card ι) > δ := by
  sorry

end Quotienting
