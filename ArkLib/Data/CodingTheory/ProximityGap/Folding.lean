/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.FoldingPolynomial
import ArkLib.Data.Polynomial.SplitFold
import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ProximityGap.Folding.FoldingContext
import ArkLib.Data.Finset.PickSubset
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.Domain.CosetFftDomain.Block
import ArkLib.Data.Domain.CosetFftDomain.Subdomain
import ArkLib.Data.Domain.CosetFftDomain.Log
import ArkLib.Data.Domain.CosetFftDomain.Pullback
import ArkLib.Data.Polynomial.Indicator
import ArkLib.ToMathlib.Polynomial.EvalExt
import ArkLib.ToMathlib.Polynomial.NatDegreeOfSum

/-! This file contains all the definition needed to state
  and prove the lemma 4.9 from [ACFY24] as well as the proof of it.

## Main definitions

* `foldWord` : the folding function that is to be used by the verifier to fold
    purported codeword using a random challenge.
* `folding_preserves_distance` : lemma 4.9 from [ACFY24]. "Soundness" of the folding operation.
    If a purported codeword `f`
    has distance `δ` to a given RS-code then,
    with high probability over the choice of folding randomness,
    its folding also has distance `δ` to the "k-wise folded" RS-code.
* `foldWord_codeword` : a bonus theorem not present in [ACFY24]. "Completeness" of the folding
    operation.
    folding a codeword is the same RS-encoding folding polynomial applied to
    the message.

## References

* [Arnon, G., Chiesa, A., Fenzi, G., Yogev, E.,
  *STIR: Reed–Solomon Proximity Testing with Fewer Queries*][ACFY24]
-/

namespace ProximityGap

open NNReal Finset Function
open scoped ProbabilityTheory
open scoped BigOperators LinearCode
open Code Affine ReedSolomon
open Polynomial Domain
open CosetFftDomain CosetFftDomainClass

variable {F : Type} [Field F] [DecidableEq F]
variable {n : ℕ}

/-- Given a word `f`, `foldWordAux` is a polynomial `pₓ`
  of degree < '2 ^ k' such that `pₓ(domain i) = f i` for each `i`
  such that `domain i ^ 2 ^ k = x`. -/
noncomputable def foldWordAux (domain : SmoothCosetFftDomain n F)
  (f : Word F (Fin (2 ^ n))) (k : ℕ) (x : F) : Polynomial F :=
  Lagrange.interpolate (blockIdx domain k x) domain f

section

variable {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))}
variable {k : ℕ} {x : F}

omit [DecidableEq F] in
private lemma even_add_odd_eq_of_2_ne_0
  (x y z : F) (hz : z ≠ 0) (hchar : (2 : F) ≠ 0) :
  x = (x + y) / 2 + (x - y) / (2 * z) * z := by grind

/-- An explicit formula to compute `foldWordAux` when `k = 2`
  not involving Lagrange interpolation. -/
lemma foldWordAux_of_k_2 [NeZero n] {i : Fin (2 ^ (n - 1))} :
    foldWordAux domain f 1 (domain.subdomain 1 i) =
    let x : domain := CosetFftDomain.twoNthRoot (i := 1)
      ⟨domain.subdomain 1 i, by simp⟩
    let i := domain.log x
    let i' := domain.log ⟨-x.1, by obtain ⟨x, hx⟩ := x; simpa using hx⟩
    C ((f i + f i') / 2) + Polynomial.X * C ((f i - f i') / (2 * x)) := by
  unfold foldWordAux
  have hn : n ≠ 0 := NeZero.ne _
  extract_lets y j j'
  have h :
    ({i_1 | domain i_1 ^ 2 ^ 1 = (CosetFftDomain.subdomain domain 1) i} : Finset _) =
    {j, j'} := by
    have h := square_roots_explicit
      (ω := domain) (i := 0) (by omega) (y := y)
      (x := (CosetFftDomain.subdomain domain 1) i)
      (by simp) (by simp [y])
    have hpre : Finset.preimage {y.1, -y.1} domain (by simp) = {j, j'} := by
      aesop (add unsafe (by apply CosetFftDomain.injective (ω := domain)))
    ext u
    simp only [mem_filter, mem_univ, true_and, ←hpre, ←h, Nat.sub_zero, mem_preimage]
    aesop
  rw [blockIdx, h]
  have hcard : Finset.card {j, j'} = 2 := by
    rw [←h]
    conv_rhs =>
      rw [←pow_one 2,
          ←card_block_of_mem_subdomain (ω := domain) (i := 0)
              (x := (CosetFftDomain.subdomain domain 1) i)
              (by omega) (by simp)]
    exact Finset.card_bij
      (fun a _ ↦ domain a)
      (fun a ha ↦ by
        simp only [Nat.sub_zero, mem_block, pow_one]
        simpa using ha)
      (fun _ _ _ _ h ↦ CosetFftDomain.injective h)
      (fun b hb ↦ by
        obtain ⟨⟨j, hb⟩, hb'⟩ :
          b ∈ domain ∧ b ^ 2 = (CosetFftDomain.subdomain domain 1) i := by
          aesop
        exact ⟨j, by simp [hb, hb'], by simp [hb]⟩)
  apply Polynomial.eq_of_eval_eq_degree (n := 2) (s := {y.1, -y.1})
  · exact lt_of_lt_of_le
      (Lagrange.degree_interpolate_lt _ CosetFftDomain.injOn)
      (by simp [hcard])
  · exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) <| by
      simp only [X_mul_C, degree_mul, degree_X, WithBot.coe_ofNat, sup_lt_iff]
      constructor
      · exact lt_trans Polynomial.degree_C_lt (by simp)
      · exact lt_of_lt_of_le
          (WithBot.add_lt_add_right (by simp) Polynomial.degree_C_lt) (by rfl)
  · conv_rhs =>
      rw [←hcard]
    exact Finset.card_le_card_of_injOn (f := domain)
      (fun x hx ↦ by aesop) CosetFftDomain.injOn
  · intro x hx
    have hx : (x = domain j ∧ y.1 = domain j) ∨
              (x = domain j' ∧ y.1 = -domain j') := by aesop
    have hj := even_add_odd_eq_of_2_ne_0 (f j) (f j') (domain j) (by simp)
      (CosetFftDomainClass.domain_implies_2_ne_0 domain)
    have hj' := even_add_odd_eq_of_2_ne_0 (f j') (f j) (domain j') (by simp)
      (CosetFftDomainClass.domain_implies_2_ne_0 domain)
    rcases hx with ⟨rfl, hy⟩ | ⟨rfl, hy⟩
    · rw [Lagrange.eval_interpolate_at_node _ CosetFftDomain.injOn (by simp),
          hy]
      conv_lhs => rw [hj]
      simp
    · rw [Lagrange.eval_interpolate_at_node _ CosetFftDomain.injOn (by simp), hy]
      conv_lhs => rw [hj']
      simp?
      grind

/-- The degree of the auxiliary polynomial `foldWordAux`
  is less than 2^k. -/
@[simp]
lemma foldWordAux_degree {k : ℕ} {x : F} :
    (foldWordAux domain f k x).degree < 2 ^ k :=
  lt_of_lt_of_le
    (Lagrange.degree_interpolate_lt _ (by simp))
    (by norm_cast; simp)

/-- The natDegree of the auxiliary polynomial `foldWordAux`
  is less than 2^k. -/
@[simp]
lemma foldWordAux_natDegree {k : ℕ} {x : F} :
    (foldWordAux domain f k x).natDegree < 2 ^ k := by
  by_cases foldWordAux domain f k x = 0 <;>
    aesop (add simp Polynomial.natDegree_lt_iff_degree_lt)

/-- Compute value of the folded word.
  Takes the auxiliary polynomial `foldWordAux` and evaluates it on `a`,
  the folding randomness. -/
noncomputable def foldValue (domain : SmoothCosetFftDomain n F)
  (f : Word F (Fin (2 ^ n)))
  (k : ℕ) (α : F) (x : F) : F :=
  (foldWordAux domain f k x).eval α

lemma foldValue_def {α : F} {x : F} :
    foldValue domain f k α x = (foldWordAux domain f k x).eval α := rfl

lemma foldValue_def' {α : F} {x : F} :
    foldValue domain f k α x = (Lagrange.interpolate (blockIdx domain k x) domain f).eval α := rfl

@[simp]
lemma foldValue_pow_x_k {i : Fin (2 ^ n)} :
    foldValue domain f k (domain i) (domain i ^ 2 ^ k) = f i :=
  Lagrange.eval_interpolate_at_node _ (by simp) (by simp)

@[simp]
lemma foldValue_zero {k : ℕ} :
    foldValue domain 0 k = 0 := by aesop (add simp [foldValue, foldWordAux])

/-- An explicit formula for `foldValue` when `k = 1`. -/
lemma foldValue_k_1 [NeZero n] {i : Fin (2 ^ (n - 1))} {α : F} :
    foldValue domain f 1 α (domain.subdomain 1 i) =
    let x : domain := CosetFftDomain.twoNthRoot (i := 1)
        ⟨domain.subdomain 1 i, by simp⟩
    let i := domain.log x
    let i' := domain.log ⟨-x.1, by obtain ⟨x, hx⟩ := x; simpa using hx⟩
    ((f i + f i') / 2) + α * ((f i - f i') / (2 * x)) := by
  simp [foldValue, foldWordAux_of_k_2]
  ring

/-- Fold a word. Takes a word `f` over `Fin (2 ^ n)` and randomness
  `a`, and returns a word over `Fin (2 ^ (n - k))`. -/
noncomputable def foldWord (domain : SmoothCosetFftDomain n F)
  (f : Word F (Fin (2 ^ n))) (k : ℕ) (α : F) :
  Word F (Fin (2 ^ (n - k))) := fun x ↦
  foldValue domain f k α (domain.subdomain k x)

@[simp]
lemma foldWord_zero {k : ℕ} :
    foldWord domain 0 k = 0 := by aesop (add simp [foldWord])

/-- An explicit formula for `foldWord` when `k = 1` that
  does not use Lagrange interpolation. -/
theorem foldWord_k_1 [NeZero n] {i : Fin (2 ^ (n - 1))} {α : F} :
    foldWord domain f 1 α i =
    let x : domain := CosetFftDomain.twoNthRoot (i := 1)
        ⟨domain.subdomain 1 i, by simp⟩
    let i := domain.log x
    let i' := domain.log ⟨-x.1, by obtain ⟨x, hx⟩ := x; simpa using hx⟩
    ((f i + f i') / 2) + α * ((f i - f i') / (2 * x)) := by
  simp [foldWord, foldValue_k_1]

/-- An explicit formula for `foldWord` when `k = 1` that
  does not use Lagrange interpolation. Functional version. -/
theorem foldWord_k_1' [NeZero n] {α : F} :
    foldWord domain f 1 α = fun i ↦
    let x : domain := CosetFftDomain.twoNthRoot (i := 1)
        ⟨domain.subdomain 1 i, by simp⟩
    let i := domain.log x
    let i' := domain.log ⟨-x.1, by obtain ⟨x, hx⟩ := x; simpa using hx⟩
    ((f i + f i') / 2) + α * ((f i - f i') / (2 * x)) := by aesop (add simp foldWord_k_1)

/-- An explicit formula for `foldWord` when `k = 1` that
  does not use Lagrange interpolation and avoids using `log`. -/
theorem foldWord_k_1_of_sq_roots {i : Fin (2 ^ (n - 1))} {α : F}
    {j j' : Fin (2 ^ n)} (hjj' : j ≠ j')
  (hj : domain j ^ 2 = domain.subdomain 1 i) (hj' : domain j' ^ 2 = domain.subdomain 1 i) :
  foldWord domain f 1 α i =
    ((f j + f j') / 2) + α * ((f j - f j') / (2 * domain j)) := by
  have hn : n ≠ 0 := by aesop (add safe [cases Fin, (by omega)])
  let : NeZero n := ⟨hn⟩
  rw [foldWord_k_1]
  extract_lets x a b
  have ha : domain a = x := by simp [a]
  have hb : domain b = -x := by simp [b]
  have hx : x ^ 2 = domain.subdomain 1 i := by simp [x]
  have hj_cases : domain j = x ∨ domain j = -x := by aesop (add safe eq_or_eq_neg_of_sq_eq_sq)
  have hj'_cases : domain j' = x ∨ domain j' = -x := by aesop (add safe eq_or_eq_neg_of_sq_eq_sq)
  rcases hj_cases with hjx | hjx <;> rcases hj'_cases with hj'x | hj'x <;>
    try
      exfalso
      exact hjj' (CosetFftDomain.injective (hjx.trans hj'x.symm))
  · obtain rfl : j = a := CosetFftDomain.injective (hjx.trans ha.symm)
    obtain rfl : j' = b := CosetFftDomain.injective (hj'x.trans hb.symm)
    rw [ha]
  · obtain rfl : j = b := CosetFftDomain.injective (hjx.trans hb.symm)
    obtain rfl : j' = a := CosetFftDomain.injective (hj'x.trans ha.symm)
    rw [hb]
    field_simp
    ring

lemma foldWord_k_1_eval_domain [NeZero n] {i : Fin (2 ^ (n - 1))}
    {j : Fin (2 ^ n)} (hj : domain j ^ 2 = domain.subdomain 1 i) :
  foldWord domain f 1 (domain j) i = f j := by
  let j' := domain.log ⟨-domain j, by simp⟩
  have hjj' : j ≠ j' := fun contra ↦ by
    have := domain_implies_x_ne_neg_x (ω := domain) (x := domain j)
    have := congrArg (f := domain) contra
    simp only [log_right_inverse', j'] at this
    exact domain_implies_x_ne_neg_x (ω := domain) (by simp) this
  have := CosetFftDomainClass.domain_implies_2_ne_0 domain
  rw [foldWord_k_1_of_sq_roots hjj'] <;>
    aesop (add safe [(by grind), (by field_simp)])

/-- The "even" part of the folding function. -/
def foldWordEven [NeZero n] (domain : SmoothCosetFftDomain n F)
    (f : Word F (Fin (2 ^ n))) (i : Fin (2 ^ (n - 1))) : F :=
  let x : domain := CosetFftDomain.twoNthRoot (i := 1)
        ⟨domain.subdomain 1 i, by simp⟩
  let i := domain.log x
  let i' := domain.log ⟨-x.1, by obtain ⟨x, hx⟩ := x; simpa using hx⟩
  (f i + f i') / 2

/-- The "odd" part of the folding function. -/
def foldWordOdd [NeZero n] (domain : SmoothCosetFftDomain n F)
    (f : Word F (Fin (2 ^ n))) (i : Fin (2 ^ (n - 1))) : F :=
  let x : domain := CosetFftDomain.twoNthRoot (i := 1)
        ⟨domain.subdomain 1 i, by simp⟩
  let i := domain.log x
  let i' := domain.log ⟨-x.1, by obtain ⟨x, hx⟩ := x; simpa using hx⟩
  (f i - f i') / (2 * x)

/-- `foldWord` equals the natural linear combination
  of its even and odd parts. -/
lemma foldWord_k_1_eq_foldWordEven_add_foldWordOdd [NeZero n] {α : F} :
    foldWord domain f 1 α =
    foldWordEven domain f + α • foldWordOdd domain f := by
  aesop (add simp [foldWord_k_1, foldWordEven, foldWordOdd])

/-- Folding the evaluation of `p₀(X²) + X * p₁(X²)` with randomness `α` gives the evaluation
  of `p₀ + α * p₁` on the halved domain. -/
@[simp]
lemma foldWord_evalOnPoints_split [NeZero n] {p₀ p₁ : Polynomial F} {α : F}
    {i : Fin (2 ^ (n - 1))} :
  foldWord domain (evalOnPoints (domain : Fin (2 ^ n) ↪ F)
      (p₀.comp (Polynomial.X ^ 2) + Polynomial.X * p₁.comp (Polynomial.X ^ 2))) 1 α i =
    p₀.eval (domain.subdomain 1 i) + α * p₁.eval (domain.subdomain 1 i) := by
  rw [foldWord_k_1]
  extract_lets x a b
  have hva : evalOnPoints (domain : Fin (2 ^ n) ↪ F)
      (p₀.comp (Polynomial.X ^ 2) + Polynomial.X * p₁.comp (Polynomial.X ^ 2)) a =
      p₀.eval ((x : F) ^ 2) + (x : F) * p₁.eval ((x : F) ^ 2) := by
    aesop (add simp evalOnPoints)
  have hvb : evalOnPoints (domain : Fin (2 ^ n) ↪ F)
      (p₀.comp (Polynomial.X ^ 2) + Polynomial.X * p₁.comp (Polynomial.X ^ 2)) b =
      p₀.eval ((x : F) ^ 2) - (x : F) * p₁.eval ((x : F) ^ 2) := by
    aesop (add simp evalOnPoints) (add safe (by grind))
  have : (2 : F) ≠ 0 := CosetFftDomainClass.domain_implies_2_ne_0 domain
  aesop (add safe [(by field_simp), (by grind)])

/-- The version of a folding where
  k steps are achieved via iterated application
  of k=1 folding. -/
noncomputable def iteratedFoldWord (domain : SmoothCosetFftDomain n F)
  (f : Word F (Fin (2 ^ n))) (k : ℕ) (α : Fin k → F) :
  Word F (Fin (2 ^ (n - k))) :=
  match k with
  | 0 => f
  | Nat.succ k =>
    let prev := iteratedFoldWord domain f k (fun i ↦ α ⟨i.val, by omega⟩)
    let foldedPrev :=
      foldWord (domain.subdomain k) prev 1 (α ⟨k, by omega⟩)
    fun i ↦ foldedPrev ⟨i.val, by aesop (add safe cases Fin)⟩

@[simp]
lemma iteratedFoldWord_zero {α : Fin 0 → F} :
    iteratedFoldWord domain f 0 α = f := rfl

lemma iteratedFoldWord_succ {α : Fin (k + 1) → F} :
    iteratedFoldWord domain f (k + 1) α =
    foldWord (domain.subdomain k)
      (iteratedFoldWord domain f k (fun i ↦ α ⟨i.val, by omega⟩)) 1 (α ⟨k, by omega⟩) := by aesop

/-- Unfolding one round of `iteratedFoldWord` from the last round, with the randomness of the
  earlier rounds spelled as a restriction along `Fin.castSucc`. -/
lemma iteratedFoldWord_succ'
    {f : Word F (Fin (2 ^ n))} {α : Fin (k + 1) → F} :
    iteratedFoldWord domain f (k + 1) α =
      foldWord (domain.subdomain k) (iteratedFoldWord domain f k (fun i ↦ α i.castSucc)) 1
        (α (Fin.last k)) := rfl

omit [DecidableEq F] in
/-- TODO: this will go once this https://github.com/Verified-zkEVM/CompPoly/pull/203
  is merged. -/
private lemma eval_comm {f : Polynomial (Polynomial F)} {a x : F} :
  (f.eval (Polynomial.C a)).eval x = (Polynomial.map (evalRingHom x) f).eval a := by
  simp only [Polynomial.eval_map]
  have h_eval : Polynomial.eval (Polynomial.C a) f =
    ∑ i ∈ f.support, f.coeff i * (Polynomial.C a) ^ i := by
    aesop (add simp [Polynomial.eval_eq_sum])
  simp [h_eval, Polynomial.eval_finsetSum,
        Polynomial.eval₂_eq_sum, Polynomial.sum_def]

private lemma interpolate_eq_folding_poly_eval
  [FoldingContextMiddle k n]
  (hx : x ∈ domain.subdomain k) :
  ((Lagrange.interpolate (blockIdx domain k x) domain)
    f) =
  (Polynomial.map (evalRingHom x)
    (FoldingPolynomial.foldingPolynomial (Y ^ 2 ^ k) ((Lagrange.interpolate univ ⇑domain) f))) := by
  by_cases hf : f = 0
  · simp [hf]
  · apply eq_of_eval_eq_degree (n := 2 ^ k)
        (s := block domain k x)
    · exact lt_of_lt_of_le (Lagrange.degree_interpolate_lt _ (by simp)) <| by
        aesop (add safe (by norm_cast))
    · exact lt_of_le_of_lt Polynomial.degree_map_le <| by
        have h := FoldingPolynomial.folding_polynomial_deg_y_bound_x_k
          (f := (Lagrange.interpolate univ ⇑domain) f)
          (k := 2 ^ k)
        simp only [Bivariate.natDegreeY] at h
        rw [Polynomial.natDegree_lt_iff_degree_lt (
          FoldingPolynomial.folding_polynomial_ne_zero_of_ne_zero <|
            fun contra ↦ hf <| by
              ext x
              aesop
                (erase Lagrange.interpolate_apply)
                (add safe (by rw [←Lagrange.eval_interpolate_at_node
                  (s := univ) (v := domain) f]))
        )] at h
        exact h
    · simp [card_block_of_mem_subdomain' (by grind) hx]
    · simp only [mem_block, and_imp]
      rintro u ⟨i, hu₁⟩ hu₂
      rw [←hu₂, ←foldValue_def', ←hu₁,
        FoldingPolynomial.eval_property_of_folding_polynomial_x_k]
      aesop
        (erase Lagrange.interpolate_apply)
        (add safe (by rw [Lagrange.eval_interpolate_at_node]))
        (add simp [FoldingPolynomial.eval_property_of_folding_polynomial_x_k])

open FoldingContext in
/-- Perfect completeness of folding: folding a codeword is the same as
  applying `polyFold` and then encoding.

  `d` and `n` are the log degree and the log size of the RS-code
  respectively.
-/
theorem foldWord_codeword {d : ℕ} [FoldingContext k d n]
    {α : F}
  {p : ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) (2 ^ d)} :
  foldWord domain p k α =
    evalOnPoints (domain.subdomain k)
        (FoldingPolynomial.polyFold (ReedSolomon.toPolynomial p) (2 ^ k) α) := by
  ext x
  simp only [foldWord, foldValue, foldWordAux, evalOnPoints,
    toPolynomial, LinearMap.coe_mk, AddHom.coe_mk,
    FoldingPolynomial.polyFold]
  rw [eval_comm, interpolate_eq_folding_poly_eval (by simp)]
  rfl

theorem foldWord_evalOnPoints [FoldingContextMiddle k n]
    {α : F} {p : Polynomial F}
  (hp_deg : p.degree < 2 ^ n) :
  foldWord domain (evalOnPoints domain p) k α =
    evalOnPoints (domain.subdomain k)
        (FoldingPolynomial.polyFold p (2 ^ k) α) := by
  have : FoldingContext k n n := FoldingContext.ofMiddle
  let f := evalOnPoints (domain : Fin (2 ^ n) ↪ F) p
  have hcode : f ∈ code domain (2 ^ n) := by simp_all [evalOnPoints_mem_code_of_degree_lt, f]
  rw [show evalOnPoints _ _ = (⟨f, hcode⟩ : code _ _) by rfl, foldWord_codeword]
  simp_all [toPolynomial_evalWord_of_degree_lt, f]

/-- Perfect completeness of folding: if a word belongs to an RS-code
  then its `foldWord` belongs to a folded RS-code.

  `d` and `n` are the log degree and the log size of the
  original RS-code respectively.
-/
theorem foldWord_mem_code_of_mem_code {d : ℕ} [FoldingContext k d n]
    {α : F}
  {f : Word F (Fin (2 ^ n))}
  (hf : f ∈ ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) (2 ^ d)) :
  foldWord domain f k α ∈
    ReedSolomon.code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) (2 ^ (d - k)) := by
  have hf' :=
    ReedSolomon.mem_code_iff_exists_polynomial'.mp hf
  obtain ⟨p, hf'⟩ := hf'
  apply ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval
    (p := FoldingPolynomial.polyFold p (2 ^ k) α)
  · exact lt_of_le_of_lt FoldingPolynomial.polyFold_natDegree_le <| by
      by_cases hp : p = 0
      · aesop (add safe (by omega))
      · rw [Nat.div_lt_iff_lt_mul (by simp)]
        have : p.natDegree < 2 ^ d := by
          rw [←Polynomial.natDegree_lt_iff_degree_lt hp] at hf'
          aesop
        grind
  · intro i
    have := foldWord_codeword (α := α) (p := ⟨f, hf⟩)
    simp only at this
    simp only [this, evalOnPoints,
      LinearMap.coe_mk, AddHom.coe_mk]
    obtain ⟨hp_deg, hf'⟩ := hf'
    subst hf'
    congr
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
      (v := domain) (s := univ) (by simp)
    · exact lt_of_lt_of_le (ReedSolomon.toPolynomial_lt_min_deg_card _) <| by
        norm_cast
        simp
    · exact lt_of_lt_of_le hp_deg <| by
        norm_cast
        simp
    · intro i _
      conv_lhs =>
        rw [show domain i = (domain : (Fin (2 ^ n)) ↪ F) i by rfl]
      rw [ReedSolomon.toPolynomial_eval_at_domain]
      simp [evalOnPoints]

/-- Perfect completeness of iterated folding, with the context inequalities as explicit
  hypotheses (so that the statement can be used inductively). -/
private lemma iteratedFoldWord_mem_code_of_mem_code_aux {d : ℕ}
    {α : Fin k → F} {f : Word F (Fin (2 ^ n))}
    (hkd : k ≤ d) (hdn : d ≤ n)
    (hf : f ∈ ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) (2 ^ d)) :
    iteratedFoldWord domain f k α ∈
      ReedSolomon.code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) (2 ^ (d - k)) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    have hprev := ih (α := fun i ↦ α ⟨i.val, by omega⟩) (by omega)
    have : FoldingContext 1 (d - k) (n - k) := FoldingContext.mk' le_rfl (by omega) (by omega)
    have hstep := foldWord_mem_code_of_mem_code (domain := domain.subdomain k) (k := 1)
      (α := α ⟨k, by omega⟩) hprev
    rw [subdomain_subdomain_one (by omega)] at hstep
    rw [iteratedFoldWord_succ]
    exact hstep

/-- Perfect completeness of iterated folding: if a word belongs to an RS-code
  then its `iteratedFoldWord` belongs to a folded RS-code.
-/
theorem iteratedFoldWord_mem_code_of_mem_code {d : ℕ} [FoldingContext k d n]
    {α : Fin k → F} {f : Word F (Fin (2 ^ n))}
  (hf : f ∈ ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) (2 ^ d)) :
  iteratedFoldWord domain f k α ∈
    ReedSolomon.code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) (2 ^ (d - k)) :=
  iteratedFoldWord_mem_code_of_mem_code_aux FoldingContextLeft.k_le_d
    FoldingContextRight.d_le_n hf

private noncomputable def foldWordAuxCoeff (domain : SmoothCosetFftDomain n F)
  (f : Word F (Fin (2 ^ n))) (k : ℕ) (i : Fin (2 ^ k)) (x : F) : F :=
  (foldWordAux domain f k x).coeff i

private lemma foldWordAux_coeff_eq_foldWordAuxCoeff_fin {i : Fin (2 ^ k)} :
  (foldWordAux domain f k x).coeff i =
    foldWordAuxCoeff domain f k i x := by simp [foldWordAux, foldWordAuxCoeff]

private lemma foldWordAux_coeff_eq_foldWordAuxCoeff_nat {i : ℕ} :
  (foldWordAux domain f k x).coeff i =
    if h : i < 2 ^ k
    then foldWordAuxCoeff domain f k ⟨i, h⟩ x
    else 0 := by
  by_cases h : i < 2 ^ k <;> simp only [h, ↓reduceDIte]
  · rw [←foldWordAux_coeff_eq_foldWordAuxCoeff_fin]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt <|
            lt_of_lt_of_le foldWordAux_natDegree <| by simpa using h]

private lemma foldWordAux_eq_sum_of_foldWordAuxCoeff :
  foldWordAux domain f k x =
    ∑ j, Polynomial.C (foldWordAuxCoeff domain f k j x) * Y ^ j.val := by
  ext n
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  by_cases hlt : n < 2 ^ k
  · aesop
      (add simp [foldWordAuxCoeff])
      (add safe [(by rw [Finset.sum_eq_single_of_mem ⟨n, hlt⟩])])
  · simp only [foldWordAux_coeff_eq_foldWordAuxCoeff_nat, hlt, ↓reduceDIte]
    exact symm ∘ Finset.sum_eq_zero <| fun x _ ↦ match x with
      | ⟨x, hx⟩ => by aesop (add safe (by omega))

private lemma foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha
  {α : F} :
  foldValue domain f k α x =
    ∑ j, (foldWordAuxCoeff domain f k j x) * α ^ j.val := by
  aesop
    (add simp
      [foldValue,
        Polynomial.eval_finsetSum,
        foldWordAux_eq_sum_of_foldWordAuxCoeff])

private noncomputable def indicatedPolynomial
  (domain : SmoothCosetFftDomain n F) (f : Word F (Fin (2 ^ n))) (k : ℕ) (s' : Finset F) :
  Polynomial (Polynomial F) := ∑ x ∈ s',
    Polynomial.C (singletonIndicator x s') *
      (Polynomial.map Polynomial.C <| foldWordAux domain f k x)

section IndicatedPolynomial

variable {s' : Finset F}

omit [Field F] [DecidableEq F] in
private theorem card_ne_zero (hs' : s'.Nonempty) : NeZero (Finset.card s') where
  out := by aesop

private lemma indicated_polynomial_degree_x_lt (hs' : s'.Nonempty) :
  Bivariate.degreeX (indicatedPolynomial domain f k s') < s'.card := by
  simp only [Bivariate.degreeX, indicatedPolynomial, finsetSum_coeff, coeff_C_mul, coeff_map]
  rw [Finset.sup_lt_iff (by simp [hs'])]
  intro b hb
  exact natDegree_sum_lt_of_forall_lt (inst := card_ne_zero hs') _ _ <|
    fun i hi ↦ lt_of_le_of_lt natDegree_mul_le <| by
      aesop
        (add simp [singleton_indicator_natDegree_lt_of_mem])

private lemma indicated_polynomial_degree_y_lt :
  Bivariate.natDegreeY (indicatedPolynomial domain f k s') < 2 ^ k := by
  simp only [Bivariate.natDegreeY, indicatedPolynomial]
  exact natDegree_sum_lt_of_forall_lt _ _ <| fun i hi ↦
    lt_of_le_of_lt natDegree_mul_le <| by
      aesop
        (add simp [foldWordAux_natDegree])
        (add safe (by omega))

private lemma indicated_polynomial_eq_foldAux {α : F} (hx : x ∈ s') :
  ((indicatedPolynomial domain f k s').eval (Polynomial.C α)).eval x =
    (foldWordAux domain f k x).eval α := by
  aesop
    (add simp [indicatedPolynomial, eval_finsetSum])
    (add safe
      [(by rw [singleton_indicator_eval_eq_zero_of_mem_sdiff]),
        (by rw [Finset.sum_eq_ite x])])

private lemma indicated_polynomial_eval_eq_combination_of_correlated
  {u : Fin (2 ^ k) → Polynomial F}
  {α : F}
  (hu : ∀ i x, x ∈ s' → (u i).eval x = foldWordAuxCoeff domain f k i x)
  (hx : x ∈ s') :
  ((indicatedPolynomial domain f k s').eval (Polynomial.C α)).eval x =
    ∑ i, (u i).eval x * α ^ i.val := by
  aesop
    (add safe (by rw [←foldValue_def]))
    (add simp
      [indicated_polynomial_eq_foldAux,
        foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha])

private lemma indicated_polynomial_eq_combination_of_correlated
  (hs' : s'.Nonempty)
  {u : Fin (2 ^ k) → Polynomial F}
  {α : F}
  (hu : ∀ i x, x ∈ s' → (u i).eval x = (foldWordAuxCoeff domain f k i x))
  (hu_deg : ∀ i, (u i).natDegree < s'.card) :
  ((indicatedPolynomial domain f k s').eval (Polynomial.C α)) =
    ∑ i, (u i) * Polynomial.C (α ^ i.val) := by
  apply Polynomial.eq_of_eval_eq_natDegree (s := s') (n := #s')
    <;> try rfl
  · simp only [indicatedPolynomial,
      eval_finsetSum, eval_mul, eval_C, eval_map_apply]
    exact natDegree_sum_lt_of_forall_lt (inst := card_ne_zero hs') _ _ <|
      fun i _ ↦ lt_of_le_of_lt natDegree_mul_le <| by
        aesop
          (add simp [singleton_indicator_natDegree_lt_of_mem])
  · exact natDegree_sum_lt_of_forall_lt (inst := card_ne_zero hs') _ _ <|
      fun i _ ↦ lt_of_le_of_lt natDegree_mul_le <| by simp [hu_deg]
  · aesop
      (add safe forward
        [indicated_polynomial_eval_eq_combination_of_correlated])
      (add simp [eval_finsetSum])

private lemma indicated_polynomial_eq_foldAux'
  [Fintype F]
  {s' : Finset F}
  {u : Fin (2 ^ k) → Polynomial F}
  (hx : ∀ i, (u i).eval x = (foldWordAuxCoeff domain f k i x))
  (hu : ∀ i x, x ∈ s' → (u i).eval x = (foldWordAuxCoeff domain f k i x))
  (hu_deg : ∀ i, (u i).natDegree < s'.card)
  (h_s' : s'.Nonempty)
  (h_card : 2 ^ k ≤ Fintype.card F) :
  (Polynomial.map
    (Polynomial.evalRingHom x)
    (indicatedPolynomial domain f k s')) =
    foldWordAux domain f k x := by
  refine Polynomial.eq_of_eval_eq_natDegree (s := Finset.univ) (n := 2 ^ k) ?_ ?_ ?_ ?_
  · simp only
      [indicatedPolynomial, Polynomial.map_sum,
        Polynomial.map_mul, map_C, coe_evalRingHom]
    exact natDegree_sum_lt_of_forall_lt _ _ <| fun i hi ↦
      lt_of_le_of_lt natDegree_mul_le <| by
        aesop
          (add simp [Polynomial.map_map])
          (add safe [foldWordAux_natDegree])
  · exact foldWordAux_natDegree
  · simpa using h_card
  · intro α _
    rw [←eval_comm,
      indicated_polynomial_eq_combination_of_correlated h_s' hu hu_deg,
      eval_finsetSum, ←foldValue_def,
      foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha]
    simp only [eval_mul, eval_C, hx]

private lemma foldWordAux_poly_sum {a : F} :
  ((foldWordAux domain f k a).sum fun e a ↦ Polynomial.C a * Polynomial.X ^ e) =
  foldWordAux domain f k a := by
  aesop (add safe
    [(by rw [←Polynomial.sum_monomial_eq]),
     (by rw [Polynomial.sum])])

private lemma indicated_polynomial_comp_x_k_natDegree
  (hs' : s'.Nonempty) :
  ((Polynomial.map (Polynomial.compRingHom (Polynomial.X ^ 2 ^ k)) <|
    indicatedPolynomial domain f k s').eval Polynomial.X).natDegree < (2 ^ k) * s'.card := by
  by_cases h_card : 1 < s'.card
  · simp only [indicatedPolynomial,
      Polynomial.eval_map, eval₂_finsetSum,
      eval₂_mul, eval₂_C, coe_compRingHom]
    exact natDegree_sum_lt_of_forall_lt
      (inst := instNeZeroNatHMul (hm := card_ne_zero hs')) _ _ <|
      fun i hi ↦ lt_of_le_of_lt natDegree_mul_le <| by
      simp only [natDegree_comp, natDegree_pow, natDegree_X, mul_one, eval₂_map,
        eval₂, RingHom.coe_comp, coe_compRingHom, comp_apply, C_comp, foldWordAux_poly_sum]
      have h_ind :=
        Nat.le_sub_one_of_lt (singleton_indicator_natDegree_lt_of_mem hi)
      exact lt_of_le_of_lt
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ h_ind) _) <|
          lt_of_lt_of_le
            (Nat.add_lt_add_left foldWordAux_natDegree _) <| by
            rw [Nat.mul_comm, ←Nat.mul_add_one]
            grind +ring
  · have h_card : #s' = 1 := by grind
    aesop
      (add unsafe [(by rw [Polynomial.eval_map, Polynomial.eval₂_map, eval₂])])
      (add simp [Finset.card_eq_one, indicatedPolynomial,
        singletonIndicator, indicator,
        foldWordAux_poly_sum])
      (add safe [foldWordAux_natDegree])

end IndicatedPolynomial

omit [DecidableEq F] in
private lemma eval_comp_x_pow_map_eq {f : Polynomial (Polynomial F)} {x : F}
  {k : ℕ} :
  Polynomial.eval x
    (Polynomial.eval
        Polynomial.X
        (Polynomial.map (Polynomial.X ^ k).compRingHom f)) =
             (Polynomial.eval
               x
               (Polynomial.map
                (Polynomial.evalRingHom (x ^ k))
                f)) := by
  induction f using Polynomial.induction_on <;> aesop (add simp pow_succ)

private noncomputable def hammingDistComplementBound
  {n : ℕ} (k : ℕ) (domain : SmoothCosetFftDomain n F) (s : Finset F) : ℕ :=
  Finset.card (Pullback.pullback domain 0 k s)

private noncomputable def hammingDistBound
  {n : ℕ} (k : ℕ) (domain : SmoothCosetFftDomain n F) (s : Finset F) : ℕ :=
  Fintype.card (Fin (2 ^ n)) - hammingDistComplementBound k domain s

@[simp]
private lemma contradictory_hamming_dist_zero :
  hammingDistBound k domain ∅ = 2 ^ n := by
  simp [hammingDistBound, hammingDistComplementBound]

@[simp]
private lemma contradictory_hamming_dist_formula {s : Finset F}
  [FoldingContextMiddle k n]
  (h_s : s ⊆ (domain.subdomain k).toFinset) :
  hammingDistBound k domain s =
    2 ^ n - 2 ^ k * Finset.card s := by
  aesop
    (add simp [hammingDistBound, hammingDistComplementBound])
    (add safe [(by grind),
               (by rw [Pullback.card_pullback_eq_mul_card_pullback₂,
                      Pullback.card_pullback₂_eq])])

private lemma correlated_agreement_implies_contradictory_hamm_dist
  [Fintype F]
  {s : Finset F}
  (h_s : s ⊆ (domain.subdomain k).toFinset)
  {u : Fin (2 ^ k) → Polynomial F}
  (h_u : ∀ i, ∀ x ∈ s, (u i).eval x =
    foldWordAuxCoeff domain f k i x)
  {d : ℕ} [FoldingContextLeft k d]
  (h_k_card : (2 ^ k) ≤ Fintype.card F)
  (h_u_deg : ∀ i, (u i).natDegree < 2 ^ (d - k)) :
  ∃ f' : Polynomial F,
    f'.natDegree < 2 ^ d ∧
      hammingDist f (fun x => f'.eval (domain x)) ≤
        hammingDistBound k domain s := by
  by_cases h_empty : s = ∅
  · exists (C <| f 0)
    aesop
      (add safe (by grind))
      (add unsafe (by rw [←Finset.compl_filter, Finset.card_compl]))
      (add simp [hammingDist, Finset.card_sdiff])
  · let s' := s.pickSubset (2 ^ (d - k))
    have h_nonempty : s.Nonempty := by grind
    have h_s'_card : s'.card = min s.card (2 ^ (d - k)) := by simp [s']
    have h_s'_non_empty : s'.Nonempty := by aesop
    exists ((Polynomial.map (Polynomial.compRingHom (Polynomial.X ^ (2 ^ k))) <|
      indicatedPolynomial domain f k s').eval Polynomial.X)
    constructor
    · exact lt_of_lt_of_le
        (indicated_polynomial_comp_x_k_natDegree h_s'_non_empty)
        (FoldingContext.pow_2_k_mul_le_pow_2_d_of (by simp_all))
    · simp only [hammingDist, ne_eq, hammingDistBound, Fintype.card_fin]
      rw [←Finset.compl_filter, Finset.card_compl, Fintype.card_fin]
      apply Nat.sub_le_sub_left
      rw [hammingDistComplementBound, Pullback.card_pullback_eq_card_pullback₁]
      apply Finset.card_le_card
      intro x hx
      have hx := Pullback.mem_s_of_mem_pullback₁ hx
      rw [subdomain_0_apply] at hx
      simp only [tsub_zero, Nat.sub_zero, mem_filter, mem_univ, true_and] at hx ⊢
      rw [eval_comp_x_pow_map_eq]
      by_cases h_s'_s : s' = s
      · rw [h_s'_s,
            ←eval_comm,
            indicated_polynomial_eq_foldAux (by simp [hx]),
            ←foldValue_def,
            foldValue_pow_x_k]
      · rw [indicated_polynomial_eq_foldAux' (u := u) (by aesop)] <;> try assumption
        · rw [←foldValue_def, foldValue_pow_x_k]
        · intro i x hx
          have hx := (pick_subset_subset : s' ⊆ s) hx
          rw [h_u _ _ hx]
        · intro i
          exact lt_of_lt_of_le
            (h_u_deg i)
            (by rw [pick_subset_card_eq_of_ne h_s'_s])

open FoldingContext in
private lemma dist_from_code_bound_of_correlated_agreement
  [Finite F]
  {s : Finset F}
  (h_s : s ⊆ (domain.subdomain k).toFinset)
  {u : Fin (2 ^ k) → Polynomial F}
  (h_u : ∀ i, ∀ x ∈ s, (u i).eval x =
      foldWordAuxCoeff domain f k i x)
  {d : ℕ} [FoldingContext k d n]
  (h_u_deg : ∀ i, (u i).natDegree < (2 ^ (d - k))) :
  Δ₀(f, ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) (2 ^ d))
        ≤ 2 ^ n -
          2 ^ k * Finset.card s := by
  have := Fintype.ofFinite
  simp only [distFromCode, SetLike.mem_coe]
  exact sInf_le_of_le
    (b := ↑(hammingDistBound k domain s))
    (h := by
      aesop
        (add safe (by rw [contradictory_hamming_dist_formula]))) <| by
    obtain ⟨f', h_f'_deg, hdist⟩ :=
      correlated_agreement_implies_contradictory_hamm_dist h_s h_u (by {
    exact le_trans (b := 2 ^ n) (by grind) <| by
      convert card_toFinset_le_fintype_card (ω := domain) <;> aesop
  }) h_u_deg
    simp only [Set.mem_ofPred_eq, Nat.cast_le]
    aesop (add safe [evalOnPoints_mem_code_of_natDegree_lt])

omit [DecidableEq F] in
/-- The rate of the folded RS-code is the same. -/
lemma folded_rate_eq {d : ℕ} [FoldingContext k d n] :
    LinearCode.rate
      (ReedSolomon.code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) (2 ^ (d - k))) =
    LinearCode.rate (ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) (2 ^ d)) := by
  simp only [rateOfLinearCode_eq_min_div, Fintype.card_fin]
  rw [min_def, min_def]
  have hdk : 2 ^ (d - k) ≤ 2 ^ (n - k) :=
    Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_right FoldingContextRight.d_le_n k)
  have hdn : 2 ^ d ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by omega) FoldingContextRight.d_le_n
  rw [if_pos hdk, if_pos hdn]
  field_simp
  norm_cast
  rw [← pow_add]
  have hk_d : k ≤ d := FoldingContextLeft.k_le_d
  have hd_n : d ≤ n := FoldingContextRight.d_le_n
  have hexp : d - k + n = n - k + d := by omega
  rw [hexp]
  exact pow_add 2 (n - k) d

omit [DecidableEq F] in
/-- The square root of the rate of the folded RS-code is the same. -/
lemma folded_sqrtRate_eq {d : ℕ} [FoldingContext k d n] :
    ReedSolomon.sqrtRate
     (2 ^ (d - k))
     (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) =
    ReedSolomon.sqrtRate (2 ^ d) (domain : Fin (2 ^ n) ↪ F) := by
  simp [ReedSolomon.sqrtRate, folded_rate_eq]

open FoldingContext in
/--
Folding preserves distance from Reed–Solomon codes.

For any word `f` over the smooth coset FFT domain, log degree parameter `d`,
folding parameter `k`, and distance threshold `δ` satisfying
`0 < δ < min (δᵣ(f, RS[2 ^ d])) (1 - sqrtRate(2 ^ d))`, the probability over a
uniformly random folding challenge `r : F` that the folded word is within
relative distance `δ` of the Reed–Solomon code of reduced degree
`2 ^ d / 2^k` on the folded subdomain is bounded by the proximity-gap error
term.

This is Lemma 4.9 from [ACFY24]: a random `2^k`-folding step preserves distance from
the corresponding Reed–Solomon code except with probability controlled by
`ProximityGap.errorBound`.
-/
theorem folding_preserves_distance
    [Fintype F]
  {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))} {d k : ℕ}
  [FoldingContext k d n]
  {δ : ℝ≥0}
  -- Retained to match the mathematical statement; the imported gap bound omits it.
  (_δ_gt_0 : 0 < δ)
  (δ_lt : δ < min (δᵣ(f, ReedSolomon.code (domain : Fin (2 ^ n) ↪ F) (2 ^ d)))
    (1 - (ReedSolomon.sqrtRate (2 ^ d) (domain : Fin (2 ^ n) ↪ F)))) :
    Pr_{ let r ←$ᵖ F}[δᵣ(foldWord domain f k r,
      ReedSolomon.code (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F)
      (2 ^ (d - k))) ≤ δ] ≤
        ((2 ^ k) - 1) * ProximityGap.errorBound δ (2 ^ (d - k))
        (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) := by
    have bound_tighter :
      (↑δ) < 1 - ReedSolomon.sqrtRate (2 ^ (d - k))
        (domain.subdomain k : Fin (2 ^ (n - k)) ↪ F) := by
        aesop
          (add safe
            [(by rw [folded_sqrtRate_eq]), (by norm_cast at *)])
    have correlated_agreement :=
      @correlatedAgreement_affine_curves (Fin (2 ^ (n - k))) _ _ F _ _ _
        (2 ^ k - 1) ((2 ^ (d - k)))
        (domain := domain.subdomain k) (δ := δ)
        (hδ_pos := _δ_gt_0) (hδ := bound_tighter)
    unfold foldWord δ_ε_correlatedAgreementCurves at *
    by_contra contra
    simp only [not_le, foldValue_eq_sum_of_foldAuxCoeff_mul_pow_alpha, bind_pure_comp, Functor.map,
      PMF.bind_apply,
      PMF.uniformOfFintype_apply,
      comp_apply, PMF.pure_apply, eq_iff_iff, true_iff,
      mul_ite, mul_one, mul_zero, tsum_fintype] at contra correlated_agreement
    let cast (x : Fin (2 ^ k - 1 + 1)) : Fin (2 ^ k) :=
      Fin.cast (by rw [Nat.sub_add_cancel (by grind)]) x
    let cast' (x : Fin (2 ^ k)) : Fin (2 ^ k - 1 + 1) :=
      Fin.cast (by rw [Nat.sub_add_cancel (by grind)]) x
    have bijective_cast : Bijective cast := by
      rw [bijective_iff_has_inverse]
      exists cast'
      simp [LeftInverse, RightInverse, cast, cast']
    specialize correlated_agreement
      (Matrix.of (fun i j ↦ foldWordAuxCoeff domain f k
        (cast i)
        (domain.subdomain k j)))
    have correlated_curve_eq_sum_of_foldWord_coeffs {a : F} :
      ∑ i : Fin (2 ^ k - 1 + 1), a ^ (↑i : ℕ) •
        Matrix.of (fun i j ↦
          foldWordAuxCoeff domain f k (cast i) (domain.subdomain k j)) i =
      (fun x ↦
        ∑ j, foldWordAuxCoeff domain f k j
          (domain.subdomain k x) * a ^ (↑j : ℕ)) := by
      ext x
      simp only [Finset.sum_apply]
      change (∑ i : Fin (2 ^ k - 1 + 1),
        a ^ (i : ℕ) * foldWordAuxCoeff domain f k (cast i) (domain.subdomain k x)) =
          ∑ j : Fin (2 ^ k), foldWordAuxCoeff domain f k j
            (domain.subdomain k x) * a ^ (j : ℕ)
      exact Fintype.sum_bijective cast bijective_cast _ _ <|
        fun i ↦ by simp [cast, mul_comm]
    specialize correlated_agreement (by {
      conv_lhs =>
        rhs
        ext a
        rw [correlated_curve_eq_sum_of_foldWord_coeffs]
      norm_cast at contra
    })
    simp only [jointAgreement, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, ge_iff_le,
      SetLike.mem_coe, Matrix.of_apply] at correlated_agreement
    obtain ⟨S, h_card, v, h'⟩ := correlated_agreement
    rw [forall_and] at h'
    rcases h' with ⟨h_rs, h'⟩
    have h_rs := fun x ↦ (mem_code_iff_exists_polynomial_of_ne_zero
        (ne := ⟨by simp⟩)).mp (h_rs x)
    let u : Fin (2 ^ k - 1 + 1) → Polynomial F :=
      fun i => Classical.choose (h_rs i)
    have contradiction := dist_from_code_bound_of_correlated_agreement (domain := domain) (f := f)
      (s := Finset.image
        (domain.subdomain k) S)
      (fun x hx ↦ by
        rw [CosetFftDomainClass.mem_toFinset_iff_mem]
        simp only [mem_image] at hx
        obtain ⟨x', _, hx'⟩ := hx
        aesop
      )
      (u := u ∘ cast')
      (fun i j hj ↦ by
        clear *- hj h'
        let i' := cast' i
        simp only [Finset.mem_image] at hj
        obtain ⟨j', hj, rfl⟩ := hj
        specialize h' i' hj
        have h_spec := congrFun (a := j') <| Classical.choose_spec (h_rs i') |>.2
        have h_agree' := (Finset.mem_filter.mp h').2
        have h_agree : v i' j' = foldWordAuxCoeff domain f k i (domain.subdomain k j') := by
          simpa [i', cast, cast'] using h_agree'
        exact h_spec.symm.trans h_agree
      )
      (d := d)
      (fun i ↦
        And.left <| Classical.choose_spec (h_rs (cast' i)))
    rw [Finset.card_image_of_injective _ (by simp)] at contradiction
    have contradiction : (Δ₀(f, code (domain : Fin (2 ^ n) ↪ F) (2 ^ d)) : ENNReal)
      ≤ (↑(2 ^ n) : ℚ≥0) * δ :=
      le_trans (ENat.toENNReal_le.mpr contradiction) <| by
        apply le_trans
          (b := (2 ^ n : ENNReal) - 2 ^ k * (1 - ↑δ) * 2 ^ (n - k))
        · rw [ENat.toENNReal_sub,
              show ENat.toENNReal (2 ^ n) = (2 ^ n : ENNReal) by simp,
              ENNReal.sub_le_sub_iff_left (h' := by simp)
                (h := swap (le_trans (b := 2 ^ n * 1)) (by simp) <| by
                  rw [mul_comm,
                      ←mul_assoc,
                      ←pow_add]
                  simp only [FoldingContextMiddle.k_le_n, Nat.sub_add_cancel]
                  rw [ENNReal.mul_le_mul_iff_right (by simp) (by simp)]
                  simp
          )]
          apply le_trans (b := 2 ^ k * ↑↑(#S))
          · rw [mul_assoc,
                ENNReal.mul_le_mul_iff_right (by simp) (by simp)]
            have h_card := ENNReal.coe_le_coe.mpr h_card
            exact (swap le_trans h_card) (by norm_cast)
          · norm_cast
        · rw [mul_comm,
              ←mul_assoc,
              ←pow_add]
          simp only [FoldingContextMiddle.k_le_n, Nat.sub_add_cancel]
          conv_lhs =>
            lhs
            rw [←mul_one (2 ^ n)]
          rw [←ENNReal.mul_sub (by simp),
              ENNReal.sub_sub_cancel (by simp)
                (by {
                  simp only [lt_inf_iff] at δ_lt
                  exact le_trans (le_of_lt δ_lt.2) (by simp)
                })]
          norm_cast
    have contradiction : δᵣ(f, code (domain : Fin (2 ^ n) ↪ F) (2 ^ d)) ≤ (δ : NNReal) := by
      rw [relDistFromCode_le_iff_distFromCode_toENNReal_le]
      exact le_trans contradiction <| by
        simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
        rw [mul_comm]
        norm_cast
    simp only [lt_inf_iff] at δ_lt
    simpa using lt_of_lt_of_le δ_lt.1 contradiction

end

end ProximityGap
