/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module


public import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude
public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch

/-!
# Binary Basefold codes and decoding

## Main definitions

* `code`, `codeDistance`: the Reed–Solomon code on `S⁽ⁱ⁾` used at round `i`, and its
  minimum distance.
* `fiberwiseDisagreementSet`, `fiberwiseDistance`, `FiberwiseClose`: distance counted over the
  fibers of `S⁽ⁱ⁾ → S⁽ⁱ⁺ˢᵗᵉᵖˢ⁾`.
* `UniqueDecodingClose`, `uniqueDecodingCodeword`: closeness within the unique-decoding radius
and the unique close
  codeword.

## Main statements

* `uniqueDecodingClose_of_fiberwiseClose`: fiberwise closeness implies closeness within the
unique-decoding
  radius.
* `fold_mem_code`, `iteratedFold_mem_code`: folding
  maps codewords to codewords.

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Numbering follows the archived revision of [DP24].
-/

@[expose] public section

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open Code ReedSolomon BerlekampWelch ProbabilityTheory

noncomputable section SoundnessTools

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [hF₂ : Fact (Fintype.card 𝔽q = 2)]
local instance instFactPrimeRingCharCode [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) :=
  ⟨CharP.prime_ringChar 𝔽q⟩
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}

/-!
### Binary Basefold Specific Code Definitions

Reed–Solomon codes and their fiberwise distance on the folding domains.
-/

/-- The Reed–Solomon evaluation code on `S⁽ⁱ⁾` with degree bound `2 ^ (ℓ - i)`. -/
def code (i : Fin r) :
    Submodule L ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L) :=
  let domain : (sDomain 𝔽q β h_ℓ_add_R_rate) i ↪ L :=
    ⟨fun x => x.val, fun x y h => by exact Subtype.ext h⟩
  ReedSolomon.code (domain := domain) (deg := 2^(ℓ - i.val))

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
/-- Every codeword is the evaluation of a polynomial below the round degree bound. -/
lemma exists_polynomial_of_mem_code (i : Fin r)
    (u : (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
  ∃ P : L⦃<2^(ℓ-i)⦄[X],
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i) (P := P) = u := by
  have h_u_mem := u.property
  unfold code at h_u_mem
  simp only [ReedSolomon.code, evalOnPoints, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.mem_map] at h_u_mem
  obtain ⟨P_raw, hP_raw⟩ := h_u_mem
  -- Construct the subtype element
  let P : L⦃<2^(ℓ-i)⦄[X] := ⟨P_raw, hP_raw.1⟩
  use P
  -- Prove the evaluation part
  exact hP_raw.2

/-- Choose a polynomial below the round degree bound that evaluates to the codeword. -/
def codewordPolynomial (i : Fin r)
    (u : (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) : L⦃<2^(ℓ-i)⦄[X] :=
  Classical.choose (exists_polynomial_of_mem_code 𝔽q β i u)

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
/-- The chosen polynomial evaluates to the original codeword. -/
lemma codewordPolynomial_spec (i : Fin r)
    (u : (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
  u = polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i)
    (P := codewordPolynomial 𝔽q β i u) := by
  let res := Classical.choose_spec (exists_polynomial_of_mem_code 𝔽q β i u)
  exact id (Eq.symm res)

/-- Evaluate a polynomial below the round degree bound as a codeword. -/
def polynomialCodeword (i : Fin r) (P : L⦃< 2 ^ (ℓ - i)⦄[X]) :
    (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  let g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i :=
    polyToOracleFunc 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (domainIdx := i) (P := P)
  have h_g_mem : g ∈ code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
    unfold code
    simp only [ReedSolomon.code, evalOnPoints, LinearMap.coe_mk,
      AddHom.coe_mk, Submodule.mem_map]
    use P
    constructor
    · simp only [SetLike.coe_mem]
    · funext y
      exact rfl
  exact ⟨g, h_g_mem⟩

/-- The minimum distance of the code at index `i`. -/
abbrev codeDistance (i : Fin r) : ℕ :=
  ‖((code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    Set ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L))‖₀

omit [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
/-- At an active round, minimum distance is domain size minus dimension plus one. -/
lemma codeDistance_eq (i : Fin r) (h_i : i ≤ ℓ) :
    codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    = 2^(ℓ + 𝓡 - i.val) - 2^(ℓ - i.val) + 1 := by
  unfold codeDistance
  -- Create the embedding from domain elements to L
  let domain : (sDomain 𝔽q β h_ℓ_add_R_rate) i ↪ L :=
    ⟨fun x => x.val, fun x y h => by exact Subtype.ext h⟩
  -- Create α : Fin m → L by composing with an equivalence
  let m := Fintype.card ((sDomain 𝔽q β h_ℓ_add_R_rate) i)
  have h_dist_RS := ReedSolomon.dist_eq_of_le (F := L) (ι := (sDomain 𝔽q β h_ℓ_add_R_rate)
    (i := i)) (α := domain) (n := 2^(ℓ - i.val)) (by
      rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := lt_rounds_add_rate_of_le_rounds (by
        omega))]
      rw [hF₂.out];
      apply Nat.pow_le_pow_right (hx := by omega); omega
    )
  unfold code
  rw [h_dist_RS]
  rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := lt_rounds_add_rate_of_le_rounds (by
    omega)), hF₂.out]

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
/-- Every round code contains distinct constant codewords, so its minimum distance is positive. -/
lemma codeDistance_pos (i : Fin r) :
    0 < codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
  unfold codeDistance code
  exact Code.dist_pos_of_Nontrivial _ ReedSolomon.code_Nontrivial

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
/-- The minimum distance of every round code is nonzero. -/
lemma codeDistance_neZero (i : Fin r) :
    NeZero (codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
  ⟨ne_of_gt (codeDistance_pos 𝔽q β i)⟩

/-- Disagreement set Δ : The set of points where two functions disagree.
For functions f^(i) and g^(i), this is {y ∈ S^(i) | f^(i)(y) ≠ g^(i)(y)}. -/
def disagreementSet (i : Fin r)
    {destIdx : Fin r} (h_destIdx : destIdx = i.val)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
  Finset ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :=
  have h_destIdx_eq_i : destIdx = i := Fin.ext h_destIdx
  {(y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) |
    f (cast (by subst h_destIdx_eq_i; rfl) y) ≠ g (cast (by subst h_destIdx_eq_i; rfl) y)}

/-- Fiber-wise disagreement set Δ^(i) : The set of points y ∈ S^(i+ϑ) for which
functions f^(i) and g^(i) are not identical when restricted to the entire fiber
of points in S⁽ⁱ⁾ that maps to y. -/
def fiberwiseDisagreementSet (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
  Finset ((sDomain 𝔽q β h_ℓ_add_R_rate) destIdx) :=
  -- The set of points `y ∈ S^{i+steps}` that there exists a
    -- point `x` in its fiber where `f x ≠ g x`
  {y | ∃ x, (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i)
    (k := steps) h_destIdx h_destIdx_le x) = y ∧ f x ≠ g x}

omit [DecidableEq 𝔽q] hF₂ [NeZero 𝓡] in
omit [NeZero ℓ] in
/-- Transport the disagreement fibers along equality of source indices. -/
lemma fiberwiseDisagreementSet_congr_sourceDomain_index
    (sourceIdx₁ sourceIdx₂ : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_sourceIdx_eq : sourceIdx₁ = sourceIdx₂)
    (h_destIdx : destIdx = sourceIdx₁.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) sourceIdx₁) :
  let Δ_fiber₁ := fiberwiseDisagreementSet 𝔽q β sourceIdx₁ steps h_destIdx h_destIdx_le f g
    let Δ_fiber₂ := fiberwiseDisagreementSet 𝔽q β sourceIdx₂ steps (by omega) h_destIdx_le
      (fun x => f (cast (by subst h_sourceIdx_eq; rfl) x))
      (fun x => g (cast (by subst h_sourceIdx_eq; rfl) x))
  Δ_fiber₁ = Δ_fiber₂ := by
  subst h_sourceIdx_eq
  rfl

omit [DecidableEq 𝔽q] hF₂ [NeZero ℓ] [NeZero 𝓡] in
/-- When `steps = 0`, the fiberwise disagreement set (projecting to `S^{i+0} = S^i`)
equals the ordinary pointwise disagreement set.
Both sides are stated with `destIdx := i` so they share the same `Finset` type. -/
@[simp]
lemma fiberwiseDisagreementSet_steps_zero_eq_disagreementSet
    (i destIdx : Fin r) (h_destIdx : destIdx = i.val + 0) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    fiberwiseDisagreementSet 𝔽q β i (steps := 0) (destIdx := destIdx)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f g =
    disagreementSet 𝔽q β (i := i) (destIdx := destIdx) (h_destIdx := h_destIdx) f g := by
  have h_destIdx_eq_i : destIdx = i := Fin.ext h_destIdx
  subst h_destIdx_eq_i
  ext y
  simp only [fiberwiseDisagreementSet, disagreementSet, Finset.mem_filter, Finset.mem_univ,
    true_and, ne_eq]
  constructor
  · rintro ⟨x, hxy, hfg⟩
    have hx_eq :
        iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := destIdx) (k := 0)
          (destIdx := destIdx) (h_destIdx := by simp) (h_destIdx_le := by omega) x = x := by
      apply Subtype.ext
      simp only [iteratedQuotientMap, intermediateNormVpoly, Fin.foldl_zero,
        Polynomial.eval_X, Subtype.coe_eta]
    rw [hx_eq] at hxy
    exact hxy ▸ hfg
  · intro hfg
    refine ⟨y, ?_, hfg⟩
    apply Subtype.ext
    simp only [iteratedQuotientMap, intermediateNormVpoly, Fin.foldl_zero,
      Polynomial.eval_X, Subtype.coe_eta]

omit [DecidableEq 𝔽q] hF₂ [NeZero ℓ] [NeZero 𝓡] in
/-- A fiber disagrees exactly when it contains a point on which the two words disagree. -/
@[simp]
lemma mem_fiberwiseDisagreementSet_iff (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :
    y ∈ fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g ↔
      ∃ x, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i := i) (k := steps)
        h_destIdx h_destIdx_le x = y ∧
        f x ≠ g x := by
  simp only [fiberwiseDisagreementSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The number of quotient fibers on which two words disagree. -/
def pairFiberwiseDistance (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : ℕ :=
    (fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g).card

/-- Fiber-wise distance d^(i) : The minimum size of the fiber-wise disagreement set
between f^(i) and any codeword in C^(i). -/
def fiberwiseDistance (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : ℕ :=
  -- The minimum size of the fiber-wise disagreement set between f^(i) and any codeword in C^(i)
  -- d^(i)(f^(i), C^(i)) := min_{g^(i) ∈ C^(i)} |Δ^(i)(f^(i), g^(i))|
  let C_i := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  let disagreement_sizes := (fun (g : C_i) =>
    pairFiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      steps h_destIdx h_destIdx_le (f := f) (g := g)
  ) '' Set.univ
  sInf disagreement_sizes

/-- Fiberwise closeness : f^(i) is fiberwise close to C^(i) if
2 * d^(i)(f^(i), C^(i)) < d_{i+steps} -/
def FiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  2 * (fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f)) <
      (codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx): ℕ∞)

/-- Two words are close when twice their disagreeing-fiber count is below the destination
distance. -/
def PairFiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
    2 * pairFiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps
      h_destIdx h_destIdx_le (f := f) (g := g) <
      (codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx): ℕ∞)

/-- Hamming UDR-closeness : f is close to C in Hamming distance if `2 * d(f, C) < d_i` -/
def UniqueDecodingClose (i : Fin r)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
    2 * Δ₀(f, (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) <
      codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)

/-- Two words are within the decoding radius when twice their Hamming distance is below code
distance. -/
def PairUniqueDecodingClose (i : Fin r)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  2 * Δ₀(f, g) < codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
/-- Congruence lemma for `UniqueDecodingClose`: transport along a `Fin r` equality.
Given two `Fin r` indices with the same value and `HEq` functions, `UniqueDecodingClose`
transfers. -/
lemma uniqueDecodingClose_congr {i j : Fin r} (hij : i = j)
    {f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i}
    {g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j}
    (hfg : HEq f g) (h : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f) :
    UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j g := by
  subst hij
  exact eq_of_heq hfg ▸ h

omit [DecidableEq 𝔽q] hF₂ [NeZero 𝓡] [NeZero ℓ] in
/-- When `steps = 0`, `pairFiberwiseDistance` equals the Hamming distance. -/
@[simp]
lemma pairFiberwiseDistance_steps_zero_eq_hammingDist
    (i : Fin r) (h_i_le : i ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    pairFiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (destIdx := i) (steps := 0) (h_destIdx := by omega) (h_destIdx_le := by omega)
      (f := f) (g := g) = hammingDist f g := by
  rw [pairFiberwiseDistance, fiberwiseDisagreementSet_steps_zero_eq_disagreementSet 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (destIdx := i)
    (h_destIdx := by omega) (h_destIdx_le := by omega) f g]
  simp only [disagreementSet, cast_eq, ne_eq, card_filter, ite_not, hammingDist]

omit [DecidableEq 𝔽q] hF₂ [NeZero 𝓡] [NeZero ℓ] in
/-- When `steps = 0`, fiberwise closeness coincides with UDR closeness. -/
@[simp]
lemma fiberwiseClose_steps_zero_iff_uniqueDecodingClose
    (i destIdx : Fin r) (h_destIdx : destIdx = i.val + 0) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (steps := 0)
      (destIdx := destIdx) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) f ↔
    UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i  f := by
  have h_destIdx_eq_i : destIdx = i := Fin.ext h_destIdx
  subst h_destIdx_eq_i
  have h_dist_eq :
      (fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
        (steps := 0) (destIdx := destIdx) (h_destIdx := by simp)
        (h_destIdx_le := by omega) (f := f) : ℕ∞) =
        Δ₀(f, (↑(code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) :
          Set (OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx))) := by
    let C_i := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    let S : Set ℕ := (fun (g : C_i) => hammingDist f g) '' Set.univ
    let SENat : Set ℕ∞ := (fun (g : C_i) => (hammingDist f g : ℕ∞)) '' Set.univ
    have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
    have h_coe_sinfS_eq_sinfSENat : ↑(sInf S) = sInf SENat := by
      rw [ENat.natCast_sInf (hs := hS_nonempty)]
      simp only [SENat, Set.image_univ, sInf_range]
      simp only [S, Set.image_univ, iInf_range]
    have h_distFromCode_eq_sInf :
        Δ₀(f, (↑C_i :
          Set (OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx))) =
        sInf SENat := by
      apply le_antisymm
      · simp only [Code.distFromCode]
        apply sInf_le_sInf
        intro a ha
        rcases (Set.mem_image _ _ _).mp ha with ⟨g, _, rfl⟩
        exact ⟨g, g.property, le_refl _⟩
      · simp only [Code.distFromCode]
        apply le_sInf
        intro d hd
        rcases hd with ⟨v, hv_mem, h_dist_v_le_d⟩
        have h_sInf_le_dist_v : sInf SENat ≤ ↑(hammingDist f v) := by
          apply sInf_le
          rw [Set.mem_image]
          exact ⟨⟨v, hv_mem⟩, Set.mem_univ _, rfl⟩
        exact h_sInf_le_dist_v.trans h_dist_v_le_d
    unfold fiberwiseDistance
    simp only [pairFiberwiseDistance_steps_zero_eq_hammingDist]
    rw [h_coe_sinfS_eq_sinfSENat, ← h_distFromCode_eq_sInf]
  unfold FiberwiseClose UniqueDecodingClose
  rw [h_dist_eq]

omit [DecidableEq 𝔽q] hF₂ [NeZero 𝓡] in
omit [NeZero ℓ] in
/-- Transport fiberwise code closeness along equality of source indices. -/
lemma fiberwiseClose_congr_sourceDomain_index
    (sourceIdx₁ sourceIdx₂ : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_sourceIdx_eq : sourceIdx₁ = sourceIdx₂)
    (h_destIdx : destIdx = sourceIdx₁.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) sourceIdx₁) :
  let Δ_fiber₁ := FiberwiseClose 𝔽q β sourceIdx₁ steps h_destIdx h_destIdx_le f
  let Δ_fiber₂ := FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    sourceIdx₂ steps (by omega) h_destIdx_le
    (fun x => f (cast (by subst h_sourceIdx_eq; rfl) x))
  Δ_fiber₁ = Δ_fiber₂ := by
  subst h_sourceIdx_eq
  rfl

section ConstantFunctions

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
/-- A constant word is the evaluation of a constant polynomial and belongs to every round code. -/
lemma const_mem_code {i : Fin r} (c : L) :
    (fun _ => c) ∈ (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)) := by
  unfold code
  simp only
  simp only [ReedSolomon.code, evalOnPoints, LinearMap.coe_mk,
    AddHom.coe_mk, Submodule.mem_map]
  use Polynomial.C c
  constructor
  · rw [Polynomial.mem_degreeLT]
    apply lt_of_le_of_lt (Polynomial.degree_C_le)
    norm_num
  · ext x; simp only [Polynomial.eval_C]

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] in
/-- A constant word has zero distance to the code and lies within its decoding radius. -/
lemma uniqueDecodingClose_const {i : Fin r} (c : L) :
    UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (fun _ => c) := by
  unfold UniqueDecodingClose
  have h_zero :
      Code.distFromCode (fun _ => c)
        ((↑(code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
          Set (OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) = 0 := by
    exact Code.distFromCode_of_mem
      (C := ((↑(code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) :
        Set (OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)))
      (u := fun _ => c)
      (const_mem_code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) c)
  simp only [h_zero, mul_zero]
  exact_mod_cast codeDistance_pos 𝔽q β i

end ConstantFunctions
omit [DecidableEq 𝔽q] h_β₀_eq_1 in
omit [NeZero ℓ] in
/-- The strict twice-distance bound is equivalent to the integral unique-decoding-radius bound. -/
lemma uniqueDecodingClose_iff_dist_le_uniqueDecodingRadius (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f ↔
    Δ₀(f, (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≤
      uniqueDecodingRadius (ι := (sDomain 𝔽q β h_ℓ_add_R_rate i))
        (F := L) (C := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  unfold UniqueDecodingClose
  let card_Sᵢ := sDomain_card 𝔽q β h_ℓ_add_R_rate (i := i) (h_i :=
    lt_rounds_add_rate_of_le_rounds (by omega))
  conv_rhs =>
    unfold code;
    rw [ReedSolomon.uniqueDecodingRadius_RS_eq (h := by
      rw [card_Sᵢ, hF₂.out]; apply Nat.pow_le_pow_right (hx := by omega); omega
    )];
  simp_rw [card_Sᵢ, hF₂.out,
    codeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega)]
  simp only [cast_add, ENat.natCast_sub, cast_pow, cast_ofNat, cast_one]
  constructor
  · intro h_UDRClose
    -- 1. Prove distance is finite
    -- The hypothesis implies 2 * Δ₀ is finite, so Δ₀ must be finite.
    have h_finite : Δ₀(f, ↑(code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≠ ⊤ := by
      intro h_top
      rw [h_top] at h_UDRClose
      exact not_top_lt h_UDRClose
    -- 2. Lift to Nat to use standard arithmetic
    lift Δ₀(f, ↑(code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) to ℕ
      using h_finite with d_nat h_eq
    dsimp only [code] at h_eq
    simp_rw [←h_eq]
    have h_lt : 2 * d_nat < 2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1 := by
      norm_cast at h_UDRClose ⊢ -- both h_UDRClose and ⊢ are in ENat
    simp only [Nat.cast_le]
    have h_le := Nat.le_of_lt_succ (m := 2 * d_nat) (n := 2^(ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) ) h_lt
    rw [Nat.mul_comm 2 d_nat] at h_le
    rw [←Nat.le_div_iff_mul_le (k0 := by norm_num)] at h_le
    exact h_le
  · intro h_within
    -- 1. Prove finite
    have h_finite : Δ₀(f, ↑(code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) ≠ ⊤ := by
      intro h_top
      unfold code at h_top
      simp only [h_top, top_le_iff, ENat.natCast_ne_top] at h_within
    -- 2. Lift to Nat
    lift Δ₀(f, ↑(code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) to ℕ
      using h_finite with d_nat h_eq
    unfold code at h_eq
    rw [←h_eq] at h_within
    norm_cast at h_within ⊢
    omega

/-- Unique closest codeword in the unique decoding radius of a function f -/
def uniqueDecodingCodeword (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_within_radius : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f) :
    OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i := by
  exact Classical.choose
    ((Code.UDR_close_iff_exists_unique_close_codeword
      (C := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) f).mp
      ((uniqueDecodingClose_iff_dist_le_uniqueDecodingRadius 𝔽q β i h_i f).mp h_within_radius))

omit [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
/-- The decoded word belongs to the code and is the unique codeword within the decoding radius. -/
lemma uniqueDecodingCodeword_spec (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h_close : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f) :
    let C : Set (OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :=
      code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    let g := uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f h_close
    g ∈ C ∧ Δ₀(f, g) ≤ uniqueDecodingRadius (C := C) ∧
      ∀ v : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i,
        v ∈ C → Δ₀(f, v) ≤ uniqueDecodingRadius (C := C) → v = g := by
  have h := Classical.choose_spec
    ((Code.UDR_close_iff_exists_unique_close_codeword
      (C := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) f).mp
      ((uniqueDecodingClose_iff_dist_le_uniqueDecodingRadius 𝔽q β i h_i f).mp h_close))
  exact ⟨h.1.1, h.1.2, fun v hv hd => h.2 v ⟨hv, hd⟩⟩

omit [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
/-- Decoding a constant word returns that word. -/
lemma uniqueDecodingCodeword_const (i : Fin r) (h_i : i ≤ ℓ) (c : L) :
    uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) h_i (f := fun _ => c)
    (h_within_radius := uniqueDecodingClose_const 𝔽q β c) = fun _ => c := by
  exact ((uniqueDecodingCodeword_spec 𝔽q β i h_i (fun _ => c)
    (uniqueDecodingClose_const 𝔽q β c)).2.2 (fun _ => c)
    (const_mem_code 𝔽q β c) (by simp)).symm

omit [DecidableEq 𝔽q] h_β₀_eq_1 in
omit [NeZero ℓ] in
/-- The decoded word belongs to the round code. -/
lemma uniqueDecodingCodeword_mem_code (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_within_radius : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f) :
  (uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f h_within_radius) ∈
    (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  exact (uniqueDecodingCodeword_spec 𝔽q β i h_i f h_within_radius).1

omit [DecidableEq 𝔽q] h_β₀_eq_1 in
omit [NeZero ℓ] in
/-- The decoded word is within the unique-decoding radius of its input. -/
lemma dist_to_uniqueDecodingCodeword_le_uniqueDecodingRadius (i : Fin r) (h_i : i ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_within_radius : UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f) :
  Δ₀(f, uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f h_within_radius) ≤
    uniqueDecodingRadius (ι := (sDomain 𝔽q β h_ℓ_add_R_rate i))
      (F := L) (C := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) := by
  exact (uniqueDecodingCodeword_spec 𝔽q β i h_i f h_within_radius).2.1

omit [DecidableEq 𝔽q] [NeZero ℓ] in
/-- Hamming distance is at most the number of disagreeing fibers times their common size. -/
lemma hammingDist_le_pairFiberwiseDistance_mul_pow_two (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    Δ₀(f, g) ≤ (pairFiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      steps h_destIdx h_destIdx_le (f := f) (g := g)) * 2 ^ steps := by
  classical
  let d_fw := pairFiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    steps h_destIdx h_destIdx_le (f := f) (g := g)
  have h_dist_le_fw_dist_times_fiber_size : (hammingDist f g) ≤ d_fw * 2 ^ steps := by
    -- This proves `dist f g ≤ (fiberwiseDisagreementSet ... f g).ncard * 2 ^ steps`
    -- and lifts to ℕ∞. We prove the `Nat` version `hammingDist f g ≤ ...`,
    -- which is equivalent.
    -- Let ΔH be the finset of actually bad x points where f and g disagree.
    set ΔH := Finset.filter (fun x => f x ≠ g x) Finset.univ
    have h_dist_eq_card : hammingDist f g = ΔH.card := by
      simp only [hammingDist, ne_eq, ΔH]
    rw [h_dist_eq_card]
    -- Y_bad is the set of quotient points y that THERE EXISTS a bad fiber point x
    set Y_bad := fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g
    have hFinType_Y_bad : Fintype Y_bad := by exact Fintype.ofFinite ↑Y_bad
    -- Every point of disagreement `x` must belong to a fiber over some `y` in `Y_bad`,
    -- BY DEFINITION of `Y_bad`. Therefore, `ΔH` is a subset of the union of the fibers
    -- of `Y_bad`
    have h_ΔH_subset_bad_fiber_points : ΔH ⊆ Finset.biUnion Y_bad
        (t := fun y => ((quotientFiber 𝔽q β (i := i) (steps := steps)
          h_destIdx h_destIdx_le (y := y)) ''
          (Finset.univ : Finset (Fin ((2:ℕ)^steps)))).toFinset) := by
      intro x hx_in_ΔH; -- ⊢ x ∈ Union(quotientFiber(y), ∀ y ∈ Y_bad)
      simp only [ΔH, Finset.mem_filter] at hx_in_ΔH
      -- Now we actually apply iterated qMap into x to get y_of_x,
      -- then x ∈ quotientFiber(y_of_x) by definition
      let y_of_x := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i (k := steps) h_destIdx h_destIdx_le x
      apply Finset.mem_biUnion.mpr; use y_of_x
      have h_elemenet_Y_bad : y_of_x ∈ Y_bad := by
        simp only [Y_bad, fiberwiseDisagreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨x, rfl, hx_in_ΔH.2⟩
      simp only [h_elemenet_Y_bad, true_and]
      set qMapFiber := quotientFiber 𝔽q β (i := i) (steps := steps)
        h_destIdx h_destIdx_le (y := y_of_x)
      simp only [coe_univ, Set.image_univ, Set.toFinset_range, mem_image, mem_univ, true_and]
      use (pointToIterateQuotientIndex (i := i) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (x := x))
      have h_res := eq_iteratedQuotientMap_iff_quotientFiber_apply_eq 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (x := x) (y := y_of_x).mp (by rfl)
      exact h_res
    apply (Finset.card_le_card h_ΔH_subset_bad_fiber_points).trans
    -- The cardinality of a disjoint union is the sum of cardinalities.
    rw [Finset.card_biUnion]
    · -- The size of the sum is the number of bad fibers (`Y_bad.ncard`) times
      -- the size of each fiber (`2 ^ steps`).
      simp only [Set.toFinset_card]
      have h_card_fiber_per_quotient_point := card_quotientFiber 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      simp only [Set.image_univ, Fintype.card_ofFinset,
        Subtype.forall] at h_card_fiber_per_quotient_point
      have h_card_fiber_of_each_y : ∀ y ∈ Y_bad,
          Fintype.card ((quotientFiber 𝔽q β (i := i) (steps := steps)
            h_destIdx h_destIdx_le (y := y)) ''
            ↑(Finset.univ : Finset (Fin ((2:ℕ)^steps)))) = 2 ^ steps := by
        intro y hy_in_Y_bad
        have hy_card_fiber_of_y := h_card_fiber_per_quotient_point (a := y) (b := by
          exact Submodule.coe_mem y)
        simp only [coe_univ, Set.image_univ, Fintype.card_ofFinset, hy_card_fiber_of_y]
      rw [Finset.sum_congr rfl h_card_fiber_of_each_y]
      simp only [sum_const, smul_eq_mul, ge_iff_le]
      simp only [Y_bad, d_fw, pairFiberwiseDistance, le_refl]
    · -- Prove that the fibers for distinct quotient points y₁, y₂ are disjoint.
      intro y₁ hy₁ y₂ hy₂ hy_ne
      have h_disjoint := quotientFiber_disjoint (i := i) (steps := steps)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (y₁ := y₁) (y₂ := y₂)
        (hy_ne := hy_ne)
      simp only [Function.onFun, coe_univ]
      exact h_disjoint
  exact h_dist_le_fw_dist_times_fiber_size

omit [DecidableEq 𝔽q] [NeZero ℓ] in
/-- if `d⁽ⁱ⁾(f⁽ⁱ⁾, g⁽ⁱ⁾) < d_{ᵢ₊steps} / 2` (fiberwise distance),
then `d(f⁽ⁱ⁾, g⁽ⁱ⁾) < dᵢ/2` (regular code distance) -/
lemma pairUniqueDecodingClose_of_pairFiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h_fw_dist_lt : PairFiberwiseClose 𝔽q β i steps h_destIdx h_destIdx_le f g) :
    PairUniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (f := f)
      (g := g) := by
  classical
  unfold PairFiberwiseClose at h_fw_dist_lt
  norm_cast at h_fw_dist_lt
  unfold PairUniqueDecodingClose
  set d_fw := pairFiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    steps h_destIdx h_destIdx_le (f := f) (g := g)
  set d_cur := codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
  -- d_cur = 2 ^ (ℓ + 𝓡 - i) - 2 ^ (ℓ - i) + 1
  set d_next := codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := destIdx)
  -- d_next = 2 ^ (ℓ + 𝓡 - (i + steps)) - 2 ^ (ℓ - (i + steps)) + 1
  have h_le : 2 * Δ₀(f, g) ≤ 2 * (d_fw * 2 ^ steps) := by
    apply Nat.mul_le_mul_left
    apply hammingDist_le_pairFiberwiseDistance_mul_pow_two
  -- h_fw_dist_lt : 2 * d_fw < codeDistance 𝔽q β ⟨↑i + steps, ⋯⟩
  have h_2_fw_dist_le : 2 * d_fw ≤ d_next - 1 := by omega
  have h_fiberwise_scaled_le :
    2 * (d_fw * 2 ^ steps) ≤ (d_next * 2 ^ steps - 2 ^ steps) := by
    rw [←mul_assoc]
    conv_rhs =>
      rw (occs := [2]) [←one_mul (2 ^ steps)];
      rw [←Nat.sub_mul (n := d_next) (m := 1) (k := 2 ^ steps)];
    apply Nat.mul_le_mul_right
    exact h_2_fw_dist_le
  have h_scaled_distance_eq : (d_next * 2 ^ steps - 2 ^ steps) = d_cur - 1 := by
    dsimp only [d_next, d_cur]
    rw [codeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by omega),
      codeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by omega)]
    simp only [add_tsub_cancel_right]
    rw [Nat.add_mul, Nat.sub_mul]
    rw [←Nat.pow_add, ←Nat.pow_add]
    have h_exp1 : ℓ + 𝓡 - destIdx + steps = ℓ + 𝓡 - i.val := by omega
    have h_exp2 : ℓ - destIdx + steps = ℓ - i.val := by omega
    rw [h_exp1, h_exp2]
    omega
  have h_le_2 : 2 * (d_fw * 2 ^ steps) ≤ codeDistance 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) - 1:= by
    omega
  apply Nat.lt_of_le_pred (h := by
    simp only [d_cur]
    rw [codeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (h_i := by omega)]
    omega)
  simp only [pred_eq_sub_one]
  exact Nat.le_trans h_le h_le_2

omit [DecidableEq 𝔽q] hF₂ [NeZero 𝓡] in
omit [NeZero ℓ] in
/-- The minimum number of disagreeing fibers is attained by a codeword. -/
lemma exists_fiberwiseClosestCodeword (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    let S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
    let C_i : Set (S_i → L) := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    ∃ (g : S_i → L), g ∈ C_i ∧
      fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps h_destIdx h_destIdx_le (f := f) =
        pairFiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_destIdx h_destIdx_le (f := f) (g := g) := by
  simp only [SetLike.mem_coe]
  set S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
  set C_i := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  -- Let `S` be the set of all possible fiber-wise disagreement sizes.
  let S := (fun (g : C_i) =>
    (fiberwiseDisagreementSet 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le) (f := f) (g := g)).card) '' Set.univ
  -- The code `C_i` (a submodule) is non-empty, so `S` is also non-empty.
  have hS_nonempty : S.Nonempty := by
    refine Set.image_nonempty.mpr ?_
    exact Set.univ_nonempty
  -- For a non-empty set of natural numbers, `sInf` is an element of the set.
  have h_sInf_mem : sInf S ∈ S := Nat.sInf_mem hS_nonempty
  -- By definition, `d_fw = sInf S`.
  -- Since `sInf S` is in the image set `S`, there must be an element `g_subtype` in the domain
  -- (`C_i`) that maps to it. This `g_subtype` is the codeword we're looking for.
  rw [Set.mem_image] at h_sInf_mem
  rcases h_sInf_mem with ⟨g_subtype, _, h_eq⟩
  -- Extract the codeword and its membership proof.
  refine ⟨g_subtype, ?_, ?_⟩
  · -- membership
    exact g_subtype.property
  · -- equality of distances
    -- `fiberwiseDistance` is defined as the infimum of `S`, so it equals `sInf S`
    -- and `h_eq` tells us that this is exactly the distance to `g_subtype`.
    exact id (Eq.symm h_eq)

omit [DecidableEq 𝔽q] [NeZero ℓ] in
/-- Fiberwise closeness implies ordinary Hamming closeness within the decoding radius. -/
theorem uniqueDecodingClose_of_fiberwiseClose (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i.val + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  (h_fw_dist_lt : FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f)) :
  UniqueDecodingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i  f := by
  classical
  unfold FiberwiseClose at h_fw_dist_lt
  unfold UniqueDecodingClose
  -- 2 * Δ₀(f, ↑(code 𝔽q β ⟨↑i, ⋯⟩)) < ↑(codeDistance ℓ 𝓡 ⟨↑i, ⋯⟩)
  set d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_destIdx h_destIdx_le f
  let C_i := (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  let d_H := Δ₀(f, C_i)
  let d_i := codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
  let d_i_plus_steps := codeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx)
  have h_d_i_gt_0 : d_i > 0 := by
    dsimp only [d_i]-- , codeDistance] -- ⊢ 2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1 > 0
    have h_exp_lt : ℓ - i.val < ℓ + 𝓡 - i.val := by
      exact Nat.sub_lt_sub_right (a := ℓ) (b := ℓ + 𝓡) (c := i.val) (by omega) (by
        apply Nat.lt_add_of_pos_right; exact pos_of_neZero 𝓡)
    have h_pow_lt : 2 ^ (ℓ - i.val) < 2 ^ (ℓ + 𝓡 - i.val) := by
      exact Nat.pow_lt_pow_right (by norm_num) h_exp_lt
    rw [codeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega)]
    omega
  have h_C_i_nonempty : Nonempty C_i := by
    simp only [nonempty_subtype, C_i]
    exact Submodule.nonempty (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
  -- 1. Relate Hamming distance `d_H` to fiber-wise distance `d_fw`.
  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw
    = (fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g').card := by
    apply exists_fiberwiseClosestCodeword
  have h_UDR_close_f_g' := pairUniqueDecodingClose_of_pairFiberwiseClose 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
    h_destIdx h_destIdx_le (f := f) (g := g') (h_fw_dist_lt := by
      dsimp only [PairFiberwiseClose, pairFiberwiseDistance]; norm_cast;
      rw [←h_g'_min_card];
      exact (by norm_cast at h_fw_dist_lt)
    )
  calc
    2 * Δ₀(f, C_i) ≤ 2 * Δ₀(f, g') := by
      rw [ENat.mul_le_mul_left_iff (ha := by
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true])
        (h_top := by simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true])
      ]
      apply Code.distFromCode_le_dist_to_mem (C := C_i) (u := f) (v := g') (hv := h_g'_mem)
    _ < _ := by norm_cast -- use result from h_UDR_close_f_g'

omit [DecidableEq 𝔽q] [NeZero ℓ] in
/-- This expands `exists_fiberwiseClosestCodeword` to the case `f` is fiberwise-close to `C_i`. -/
lemma exists_unique_codeword_of_fiberwiseClose (i : Fin r) {destIdx : Fin r}
    (steps : ℕ) (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (h_fw_close : FiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) (steps := steps) h_destIdx h_destIdx_le (f := f)) :
    let S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
    let C_i : Set (S_i → L) := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
    ∃! (g : S_i → L), (g ∈ C_i) ∧
      (fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) steps h_destIdx h_destIdx_le (f := f) =
        pairFiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := i) steps h_destIdx h_destIdx_le (f := f) (g := g)) ∧
      (g = uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (h_i := by omega) f
        (h_within_radius := uniqueDecodingClose_of_fiberwiseClose 𝔽q β i steps h_destIdx
          h_destIdx_le f
        h_fw_close)) := by
  classical
  set d_fw := fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
    steps h_destIdx h_destIdx_le f
  set S_i := sDomain 𝔽q β h_ℓ_add_R_rate i
  set S_i_next := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  set C_i := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i
  obtain ⟨g, h_g_mem, h_g_min_card⟩ : ∃ g ∈ C_i, d_fw
    = (fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g).card := by
    apply exists_fiberwiseClosestCodeword
  set C_i_next := code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  have h_neZero_dist_C_i_next : NeZero (‖(C_i_next : Set (S_i_next → L))‖₀) := {
    out := by
      unfold C_i_next
      simp_rw [codeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := destIdx) (h_i := by omega)]
      omega
  }
  have h_neZero_dist_C_i : NeZero (‖(C_i : Set (S_i → L))‖₀) := {
    out := by
      unfold C_i
      simp_rw [codeDistance_eq 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i) (h_i := by omega)]
      omega
  }
  use g
  have h_f_g_UDR_close : Δ₀(f, g) ≤ Code.uniqueDecodingRadius (F := L)
    (ι := S_i) (C := C_i) := by -- This relies on `h_fw_close`
    unfold FiberwiseClose at h_fw_close
    norm_cast at h_fw_close
    rw [←Code.UDRClose_iff_two_mul_proximity_lt_d_UDR] at h_fw_close
    unfold d_fw at h_g_min_card
    rw [h_g_min_card] at h_fw_close
    rw [Code.uniqueDecodingRadius,
      ←Nat.two_mul_lt_iff_le_half_of_sub_one
        (a := #(fiberwiseDisagreementSet 𝔽q β i steps h_destIdx h_destIdx_le f g))
        (h_b_pos := by
          exact Nat.pos_of_neZero (n := ‖(C_i_next : Set (S_i_next → L))‖₀))] at h_fw_close
    -- h_fw_close : 2 * #(fiberwiseDisagreementSet ...) < ‖↑(code 𝔽q β ...)‖₀
    rw [Code.uniqueDecodingRadius,
      ←Nat.two_mul_lt_iff_le_half_of_sub_one (a := Δ₀(f,g))
        (h_b_pos := by exact Nat.pos_of_neZero (n := ‖(C_i : Set (S_i → L))‖₀))]
    -- 2 * Δ₀(f, g) < ‖↑(C_i)‖₀
    let res := pairUniqueDecodingClose_of_pairFiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i) steps h_destIdx h_destIdx_le (f := f) (g := g) (h_fw_dist_lt := by
      unfold PairFiberwiseClose pairFiberwiseDistance
      norm_cast
    )
    exact res
  let h_f_UDR_close := uniqueDecodingClose_of_fiberwiseClose 𝔽q β i steps h_destIdx h_destIdx_le
    f h_fw_close
  have h_g_eq_UDRCodeword : g = uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i (h_i := by omega) f h_f_UDR_close := by
    apply Code.eq_of_le_uniqueDecodingRadius (C := C_i) (u := f) (v := g)
      (w := uniqueDecodingCodeword 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i (h_i := by omega) f
        h_f_UDR_close)
      (hv := h_g_mem) (huv := by exact h_f_g_UDR_close)
      (hw := by apply uniqueDecodingCodeword_mem_code (i := i) (f := f) (h_within_radius :=
        h_f_UDR_close))
      (huw := by
        apply dist_to_uniqueDecodingCodeword_le_uniqueDecodingRadius (i := i) (f := f)
          (h_within_radius := h_f_UDR_close)
      )
  simp only
  constructor
  · constructor
    · exact h_g_mem
    · constructor
      · exact h_g_min_card
      · -- ⊢ g = uniqueDecodingCodeword 𝔽q β ⟨↑i, ⋯⟩ f ⋯
        exact h_g_eq_UDRCodeword
  · -- trivial contrapositive case
    intro y hy_mem_C_i
    rw [h_g_eq_UDRCodeword]
    rw [hy_mem_C_i.2.2]

omit [DecidableEq 𝔽q] [NeZero ℓ] in
/-- One folding step maps a codeword of the `i`-th code to a codeword of the `(i+1)`-th code,
because a fold advances the evaluation polynomial (`fold_advances_evaluation_poly`). -/
lemma fold_mem_code (i : Fin r) {destIdx : Fin r}
    (h_destIdx : destIdx = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (f : (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) (r_chal : L) :
    (fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) h_destIdx h_destIdx_le
      (f := f) (r_chal := r_chal)) ∈
    (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
  classical
  -- 1. Unwrap the code definition to get the polynomial P
  -- code is ReedSolomon, so f comes from some P with deg < 2^(ℓ-i)
  set C_cur := ((code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) :
    Set ((sDomain 𝔽q β h_ℓ_add_R_rate) i → L)) with h_C_cur
  have h_f_mem : f.val ∈ C_cur := by
    unfold C_cur
    simp only [Subtype.coe_prop]
  simp only [code, ReedSolomon.code, C_cur] at h_f_mem
  rcases h_f_mem with ⟨P, hP_deg, hP_eval⟩ -- the poly that generates `f` on `S^(i)`
  let iNovel_coeffs : Fin (2^(ℓ - i)) → L :=
    getINovelCoeffs 𝔽q β h_ℓ_add_R_rate (i := i) (h_i := by omega) (P := P)
  simp only [evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk] at hP_eval
  simp only [SetLike.mem_coe, mem_degreeLT, cast_pow, cast_ofNat] at hP_deg
  simp only [code, ReedSolomon.code, Submodule.mem_map]
  set new_coeffs := fun j : Fin (2^(ℓ - destIdx)) =>
  (1 - r_chal) * (iNovel_coeffs ⟨j.val * 2, by
    rw [←Nat.add_zero (j.val * 2)]
    apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - destIdx)
      (i := 0) (by omega) (by omega)
  ⟩) +
  r_chal * (iNovel_coeffs ⟨j.val * 2 + 1, by
    apply mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - destIdx)
      (i := 1) (by omega) (by omega)
  ⟩)
  set P_i_plus_1 :=
    intermediateEvaluationPoly 𝔽q β h_ℓ_add_R_rate (i := destIdx) (h_i := by omega) new_coeffs
  use P_i_plus_1
  constructor
  · -- ⊢ P_i_plus_1 ∈ L[X]_(2 ^ (ℓ - (↑i + 1)))
    apply Polynomial.mem_degreeLT.mpr
    unfold P_i_plus_1
    apply degree_intermediateEvaluationPoly_lt
  · -- ⊢ (evalOnPoints ... P_i_plus_1) = fold 𝔽q β ⟨↑i, ⋯⟩ h_i_succ_lt (↑f) r_chal
    let fold_advances_evaluation_poly_res := fold_advances_evaluation_poly 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (coeffs := iNovel_coeffs) (r_chal := r_chal)
    simp only at fold_advances_evaluation_poly_res
    funext (y : (sDomain 𝔽q β h_ℓ_add_R_rate) destIdx)
    dsimp only [evalOnPoints, Embedding.coeFn_mk, LinearMap.coe_mk, AddHom.coe_mk]
    unfold polyToOracleFunc at fold_advances_evaluation_poly_res
    let lhs_eq := congrFun fold_advances_evaluation_poly_res y
    dsimp only [P_i_plus_1]
    conv_lhs => erw [←lhs_eq]
    congr 1
    funext (x : (sDomain 𝔽q β h_ℓ_add_R_rate) i)
    unfold intermediateEvaluationPoly iNovel_coeffs
    let res := intermediateEvaluationPoly_from_inovel_coeffs_eq_self 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (h_i := by omega) (P := P) (hP_deg := hP_deg)
    unfold intermediateEvaluationPoly at res
    rw [res]
    exact (congrFun hP_eval x)

omit [DecidableEq 𝔽q] [NeZero ℓ] in
/-- Iterated folding sends a codeword to a codeword of the destination code. -/
lemma iteratedFold_mem_code (i : Fin r) {destIdx : Fin r} (steps : ℕ)
    (h_destIdx : destIdx = i + steps) (h_destIdx_le : destIdx ≤ ℓ)
    (f : (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i))
    (r_challenges : Fin steps → L) :
    (iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := steps)
      h_destIdx h_destIdx_le (f := f) (r_challenges := r_challenges)) ∈
    (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) := by
  classical
  revert destIdx h_destIdx h_destIdx_le
  induction steps generalizing i with
  | zero =>
    intro destIdx h_destIdx h_destIdx_le
    have h_i_eq_destIdx : i = destIdx := by omega
    subst h_i_eq_destIdx
    -- Base case: 0 steps. iteratedFold is identity. Code is the same.
    simp only [Fin.eta, iteratedFold, reduceAdd, Fin.val_castSucc, Fin.val_succ, id_eq,
      Fin.reduceLast, Fin.coe_ofNat_eq_mod, reduceMod, Nat.add_zero, Subtype.coe_eta,
      Fin.dfoldl_zero, SetLike.coe_mem]
  | succ k ih =>
    intro destIdx h_destIdx h_destIdx_le
    let midIdx : Fin r := ⟨i + k, by omega⟩
    have h_midIdx : midIdx = i + k := by rfl
    -- 1. Perform k steps first
    let f_k := iteratedFold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i)
      (steps := k) (destIdx := midIdx) (h_destIdx := h_midIdx) (h_destIdx_le := by omega)
      (f := f) (r_challenges := Fin.init r_challenges)
    -- 2. Apply IH: f_k is in C^{(i+k)}
    have h_fk_mem : f_k ∈ code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) midIdx := by
      exact ih (i := i) (r_challenges := Fin.init r_challenges) (destIdx := midIdx)
        (h_destIdx := h_midIdx) (h_destIdx_le := by omega) (f := f)
    set f_k_code_word : (code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) midIdx) :=
      ⟨f_k, h_fk_mem⟩
    -- 3. Perform the (k+1)-th fold on f_k
    rw [iteratedFold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) (steps := k)
      (midIdx := midIdx) (destIdx := destIdx) (h_midIdx := h_midIdx) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f := f) (r_challenges := r_challenges)]
    -- 4. Apply the Single Step Lemma
    let res := fold_mem_code (i := midIdx) (destIdx := destIdx)
      (h_destIdx := by omega) (h_destIdx_le := by omega) (f := f_k_code_word)
      (r_chal := r_challenges (Fin.last k))
    exact res

end SoundnessTools

end Binius.BinaryBasefold
