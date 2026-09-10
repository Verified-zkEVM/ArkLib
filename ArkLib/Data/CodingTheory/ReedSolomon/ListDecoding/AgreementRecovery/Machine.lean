/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.GCDSplit

/-!
# Agreement splitting without extracting parameter roots

The common recovery procedure follows roots of a squarefree modulus through their agreement
equations. For each indexed residual `e`, `gcd(h,e)` contains the agreeing roots and its exact
complement contains the nonagreeing roots. The runtime stores these factors, not their roots.

`split` traverses that binary split tree depth first. A branch stops after recording `k`
agreements; a subsequent interpolation step can then recover its unique message from those
received positions. Constant factors represent no roots and are discarded. The remaining
equation list decreases at each recursive call, independently of polynomial degrees.

Positions are recorded in reverse traversal order. This order does not affect interpolation,
but retaining their indices rather than just their values is essential: repeated received
values do not constitute repeated positions.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery

open CompPoly

variable {E index : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- A parameter factor and the received positions at which all of its roots agree. -/
structure Block (E index : Type*) [Field E] [BEq E] [LawfulBEq E] where
  /-- A divisor of the original representation modulus. -/
  factor : CPolynomial E
  /-- Distinct processed indices, stored in reverse traversal order. -/
  positions : List index

/-- Split by the remaining equations, stopping each nonconstant factor after `k` recorded
agreements. The two children use the same remaining equations and preserve all earlier matches. -/
def split (k : ℕ) : List (index × CPolynomial E) → Block E index → List (Block E index)
  | equations, block =>
    if block.factor.natDegree = 0 then []
    else if k ≤ block.positions.length then [block]
    else match equations with
      | [] => []
      | (i, e) :: rest =>
        split k rest ⟨CPolynomial.gcdFactor block.factor e, i :: block.positions⟩ ++
          split k rest ⟨CPolynomial.gcdComplement block.factor e, block.positions⟩

/-- Begin with the whole representation modulus and no confirmed positions. -/
def run (k : ℕ) (equations : List (index × CPolynomial E))
    (modulus : CPolynomial E) : List (Block E index) :=
  split k equations ⟨modulus, []⟩

/-- Every returned block has exactly the requested number of agreements, provided the caller
starts below that threshold. Each successful split records only one new position. -/
theorem split_positions_length (k : ℕ) (equations : List (index × CPolynomial E))
    (block out : Block E index) (hstart : block.positions.length ≤ k)
    (hout : out ∈ split k equations block) : out.positions.length = k := by
  induction equations generalizing block with
  | nil =>
      simp only [split] at hout
      split_ifs at hout with hzero hstop
      · simp at hout
      · simp only [List.mem_singleton] at hout
        subst out
        omega
      · simp at hout
  | cons row rest ih =>
      rcases row with ⟨i, e⟩
      simp only [split] at hout
      split_ifs at hout with hzero hstop
      · simp at hout
      · simp only [List.mem_singleton] at hout
        subst out
        omega
      · rcases List.mem_append.mp hout with hgood | hbad
        · exact ih _ (by simp; omega) hgood
        · exact ih ⟨CPolynomial.gcdComplement block.factor e, block.positions⟩ hstart hbad

/-- Every result has a nonconstant parameter factor; an empty represented root set cannot
trigger an interpolation attempt. -/
theorem split_factor_natDegree_pos (k : ℕ) (equations : List (index × CPolynomial E))
    (block out : Block E index) (hout : out ∈ split k equations block) :
    0 < out.factor.natDegree := by
  induction equations generalizing block with
  | nil =>
      simp only [split] at hout
      split_ifs at hout with hzero hstop
      · simp at hout
      · simp only [List.mem_singleton] at hout
        subst out
        omega
      · simp at hout
  | cons row rest ih =>
      rcases row with ⟨i, e⟩
      simp only [split] at hout
      split_ifs at hout with hzero hstop
      · simp at hout
      · simp only [List.mem_singleton] at hout
        subst out
        omega
      · rcases List.mem_append.mp hout with hgood | hbad
        · exact ih _ hgood
        · exact ih _ hbad

/-- Recorded indices are drawn without reordering from the reverse input order, followed by
the already recorded prefix. This lets the caller derive distinctness from its indexed rows. -/
theorem split_positions_sublist (k : ℕ) (equations : List (index × CPolynomial E))
    (block out : Block E index) (hout : out ∈ split k equations block) :
    out.positions.Sublist ((equations.map Prod.fst).reverse ++ block.positions) := by
  induction equations generalizing block with
  | nil =>
      simp only [split] at hout
      split_ifs at hout with hzero hstop
      · simp at hout
      · simp only [List.mem_singleton] at hout
        subst out
        simp
      · simp at hout
  | cons row rest ih =>
      rcases row with ⟨i, e⟩
      simp only [split] at hout
      split_ifs at hout with hzero hstop
      · simp at hout
      · simp only [List.mem_singleton] at hout
        subst out
        exact List.sublist_append_right _ _
      · rcases List.mem_append.mp hout with hgood | hbad
        · simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
            List.singleton_append] using ih _ hgood
        · have h := ih _ hbad
          apply h.trans
          simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
          exact (List.sublist_cons_self i block.positions).append_left _

/-- The initial call returns precisely `k` distinct received indices per interpolation attempt. -/
theorem run_positions (k : ℕ) (equations : List (index × CPolynomial E))
    (modulus : CPolynomial E) (hindices : (equations.map Prod.fst).Nodup)
    (out : Block E index) (hout : out ∈ run k equations modulus) :
    out.positions.length = k ∧ out.positions.Nodup := by
  constructor
  · exact split_positions_length k equations _ out (by simp) hout
  · apply (split_positions_sublist k equations _ out hout).nodup
    simpa using hindices

end ReedSolomon.ListDecoding.AgreementRecovery
