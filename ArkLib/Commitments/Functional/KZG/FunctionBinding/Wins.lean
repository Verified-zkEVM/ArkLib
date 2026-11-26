/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Commitments.Functional.KZG.FunctionBinding.Reduction

/-!
# KZG function binding: the reduction's answer wins

This file proves that `KZG.FunctionBinding.functionBindingReduction` wins the ARSDH predicate
whenever its input is a winning function-binding output: every opening is accepted under the
honest keys for `τ`, and no coefficient vector of length `n + 1` fits all openings. The
statement is pointwise in `τ`; the game-level reduction is built on top of it separately.

## Main statements

* `KZG.FunctionBinding.conflictAnswer_wins`, `KZG.FunctionBinding.trapdoorAnswer_wins`,
  `KZG.FunctionBinding.genericAnswer_wins`: the three cases.
* `KZG.FunctionBinding.functionBindingReduction_wins`: the combined statement.
-/

@[expose] public section

open CompPoly Finset

namespace KZG

namespace FunctionBinding

section Lists

variable {α : Type*}

/-- A nodup list keeps at least `l.length - #B` elements under a filter that only drops
elements of `B`. -/
theorem length_le_length_filter_add (l : List α) (hl : l.Nodup) (p : α → Bool) (B : Finset α)
    (hB : ∀ s ∈ l, p s = false → s ∈ B) : l.length ≤ (l.filter p).length + #B := by
  classical
  rw [List.length_eq_length_filter_add p]
  refine Nat.add_le_add_left ?_ _
  have hnd : (l.filter fun s => !p s).Nodup := hl.filter _
  rw [← List.toFinset_card_of_nodup hnd]
  refine Finset.card_le_card fun s hs => ?_
  simp only [List.mem_toFinset, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hs
  exact hB s hs.1 hs.2

end Lists

variable {F : Type} [Field F] [DecidableEq F]
variable {G₁ G₂ Gₜ : Type}
variable {n : ℕ}

section Polynomials

omit [DecidableEq F] in
/-- The ARSDH polynomial `∏ s ∈ S, (X - s)` evaluates to `∏ s ∈ S, (τ - s)`. -/
theorem eval_prod_X_sub_C (S : Finset F) (τ : F) :
    (∏ s ∈ S, (Polynomial.X - Polynomial.C s)).eval τ = ∏ s ∈ S, (τ - s) := by
  simp [Polynomial.eval_prod]

/-- The computable vanishing polynomial of a nodup list is Mathlib's nodal polynomial. -/
theorem toPoly_vanishing {P : List F} (hP : P.Nodup) :
    (vanishing P).toPoly = Lagrange.nodal P.toFinset id := by
  rw [Lagrange.nodal_eq, List.prod_toFinset _ hP, vanishing,
    ← CPolynomial.toPolyRingHom_apply, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  simp [CPolynomial.toPoly_sub, CPolynomial.X_toPoly, CPolynomial.C_toPoly]

omit [DecidableEq F] in
/-- A polynomial of degree below `k + 1` has degree at most `k`. -/
theorem natDegree_le_of_degree_lt {p : Polynomial F} {k : ℕ} (h : p.degree < ↑(k + 1)) :
    p.natDegree ≤ k := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le h (by exact_mod_cast hN))

/-- The computable interpolant of `n + 1` openings is Mathlib's Lagrange interpolant. -/
theorem toPoly_interpolant (node : Fin (n + 1) → Opening F G₁) :
    (interpolant node).toPoly =
      Lagrange.interpolate univ (fun i => (node i).1) (fun i => (node i).2.1) :=
  CPolynomial.CLagrange.cinterpolate_eq_interpolate

/-- The interpolant of `n + 1` openings with distinct points has degree at most `n`. -/
theorem natDegree_toPoly_interpolant_le (node : Fin (n + 1) → Opening F G₁)
    (hinj : Function.Injective fun i => (node i).1) :
    (interpolant node).toPoly.natDegree ≤ n := by
  refine natDegree_le_of_degree_lt ?_
  rw [toPoly_interpolant]
  simpa using Lagrange.degree_interpolate_lt (s := univ) (fun i => (node i).2.1)
    hinj.injOn

/-- The interpolant of openings with distinct points passes through each of them. -/
theorem eval_toPoly_interpolant (node : Fin (n + 1) → Opening F G₁)
    (hinj : Function.Injective fun i => (node i).1) (i : Fin (n + 1)) :
    (interpolant node).toPoly.eval (node i).1 = (node i).2.1 := by
  rw [toPoly_interpolant]
  exact Lagrange.eval_interpolate_at_node _ hinj.injOn (mem_univ i)

/-- If a polynomial of degree at most `n` passes through all openings, a coefficient vector
fits them. -/
theorem exists_fit_of_eval {p : Polynomial F} (hp : p.natDegree ≤ n)
    {os : List (Opening F G₁)} (h : ∀ o ∈ os, p.eval o.1 = o.2.1) :
    ∃ c : Fin (n + 1) → F, ∀ o ∈ os, evaluate c o.1 = o.2.1 :=
  ⟨fun i => p.coeff i, fun o ho => by rw [evaluate_eq_eval_toPoly, toPoly_ofFn_coeff hp, h o ho]⟩

/-- If the points of a set `A` of at most `n + 1` openings are distinct, the openings agree on
each point, and every opening shares its point with some element of `A`, then a coefficient
vector fits all openings: the Lagrange interpolant through `A`. -/
theorem exists_fit_of_cover {os : List (Opening F G₁)}
    (hnc : ∀ o ∈ os, ∀ o' ∈ os, o.1 = o'.1 → o.2.1 = o'.2.1) (A : Finset (Opening F G₁))
    (hA : #A ≤ n + 1) (hinj : Set.InjOn Prod.fst (A : Set (Opening F G₁)))
    (hsub : ∀ a ∈ A, a ∈ os) (hcover : ∀ o ∈ os, ∃ a ∈ A, a.1 = o.1) :
    ∃ c : Fin (n + 1) → F, ∀ o ∈ os, evaluate c o.1 = o.2.1 := by
  classical
  refine exists_fit_of_eval (p := Lagrange.interpolate A Prod.fst fun a => a.2.1) ?_ ?_
  · refine natDegree_le_of_degree_lt ((Lagrange.degree_interpolate_lt _ hinj).trans_le ?_)
    exact_mod_cast hA
  · intro o ho
    obtain ⟨a, ha, hao⟩ := hcover o ho
    rw [← hao, Lagrange.eval_interpolate_at_node _ hinj ha]
    exact hnc a (hsub a ha) o ho hao

/-- The interpolant of `n + 1` openings with distinct points has degree below `n + 1`. -/
theorem degree_toPoly_interpolant_lt (node : Fin (n + 1) → Opening F G₁)
    (hinj : Function.Injective fun i => (node i).1) :
    (interpolant node).toPoly.degree < ↑(n + 1) := by
  rw [toPoly_interpolant]
  simpa using Lagrange.degree_interpolate_lt (s := univ) (fun i => (node i).2.1) hinj.injOn

omit [DecidableEq F] in
/-- The computable `weight` is Mathlib's nodal weight. -/
theorem weight_eq_nodalWeight (v : Fin (n + 1) → F) (i : Fin (n + 1)) :
    weight v i = Lagrange.nodalWeight univ v i :=
  rfl

end Polynomials

section Search

omit [Field F] in
/-- A conflict found by `findConflict` consists of two openings at one point with different
values. -/
theorem findConflict_eq_some {os : List (Opening F G₁)} {o o' : Opening F G₁}
    (h : findConflict os = some (o, o')) :
    o ∈ os ∧ o' ∈ os ∧ o'.1 = o.1 ∧ o'.2.1 ≠ o.2.1 := by
  obtain ⟨a, ha, hfa⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨b, hb, hab⟩ := Option.map_eq_some_iff.mp hfa
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
  have hp := List.find?_some hb
  simp only [decide_eq_true_eq] at hp
  exact ⟨ha, List.mem_of_find?_eq_some hb, hp⟩

omit [Field F] in
/-- Without a conflict, openings at the same point have the same value. -/
theorem findConflict_eq_none {os : List (Opening F G₁)} (h : findConflict os = none) :
    ∀ o ∈ os, ∀ o' ∈ os, o.1 = o'.1 → o.2.1 = o'.2.1 := by
  intro o ho o' ho' hq
  rw [findConflict, List.findSome?_eq_none_iff] at h
  have := h o ho
  rw [Option.map_eq_none_iff, List.find?_eq_none] at this
  have h' := this o' ho'
  simp only [decide_eq_true_eq, not_and, not_not] at h'
  exact (h' hq.symm).symm

end Search

omit [Field F] in
/-- `trapdoorPoints` lists `n + 1` distinct points other than `τ`. -/
theorem trapdoorPoints_spec (τ : F) (pts : Fin (n + 2) ↪ F) :
    (trapdoorPoints pts τ).length = n + 1 ∧ (trapdoorPoints pts τ).Nodup ∧
      ∀ s ∈ trapdoorPoints pts τ, s ≠ τ := by
  have hnd0 : (List.ofFn pts).Nodup := List.nodup_ofFn.mpr pts.injective
  have hlen := length_le_length_filter_add (List.ofFn pts) hnd0 (fun s => s != τ) {τ} (by
    intro s _ hs
    simpa using hs)
  simp only [List.length_ofFn, card_singleton] at hlen
  refine ⟨?_, (hnd0.filter _).sublist (List.take_sublist _ _), fun s hs => ?_⟩
  · rw [trapdoorPoints, List.length_take]
    omega
  · simpa using (List.mem_filter.mp (List.mem_of_mem_take hs)).2

variable [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ]
  [Module F Gₜ]

section Points

variable [DecidableEq G₂]

omit [DecidableEq F] in
/-- Under `e g₁ g₂ ≠ 0`, the honest verifier key detects exactly the trapdoor. -/
theorem isTrapdoor_verifierKey {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (he : e g₁ g₂ ≠ 0) (τ s : F) : isTrapdoor (verifierKey g₂ τ) s = true ↔ s = τ := by
  rw [isTrapdoor, decide_eq_true_iff]
  exact (smul_right_injective_of_pairing_ne_zero he).eq_iff

/-- `conflictPoints` lists `n` distinct points other than `q` and the trapdoor. -/
theorem conflictPoints_spec {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (he : e g₁ g₂ ≠ 0) (τ : F) (pts : Fin (n + 2) ↪ F) (q : F) :
    (conflictPoints pts (verifierKey g₂ τ) q).length = n ∧
      (conflictPoints pts (verifierKey g₂ τ) q).Nodup ∧
      ∀ s ∈ conflictPoints pts (verifierKey g₂ τ) q, s ≠ q ∧ s ≠ τ := by
  have hnd0 : (List.ofFn pts).Nodup := List.nodup_ofFn.mpr pts.injective
  have hlen := length_le_length_filter_add (List.ofFn pts) hnd0
    (fun s => decide (s ≠ q) && !isTrapdoor (verifierKey g₂ τ) s) {q, τ} (by
      intro s _ hs
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_not,
        Bool.not_eq_eq_eq_not, Bool.not_false] at hs
      rcases hs with hs | hs
      · simp [hs]
      · simp [(isTrapdoor_verifierKey he τ s).mp hs])
  have hcard : #({q, τ} : Finset F) ≤ 2 := Finset.card_le_two
  simp only [List.length_ofFn] at hlen
  refine ⟨?_, (hnd0.filter _).sublist (List.take_sublist _ _), fun s hs => ?_⟩
  · rw [conflictPoints, List.length_take]
    omega
  · have hs' := (List.mem_filter.mp (List.mem_of_mem_take hs)).2
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true] at hs'
    refine ⟨hs'.1, fun hsτ => ?_⟩
    have := (isTrapdoor_verifierKey he τ s).mpr hsτ
    rw [hs'.2] at this
    exact Bool.false_ne_true this

end Points

section Honest

variable {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}

omit [DecidableEq F] in
/-- An accepted opening off the trapdoor is `((τ - q)⁻¹ * (c - r)) • g₁` when `cm = c • g₁`. -/
theorem opening_proof_eq [DecidableEq Gₜ] (he : e g₁ g₂ ≠ 0)
    (hg₁ : Function.Surjective (· • g₁ : F → G₁)) {τ c q r : F} {π : G₁}
    (h : verifyOpening e g₁ (verifierKey g₂ τ) (c • g₁) q r π = true) (hq : q ≠ τ) :
    π = ((τ - q)⁻¹ * (c - r)) • g₁ := by
  have hτq : τ - q ≠ 0 := sub_ne_zero.mpr hq.symm
  have heq := verifyOpening_eq he hg₁ h
  rw [← sub_smul] at heq
  rw [mul_smul, heq, smul_smul, inv_mul_cancel₀ hτq, one_smul]

/-- **Conflict case.** Given `h = (τ - q)⁻¹ • g₁` with `τ ≠ q`, the conflict answer wins. -/
theorem conflictAnswer_wins [DecidableEq G₂] (he : e g₁ g₂ ≠ 0) (τ : F) (pts : Fin (n + 2) ↪ F)
    {q : F} (hq : τ - q ≠ 0) :
    arsdhWins τ n (conflictAnswer pts (committerKey g₁ τ n) (verifierKey g₂ τ) q
      ((τ - q)⁻¹ • g₁)) := by
  have hg₁0 := ne_zero_left_of_pairing_ne_zero he
  obtain ⟨hlen, hnd, hmem⟩ := conflictPoints_spec he τ pts q
  unfold arsdhWins conflictAnswer
  dsimp only
  generalize conflictPoints pts (verifierKey g₂ τ) q = P at hlen hnd hmem ⊢
  have hqP : q ∉ P.toFinset := fun h => (hmem q (List.mem_toFinset.mp h)).1 rfl
  have hW : ∏ s ∈ P.toFinset, (τ - s) ≠ 0 :=
    prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr (hmem s (List.mem_toFinset.mp hs)).2.symm
  have hvan : (vanishing P).toPoly.natDegree ≤ n := by
    rw [toPoly_vanishing hnd, Lagrange.natDegree_nodal, List.toFinset_card_of_nodup hnd, hlen]
  have hcommit : commit (committerKey g₁ τ n) (fun i => (vanishing P).coeff i) =
      (∏ s ∈ P.toFinset, (τ - s)) • g₁ := by
    rw [commit_committerKey_of_coeff g₁ τ hvan _ fun _ => CPolynomial.coeff_toPoly _ _,
      toPoly_vanishing hnd, Lagrange.eval_nodal]
    rfl
  rw [eval_prod_X_sub_C, prod_insert hqP, hcommit]
  refine ⟨?_, mul_ne_zero hq hW, smul_ne_zero hW hg₁0, ?_⟩
  · rw [card_insert_of_notMem hqP, List.toFinset_card_of_nodup hnd, hlen]
  · rw [smul_smul, mul_inv, mul_assoc, inv_mul_cancel₀ hW, mul_one]

/-- **Trapdoor case.** Given the trapdoor, the trapdoor answer wins. -/
theorem trapdoorAnswer_wins (he : e g₁ g₂ ≠ 0) (τ : F) (pts : Fin (n + 2) ↪ F) :
    arsdhWins τ n (trapdoorAnswer pts (committerKey g₁ τ n) τ) := by
  have hg₁0 := ne_zero_left_of_pairing_ne_zero he
  obtain ⟨hlen, hnd, hmem⟩ := trapdoorPoints_spec τ pts
  have hck : committerKey g₁ τ n 0 = g₁ := by
    simp [committerKey]
  unfold arsdhWins trapdoorAnswer
  dsimp only
  generalize trapdoorPoints pts τ = S at hlen hnd hmem ⊢
  have hW : ∏ s ∈ S.toFinset, (τ - s) ≠ 0 :=
    prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr (hmem s (List.mem_toFinset.mp hs)).symm
  rw [eval_prod_X_sub_C, hck]
  exact ⟨by rw [List.toFinset_card_of_nodup hnd, hlen], hW, hg₁0, rfl⟩

end Honest

section Generic

variable {g₁ : G₁}

/-- The first component of `interpolationAnswer` is the set of node points. -/
theorem interpolationAnswer_fst (ck : Fin (n + 1) → G₁) (cm : G₁)
    (node : Fin (n + 1) → Opening F G₁) :
    (interpolationAnswer ck cm node).1 = univ.image fun i => (node i).1 :=
  rfl

/-- Under honest keys and `cm = c • g₁`, the answer's `h₁` is `(c - I(τ)) • g₁`. -/
theorem interpolationAnswer_h₁ (g₁ : G₁) (τ c : F) (node : Fin (n + 1) → Opening F G₁)
    (hinj : Function.Injective fun i => (node i).1) :
    (interpolationAnswer (committerKey g₁ τ n) (c • g₁) node).2.1 =
      (c - (interpolant node).toPoly.eval τ) • g₁ := by
  simp only [interpolationAnswer]
  rw [commit_committerKey_of_coeff g₁ τ (natDegree_toPoly_interpolant_le node hinj) _
    fun _ => CPolynomial.coeff_toPoly _ _, sub_smul]

/-- If each node's proof is `((τ - qᵢ)⁻¹ * (c - rᵢ)) • g₁`, the answer's `h₂` is
`(Z(τ)⁻¹ * (c - I(τ))) • g₁`, by the partial-fraction identity. -/
theorem interpolationAnswer_h₂ (ck : Fin (n + 1) → G₁) (cm : G₁) (τ c : F)
    (node : Fin (n + 1) → Opening F G₁) (hinj : Function.Injective fun i => (node i).1)
    (hτ : ∀ i, (node i).1 ≠ τ)
    (hπ : ∀ i, (node i).2.2 = ((τ - (node i).1)⁻¹ * (c - (node i).2.1)) • g₁) :
    (interpolationAnswer ck cm node).2.2 =
      ((∏ i, (τ - (node i).1))⁻¹ * (c - (interpolant node).toPoly.eval τ)) • g₁ := by
  have key := Lagrange.eval_nodal_inv_mul_sub_eval_interpolate (s := univ)
    (v := fun i => (node i).1) (fun i => (node i).2.1) hinj.injOn univ_nonempty
    (x := τ) (fun i _ => (hτ i).symm) c
  rw [Lagrange.eval_nodal, ← toPoly_interpolant] at key
  simp only [interpolationAnswer]
  rw [key, sum_smul]
  refine sum_congr rfl fun i _ => ?_
  rw [hπ i, smul_smul, weight_eq_nodalWeight, mul_assoc]

/-- **Interpolation case, one node set.** If the commitment's value `c` differs from the
interpolant's value at `τ`, the interpolation answer wins. -/
theorem interpolationAnswer_wins (hg₁ : g₁ ≠ 0) (τ c : F) (node : Fin (n + 1) → Opening F G₁)
    (hinj : Function.Injective fun i => (node i).1) (hτ : ∀ i, (node i).1 ≠ τ)
    (hπ : ∀ i, (node i).2.2 = ((τ - (node i).1)⁻¹ * (c - (node i).2.1)) • g₁)
    (hI : c ≠ (interpolant node).toPoly.eval τ) :
    arsdhWins τ n (interpolationAnswer (committerKey g₁ τ n) (c • g₁) node) := by
  have hZ : ∏ i, (τ - (node i).1) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hτ i).symm
  unfold arsdhWins
  rw [eval_prod_X_sub_C, interpolationAnswer_fst, prod_image fun i _ j _ h => hinj h,
    interpolationAnswer_h₁ g₁ τ c node hinj, interpolationAnswer_h₂ _ _ τ c node hinj hτ hπ,
    card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  exact ⟨rfl, hZ, smul_ne_zero (sub_ne_zero.mpr hI) hg₁, mul_smul _ _ _⟩

/-- **Interpolation case, both node sets.** Let `x` be an opening off the interpolant of the
nodes. If the nodes give `h₁ = 0`, the nodes with the first one replaced by `x` give a win. -/
theorem interpolationChoice_wins [DecidableEq G₁] (hg₁ : g₁ ≠ 0) (τ c : F)
    {os : List (Opening F G₁)}
    (hnc : ∀ o ∈ os, ∀ o' ∈ os, o.1 = o'.1 → o.2.1 = o'.2.1) (hτ : ∀ o ∈ os, o.1 ≠ τ)
    (hπ : ∀ o ∈ os, o.2.2 = ((τ - o.1)⁻¹ * (c - o.2.1)) • g₁)
    (node : Fin (n + 1) → Opening F G₁) (hmem : ∀ i, node i ∈ os)
    (hinj : Function.Injective fun i => (node i).1) {x : Opening F G₁} (hx : x ∈ os)
    (hxI : (interpolant node).toPoly.eval x.1 ≠ x.2.1) :
    arsdhWins τ n
      (if (interpolationAnswer (committerKey g₁ τ n) (c • g₁) node).2.1 = 0 then
        interpolationAnswer (committerKey g₁ τ n) (c • g₁) (Function.update node 0 x)
      else interpolationAnswer (committerKey g₁ τ n) (c • g₁) node) := by
  have hτn : ∀ i, (node i).1 ≠ τ := fun i => hτ _ (hmem i)
  split_ifs with h0
  · rw [interpolationAnswer_h₁ g₁ τ c node hinj, smul_eq_zero] at h0
    have hcI : c = (interpolant node).toPoly.eval τ := sub_eq_zero.mp (h0.resolve_right hg₁)
    have hx_ne : ∀ j, x.1 ≠ (node j).1 := fun j h => hxI <| by
      rw [h, eval_toPoly_interpolant node hinj j]
      exact hnc _ (hmem j) _ hx h.symm
    have hinj' : Function.Injective fun i => (Function.update node 0 x i).1 := by
      intro i j hij
      simp only [Function.update_apply] at hij
      split_ifs at hij with hi hj hj
      · exact hi.trans hj.symm
      · exact absurd hij (hx_ne j)
      · exact absurd hij.symm (hx_ne i)
      · exact hinj hij
    have hmem' : ∀ i, Function.update node 0 x i ∈ os := fun i => by
      rw [Function.update_apply]
      split_ifs
      exacts [hx, hmem i]
    refine interpolationAnswer_wins hg₁ τ c _ hinj' (fun i => hτ _ (hmem' i))
      (fun i => hπ _ (hmem' i)) fun hcI' => ?_
    have hvs : Set.InjOn (Function.update (fun i => (node i).1) 0 τ)
        ((univ : Finset (Fin (n + 1))) : Set (Fin (n + 1))) := by
      intro i _ j _ hij
      simp only [Function.update_apply] at hij
      split_ifs at hij with hi hj hj
      · exact hi.trans hj.symm
      · exact absurd hij.symm (hτn j)
      · exact absurd hij (hτn i)
      · exact hinj hij
    have heq : (interpolant node).toPoly = (interpolant (Function.update node 0 x)).toPoly := by
      refine Polynomial.eq_of_degrees_lt_of_eval_index_eq univ hvs
        (by simpa using degree_toPoly_interpolant_lt node hinj)
        (by simpa using degree_toPoly_interpolant_lt _ hinj') fun i _ => ?_
      simp only [Function.update_apply]
      split_ifs with hi
      · rw [← hcI, ← hcI']
      · have h' := eval_toPoly_interpolant _ hinj' i
        simp only [Function.update_of_ne hi] at h'
        rw [eval_toPoly_interpolant node hinj i, h']
    have h0' := eval_toPoly_interpolant _ hinj' 0
    simp only [Function.update_self] at h0'
    exact hxI (heq ▸ h0')
  · refine interpolationAnswer_wins hg₁ τ c node hinj hτn (fun i => hπ _ (hmem i)) fun hcI => ?_
    rw [interpolationAnswer_h₁ g₁ τ c node hinj, hcI, sub_self, zero_smul] at h0
    exact h0 rfl

/-- **Interpolation case.** Without conflicts and with `τ` not a query, if every proof is
`((τ - q)⁻¹ * (c - r)) • g₁` and no coefficient vector fits the openings, the generic answer
wins. -/
theorem genericAnswer_wins [DecidableEq G₁] (hg₁ : g₁ ≠ 0) (τ c : F)
    {os : List (Opening F G₁)}
    (hnc : ∀ o ∈ os, ∀ o' ∈ os, o.1 = o'.1 → o.2.1 = o'.2.1) (hτ : ∀ o ∈ os, o.1 ≠ τ)
    (hπ : ∀ o ∈ os, o.2.2 = ((τ - o.1)⁻¹ * (c - o.2.1)) • g₁)
    (hfit : ¬ ∃ c : Fin (n + 1) → F, ∀ o ∈ os, evaluate c o.1 = o.2.1) :
    arsdhWins τ n (genericAnswer (committerKey g₁ τ n) (c • g₁) os) := by
  have hDsub : ∀ d ∈ distinctOpenings os, d ∈ os := fun d hd => List.pwFilter_subset os hd
  have hDpair : (distinctOpenings os).Pairwise fun a b => a.1 ≠ b.1 := List.pairwise_pwFilter os
  have hDcover : ∀ o ∈ os, ∃ d ∈ distinctOpenings os, d.1 = o.1 := by
    intro o ho
    by_contra hno
    push Not at hno
    have hall := (List.forall_mem_pwFilter (R := fun a b : Opening F G₁ => a.1 ≠ b.1)
      (fun {x y z} hxz => by
        by_contra hc
        push Not at hc
        exact hxz (hc.1.trans hc.2)) o os).mp fun d hd => (hno d hd).symm
    exact hall o ho rfl
  unfold genericAnswer
  dsimp only
  set D := distinctOpenings os with hDdef
  split
  · rename_i hD
    have hmem : ∀ i : Fin (n + 1), D[i.1]'(lt_of_lt_of_le i.isLt hD) ∈ os :=
      fun i => hDsub _ (List.getElem_mem _)
    have hinj : Function.Injective
        fun i : Fin (n + 1) => (D[i.1]'(lt_of_lt_of_le i.isLt hD)).1 := by
      intro i j hij
      have hp := List.pairwise_iff_getElem.mp hDpair
      by_contra hne
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · exact hp _ _ _ _ h hij
      · exact hp _ _ _ _ h hij.symm
    split
    · rename_i hnone
      refine absurd ?_ hfit
      refine exists_fit_of_eval (natDegree_toPoly_interpolant_le _ hinj) fun o ho => ?_
      have := List.find?_eq_none.mp hnone o ho
      simp only [bne_iff_ne, ne_eq, not_not] at this
      rw [← CPolynomial.eval_toPoly, this]
    · rename_i x hx
      have hxI := List.find?_some hx
      simp only [bne_iff_ne, ne_eq] at hxI
      rw [CPolynomial.eval_toPoly] at hxI
      exact interpolationChoice_wins hg₁ τ c hnc hτ hπ _ hmem hinj
        (List.mem_of_find?_eq_some hx) hxI
  · rename_i hD
    rw [← hDdef] at hD
    refine absurd ?_ hfit
    have : Std.Symm fun a b : Opening F G₁ => a.1 ≠ b.1 := ⟨fun _ _ h h' => h h'.symm⟩
    refine exists_fit_of_cover hnc D.toFinset ((List.toFinset_card_le D).trans (by omega))
      (fun a ha b hb hab => ?_) (fun a ha => hDsub a (List.mem_toFinset.mp ha))
      fun o ho => ?_
    · by_contra hne
      exact hDpair.forall (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hne hab
    · obtain ⟨d, hd, hdo⟩ := hDcover o ho
      exact ⟨d, List.mem_toFinset.mpr hd, hdo⟩

end Generic

/-- **Function binding reduces to ARSDH, pointwise.** If `e g₁ g₂ ≠ 0`, `g₁` generates `G₁`,
every opening in `os` is accepted for `cm` under the honest verifier key for `τ`, and no
coefficient vector of length `n + 1` fits all openings, then `functionBindingReduction` satisfies
the win predicate of `ARSDH.experiment` with `D = n`. -/
theorem functionBindingReduction_wins [DecidableEq G₁] [DecidableEq G₂] [DecidableEq Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂} (he : e g₁ g₂ ≠ 0)
    (hg₁ : Function.Surjective (· • g₁ : F → G₁)) (τ : F) (pts : Fin (n + 2) ↪ F)
    {cm : G₁} {os : List (Opening F G₁)}
    (haccept : ∀ o ∈ os, verifyOpening e g₁ (verifierKey g₂ τ) cm o.1 o.2.1 o.2.2 = true)
    (hfit : ¬ ∃ c : Fin (n + 1) → F, ∀ o ∈ os, evaluate c o.1 = o.2.1) :
    arsdhWins τ n
      (functionBindingReduction pts (committerKey g₁ τ n) (verifierKey g₂ τ) cm os) := by
  unfold functionBindingReduction
  split
  · rename_i o o' hc
    obtain ⟨ho, ho', hq, hr⟩ := findConflict_eq_some hc
    have h₂ := haccept o' ho'
    rw [hq] at h₂
    obtain ⟨hτq, hπ⟩ := evalBindingReduction_wins he hg₁ τ (haccept o ho) h₂ hr.symm
    simp only [evalBindingReduction, ← sub_eq_add_neg] at hτq hπ ⊢
    rw [hπ]
    exact conflictAnswer_wins he τ pts hτq
  · rename_i hnc
    split
    · rename_i o ho
      have hoτ := List.find?_some ho
      rw [(isTrapdoor_verifierKey he τ o.1).mp hoτ]
      exact trapdoorAnswer_wins he τ pts
    · rename_i hnt
      obtain ⟨c, hc⟩ := hg₁ cm
      simp only at hc
      subst hc
      have hτ : ∀ o ∈ os, o.1 ≠ τ := fun o ho h =>
        List.find?_eq_none.mp hnt o ho ((isTrapdoor_verifierKey he τ o.1).mpr h)
      exact genericAnswer_wins (ne_zero_left_of_pairing_ne_zero he) τ c
        (findConflict_eq_none hnc) hτ
        (fun o ho => opening_proof_eq he hg₁ (haccept o ho) (hτ o ho)) hfit

end FunctionBinding

end KZG
