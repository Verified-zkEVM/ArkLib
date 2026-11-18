/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.ToMathlib.BigOperators.Fin
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.FoldingRound

/-!
# Folding many received words with shared equal-degree challenges

Start with `k = 2^r` received words.
Each round pairs the rows and combines every pair with the equal-degree combiner.
All pairs of a round share one fresh challenge `(θ, α, β)`.
After `r` rounds a single word remains.

Rows are indexed from zero.
The paper indexes rows from one and writes the new row `i` as
`f_{2i} + (α + β z)(f_{2i-1} + θ f_{2i})`.
Here row `2i` plays the role of the paper's `f_{2i-1}`, and row `2i + 1` that of `f_{2i}`.
So the new row `i` is `f_{2i+1} + (α + β z)(f_{2i} + θ f_{2i+1})`.

Round `j`, counted from one, raises the candidate degree bound from `d + j - 1` to `d + j`.
It is bad when the one-round interleaved equal-degree guarantee fails for its input words.
That guarantee uses degree bound `d + j`, threshold `A` and shared loss one.

Outside bad rounds, work backward from a candidate `P` of degree at most `d + r`.
Each round recovers the parent rows and loses at most one shared agreement point.
So `P` has witnesses of degree at most `d` that fold to `P` and lose at most `r` points.

Each round's input words depend only on the earlier challenges.
So a union bound gives failure probability at most `r ε`.
Here `ε` bounds the interleaved equal-degree error of every round.

This is Theorem 5.2 of [CWYZ26], with the round errors as a hypothesis.
The paper assumes `k ≥ 2`; the statements here also hold for `r = 0`.
The explicit value of `ε` for one round comes from the explicit interleaved equal-degree bound.
The linear-claims extension of Remark 5.3 is not formalized here.
The [paper page](../../../../../../docs/kb/papers/CWYZ26.md) records the correspondence.

The error has type `ENNReal` and a counting definition that requires no sampler.
The sibling sampling module identifies it with a supremum of native probabilities.
The fold of words is computable.
The polynomial fold is noncomputable because the affine multiplier is.

## Main definitions

* `ReedSolomon.evenRows`, `ReedSolomon.oddRows` and `ReedSolomon.interleaveRows`: splitting
  and merging `2^(m+1)` rows.
* `ReedSolomon.foldRoundWords` and `ReedSolomon.foldRoundPolynomials`: one folding round.
* `ReedSolomon.foldWords` and `ReedSolomon.foldPolynomials`: `r` folding rounds.
* `ReedSolomon.IsFoldingExceptional`: some round of the folding is bad.
* `ReedSolomon.foldingMcaError`: the uniform probability that some round is bad.

## Main statements

* `ReedSolomon.evenRows_interleaveRows` and `ReedSolomon.oddRows_interleaveRows`: merging
  inverts splitting.
* `ReedSolomon.exists_foldPolynomials_eq_of_not_isFoldingExceptional`: outside bad rounds,
  every close candidate has witnesses that fold to it.
* `ReedSolomon.le_foldingMcaError` and `ReedSolomon.foldingMcaError_le_one`: basic bounds.
* `ReedSolomon.foldingMcaError_le_mul`: the union bound `r ε`.

## References

* [Chiesa, A., Weissenberg, G., Yogev, E., and Zheng, K. Z.,
    *Affine combiners for Reed–Solomon proximity gaps*][CWYZ26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial Finset

section Rows

variable {M : Type*} {m : ℕ}

/-- The rows `0, 2, 4, …` of `2^(m+1)` rows. -/
def evenRows (v : Fin (2 ^ (m + 1)) → M) (i : Fin (2 ^ m)) : M :=
  v ⟨2 * i, by have := i.isLt; have := pow_succ 2 m; omega⟩

/-- The rows `1, 3, 5, …` of `2^(m+1)` rows. -/
def oddRows (v : Fin (2 ^ (m + 1)) → M) (i : Fin (2 ^ m)) : M :=
  v ⟨2 * i + 1, by have := i.isLt; have := pow_succ 2 m; omega⟩

/-- The rows `u 0, v 0, u 1, v 1, …`, alternating between two families of `2^m` rows. -/
def interleaveRows (u v : Fin (2 ^ m) → M) (j : Fin (2 ^ (m + 1))) : M :=
  if (j : ℕ) % 2 = 0 then u ⟨j / 2, by have := j.isLt; have := pow_succ 2 m; omega⟩
  else v ⟨j / 2, by have := j.isLt; have := pow_succ 2 m; omega⟩

@[simp]
theorem evenRows_interleaveRows (u v : Fin (2 ^ m) → M) : evenRows (interleaveRows u v) = u := by
  funext i
  simp [evenRows, interleaveRows]

@[simp]
theorem oddRows_interleaveRows (u v : Fin (2 ^ m) → M) : oddRows (interleaveRows u v) = v := by
  funext i
  have h : (2 * (i : ℕ) + 1) % 2 ≠ 0 := by omega
  simp only [oddRows, interleaveRows, h, ite_false]
  congr
  omega

/-- Every row is an even row or an odd row. -/
theorem exists_eq_evenRows_or_eq_oddRows (v : Fin (2 ^ (m + 1)) → M) (j : Fin (2 ^ (m + 1))) :
    ∃ i, v j = evenRows v i ∨ v j = oddRows v i := by
  refine ⟨⟨j / 2, by have := j.isLt; have := pow_succ 2 m; omega⟩, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · exact Or.inl (congrArg v (Fin.ext (by simp only; omega)))
  · exact Or.inr (congrArg v (Fin.ext (by simp only; omega)))

end Rows

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι] {m : ℕ}

/-- One folding round of `2^(m+1)` received words with the challenge `c = (θ, α, β)`.

The new row `i` is `f_{2i+1} + (α + β x)(f_{2i} + θ f_{2i+1})`. -/
def foldRoundWords (domain : ι ↪ F) (c : F × F × F) (f : Fin (2 ^ (m + 1)) → ι → F) :
    Fin (2 ^ m) → ι → F :=
  fun i ↦ equalDegreeWord domain (evenRows f i) (oddRows f i) c.1 c.2.1 c.2.2

/-- One folding round of `2^(m+1)` polynomials with the challenge `c = (θ, α, β)`.

The new row `i` is `P_{2i+1} + (α + β X)(P_{2i} + θ P_{2i+1})`. -/
noncomputable def foldRoundPolynomials (c : F × F × F) (P : Fin (2 ^ (m + 1)) → F[X]) :
    Fin (2 ^ m) → F[X] :=
  fun i ↦ oddRows P i + affineMultiplier c.2.1 c.2.2 * (evenRows P i + C c.1 * oddRows P i)

/-- The single word left after `r` folding rounds of `2^r` received words.
Round `j`, counted from zero, uses the challenge `c j`. -/
def foldWords (domain : ι ↪ F) : (r : ℕ) → (Fin r → F × F × F) → (Fin (2 ^ r) → ι → F) → ι → F
  | 0, _, f => f 0
  | r + 1, c, f => foldWords domain r (Fin.tail c) (foldRoundWords domain (c 0) f)

/-- The single polynomial left after `r` folding rounds of `2^r` polynomials.
Round `j`, counted from zero, uses the challenge `c j`. -/
noncomputable def foldPolynomials : (r : ℕ) → (Fin r → F × F × F) → (Fin (2 ^ r) → F[X]) → F[X]
  | 0, _, P => P 0
  | r + 1, c, P => foldPolynomials r (Fin.tail c) (foldRoundPolynomials (c 0) P)

/-- Some round of the folding of `2^r` received words with the challenges `c` is bad.

Round `j`, counted from one, folds words of degree `d + j - 1` with the challenge `c (j - 1)`.
It is bad when some tuple is interleaved equal-degree exceptional for its input words.
That uses output degree bound `d + j`, agreement threshold `A` and shared loss one.
The rows `2i` and `2i + 1` of the input words form the pair `i`. -/
def IsFoldingExceptional (domain : ι ↪ F) :
    (d A r : ℕ) → (Fin r → F × F × F) → (Fin (2 ^ r) → ι → F) → Prop
  | _, _, 0, _, _ => False
  | d, A, r + 1, c, f =>
    (∃ P, IsInterleavedEqualDegreeExceptional domain (evenRows f) (oddRows f) (d + 1) A 1
        (c 0).1 (c 0).2.1 (c 0).2.2 P) ∨
      IsFoldingExceptional domain (d + 1) A r (Fin.tail c) (foldRoundWords domain (c 0) f)

section Deterministic

/-- Outside bad rounds, close candidates of the folded word have witnesses that fold to them.

There are `2^r` received words `f`, folded in `r` rounds with the challenges `c`.
Assume no round is bad at base degree `d` and agreement threshold `A`.
Let `P` have degree at most `d + r`.
Let `S` be a set of at least `A + r` points where `P` agrees with the folded word.
Then some polynomials `W` of degree at most `d` fold to `P` with the same challenges.
At most `r` points of `S` have a row `k` with `W k ≠ f k`. -/
theorem exists_foldPolynomials_eq_of_not_isFoldingExceptional (domain : ι ↪ F) {d A r : ℕ}
    {c : Fin r → F × F × F} {f : Fin (2 ^ r) → ι → F}
    (hc : ¬ IsFoldingExceptional domain d A r c f) {P : F[X]} (hP : P.degree ≤ ↑(d + r))
    {S : Finset ι} (hS : ∀ i ∈ S, P.eval (domain i) = foldWords domain r c f i)
    (hA : A + r ≤ #S) :
    ∃ W : Fin (2 ^ r) → F[X], (∀ k, (W k).degree ≤ d) ∧ foldPolynomials r c W = P ∧
      #{i ∈ S | ∃ k, (W k).eval (domain i) ≠ f k i} ≤ r := by
  classical
  induction r generalizing d with
  | zero =>
    refine ⟨fun _ ↦ P, fun _ ↦ by simpa using hP, rfl, ?_⟩
    rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro i hi ⟨k, hk⟩
    rw [show k = 0 from Fin.ext (by have := k.isLt; simp at this; omega)] at hk
    exact hk (hS i hi)
  | succ r ih =>
    obtain ⟨hc₀, hcr⟩ := not_or.mp hc
    set h := foldRoundWords domain (c 0) f
    -- The later rounds recover the rows `H` of the first folded word.
    obtain ⟨H, hHdeg, hHP, hHloss⟩ := ih (d := d + 1) (f := h) hcr
      (by rwa [show d + 1 + r = d + (r + 1) by omega]) hS (by omega)
    set S' := S.filter fun i ↦ ∀ k, (H k).eval (domain i) = h k i
    have hS' : A + 1 ≤ #S' := by
      have hsplit : #S' + #(S.filter fun i ↦ ¬ ∀ k, (H k).eval (domain i) = h k i) = #S :=
        Finset.card_filter_add_card_filter_not _
      have hneg : #(S.filter fun i ↦ ¬ ∀ k, (H k).eval (domain i) = h k i) ≤ r := by
        refine le_of_eq_of_le (congrArg Finset.card (Finset.filter_congr fun i _ ↦ ?_)) hHloss
        simp only [not_forall]
      omega
    have hsub : S' ⊆ interleavedEqualDegreeAgreementSet domain (evenRows f) (oddRows f)
        (c 0).1 (c 0).2.1 (c 0).2.2 H := fun i hi ↦ by
      rw [mem_interleavedEqualDegreeAgreementSet]
      exact (Finset.mem_filter.mp hi).2
    -- The first round is not bad, so it supplies parent rows for `H`.
    obtain ⟨F₀, G₀, hF₀, hG₀, hFG, hloss⟩ : ∃ F₀ G₀ : Fin (2 ^ r) → F[X],
        (∀ k, (F₀ k).degree < ↑(d + 1)) ∧ (∀ k, (G₀ k).degree < ↑(d + 1)) ∧
        (∀ k, H k = G₀ k + affineMultiplier (c 0).2.1 (c 0).2.2 * (F₀ k + C (c 0).1 * G₀ k)) ∧
        #(interleavedEqualDegreeAgreementLoss domain (evenRows f) (oddRows f)
          (c 0).1 (c 0).2.1 (c 0).2.2 H F₀ G₀) ≤ 1 := by
      by_contra hno
      push Not at hno
      exact hc₀ ⟨H, hHdeg, (by omega : A ≤ A + 1).trans (hS'.trans (Finset.card_le_card hsub)),
        hno⟩
    refine ⟨interleaveRows F₀ G₀, fun k ↦ ?_, ?_, ?_⟩
    · rcases exists_eq_evenRows_or_eq_oddRows (interleaveRows F₀ G₀) k with ⟨i, hi | hi⟩ <;>
        rw [hi] <;> simp only [evenRows_interleaveRows, oddRows_interleaveRows]
      · exact Order.le_of_lt_succ (hF₀ i)
      · exact Order.le_of_lt_succ (hG₀ i)
    · rw [← hHP]
      change foldPolynomials r (Fin.tail c) (foldRoundPolynomials (c 0) (interleaveRows F₀ G₀)) =
        foldPolynomials r (Fin.tail c) H
      congr 1
      funext k
      simp [foldRoundPolynomials, hFG k]
    · refine (Finset.card_le_card (t := {i ∈ S | ∃ k, (H k).eval (domain i) ≠ h k i} ∪
        interleavedEqualDegreeAgreementLoss domain (evenRows f) (oddRows f)
          (c 0).1 (c 0).2.1 (c 0).2.2 H F₀ G₀) fun i hi ↦ ?_).trans
        ((Finset.card_union_le _ _).trans (by omega))
      obtain ⟨hiS, k, hk⟩ := Finset.mem_filter.mp hi
      by_cases hH : ∃ k, (H k).eval (domain i) ≠ h k i
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiS, hH⟩)
      refine Finset.mem_union_right _ ((mem_interleavedEqualDegreeAgreementLoss ..).mpr
        ⟨hsub (Finset.mem_filter.mpr ⟨hiS, by simpa using hH⟩), ?_⟩)
      obtain ⟨j, hj | hj⟩ := exists_eq_evenRows_or_eq_oddRows
        (fun k ↦ ((interleaveRows F₀ G₀ k).eval (domain i), f k i)) k
      · refine ⟨j, Or.inl ?_⟩
        rw [← congrFun (evenRows_interleaveRows F₀ G₀) j]
        simp only [evenRows, Prod.mk.injEq] at hj ⊢
        rw [← hj.1, ← hj.2]
        exact hk
      · refine ⟨j, Or.inr ?_⟩
        rw [← congrFun (oddRows_interleaveRows F₀ G₀) j]
        simp only [oddRows, Prod.mk.injEq] at hj ⊢
        rw [← hj.1, ← hj.2]
        exact hk

end Deterministic

section Error

variable [Fintype F] (domain : ι ↪ F)

open Classical in
/-- The worst-case probability that some folding round is bad.

The supremum ranges over the `2^r` received words, and the `r` challenges are independent and
uniform in `F³`.
The base degree is `d`, so round `j`, counted from one, has output degree bound `d + j`.
Every round uses agreement threshold `A` and shared loss one. -/
noncomputable def foldingMcaError (r d A : ℕ) : ENNReal :=
  ⨆ f : Fin (2 ^ r) → ι → F,
    ENNReal.ofReal ((#{c : Fin r → F × F × F | IsFoldingExceptional domain d A r c f} : ℝ) /
      (Fintype.card F : ℝ) ^ (3 * r))

open Classical in
/-- One family of received words bounds the folding error from below. -/
theorem le_foldingMcaError (r d A : ℕ) (f : Fin (2 ^ r) → ι → F) :
    ENNReal.ofReal ((#{c : Fin r → F × F × F | IsFoldingExceptional domain d A r c f} : ℝ) /
      (Fintype.card F : ℝ) ^ (3 * r)) ≤ foldingMcaError domain r d A := by
  unfold foldingMcaError
  exact le_iSup_of_le f le_rfl

/-- The folding error is at most one. -/
theorem foldingMcaError_le_one (r d A : ℕ) : foldingMcaError domain r d A ≤ 1 := by
  classical
  refine iSup_le fun f ↦ ?_
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_one (by positivity)]
  calc (#{c : Fin r → F × F × F | IsFoldingExceptional domain d A r c f} : ℝ)
      ≤ (Finset.univ : Finset (Fin r → F × F × F)).card := by
        exact_mod_cast Finset.card_filter_le _ _
    _ = (Fintype.card F : ℝ) ^ (3 * r) := by simp [pow_mul, pow_succ, mul_assoc]

open Classical in
/-- The counting form of the union bound over the rounds, for a real bound `e`. -/
private theorem card_isFoldingExceptional_le {e : ℝ} (he : 0 ≤ e) :
    ∀ (r d : ℕ) {A : ℕ} (f : Fin (2 ^ r) → ι → F),
      (∀ j < r, interleavedEqualDegreeMcaError domain (2 ^ (r - 1 - j)) (d + j + 1) A 1 ≤
        ENNReal.ofReal e) →
      (#{c : Fin r → F × F × F | IsFoldingExceptional domain d A r c f} : ℝ) ≤
        r * e * (Fintype.card F : ℝ) ^ (3 * r) := by
  intro r
  induction r with
  | zero =>
    intro d A f _
    simp [IsFoldingExceptional]
  | succ r ih =>
    intro d A f hε
    -- The first round fails on few challenges.
    have h₀ : (#{x : F × F × F | ∃ P, IsInterleavedEqualDegreeExceptional domain (evenRows f)
        (oddRows f) (d + 1) A 1 x.1 x.2.1 x.2.2 P} : ℝ) ≤ e * (Fintype.card F : ℝ) ^ 3 := by
      have h := (le_interleavedEqualDegreeMcaError domain (d + 1) A 1 (evenRows f)
        (oddRows f)).trans (by simpa using hε 0 (by omega))
      rw [ENNReal.ofReal_le_ofReal_iff he, div_le_iff₀ (by positivity)] at h
      exact h
    -- Each first challenge leaves a folding with one round fewer.
    have h₁ (x : F × F × F) : (#{c : Fin r → F × F × F | IsFoldingExceptional domain (d + 1) A r
        c (foldRoundWords domain x f)} : ℝ) ≤ r * e * (Fintype.card F : ℝ) ^ (3 * r) := by
      refine ih (d + 1) _ fun j hj ↦ ?_
      have h := hε (j + 1) (by omega)
      rwa [show r + 1 - 1 - (j + 1) = r - 1 - j by omega,
        show d + (j + 1) + 1 = d + 1 + j + 1 by omega] at h
    have hcount := Fin.card_filter_or_tail_le
      (fun x : F × F × F ↦ ∃ P, IsInterleavedEqualDegreeExceptional domain (evenRows f)
        (oddRows f) (d + 1) A 1 x.1 x.2.1 x.2.2 P)
      (fun x c ↦ IsFoldingExceptional domain (d + 1) A r c (foldRoundWords domain x f))
    have hcard : Fintype.card (F × F × F) = Fintype.card F ^ 3 := by
      simp [Fintype.card_prod, pow_succ, mul_assoc]
    calc (#{c : Fin (r + 1) → F × F × F | IsFoldingExceptional domain d A (r + 1) c f} : ℝ)
        ≤ (#{x : F × F × F | ∃ P, IsInterleavedEqualDegreeExceptional domain (evenRows f)
            (oddRows f) (d + 1) A 1 x.1 x.2.1 x.2.2 P} : ℝ) * ((Fintype.card F : ℝ) ^ 3) ^ r +
          ∑ x : F × F × F, (#{c : Fin r → F × F × F | IsFoldingExceptional domain (d + 1) A r
            c (foldRoundWords domain x f)} : ℝ) := by
          have hnat : #{c : Fin (r + 1) → F × F × F | IsFoldingExceptional domain d A (r + 1) c f}
              ≤ #{x : F × F × F | ∃ P, IsInterleavedEqualDegreeExceptional domain (evenRows f)
                (oddRows f) (d + 1) A 1 x.1 x.2.1 x.2.2 P} * (Fintype.card F ^ 3) ^ r +
              ∑ x : F × F × F, #{c : Fin r → F × F × F | IsFoldingExceptional domain (d + 1) A r
                c (foldRoundWords domain x f)} := by
            rw [← hcard]
            refine le_trans (le_of_eq ?_) hcount
            exact congrArg Finset.card (Finset.filter_congr fun c _ ↦ Iff.rfl)
          exact_mod_cast hnat
      _ ≤ e * (Fintype.card F : ℝ) ^ 3 * ((Fintype.card F : ℝ) ^ 3) ^ r +
          ∑ _x : F × F × F, r * e * (Fintype.card F : ℝ) ^ (3 * r) := by
          gcongr with x
          exact h₁ x
      _ = ((r + 1 : ℕ) : ℝ) * e * (Fintype.card F : ℝ) ^ (3 * (r + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
          push_cast
          ring

/-- The union bound over the folding rounds.

There are `2^r` received words folded in `r` rounds with independent uniform challenges.
The base degree is `d`, the agreement threshold is `A`, and the shared loss is one per round.
Round `j + 1`, for `j < r`, folds `2^(r - 1 - j)` pairs into words of degree `d + j + 1`.
Assume its interleaved equal-degree error is at most `ε`.
Then some round is bad with probability at most `r ε`. -/
theorem foldingMcaError_le_mul {r d A : ℕ} {ε : ENNReal}
    (hε : ∀ j < r, interleavedEqualDegreeMcaError domain (2 ^ (r - 1 - j)) (d + j + 1) A 1 ≤ ε) :
    foldingMcaError domain r d A ≤ r * ε := by
  classical
  rcases eq_or_ne ε ⊤ with rfl | hε_top
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · refine iSup_le fun f ↦ ?_
      simp [IsFoldingExceptional]
    · rw [ENNReal.mul_top (by exact_mod_cast hr.ne')]
      exact le_top
  refine iSup_le fun f ↦ ?_
  have he := card_isFoldingExceptional_le domain (ε.toReal_nonneg) r d f
    fun j hj ↦ (hε j hj).trans_eq (ENNReal.ofReal_toReal hε_top).symm
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) ^ (3 * r) := by positivity
  calc _ ≤ ENNReal.ofReal (r * ε.toReal) :=
        ENNReal.ofReal_le_ofReal ((div_le_iff₀ hq).mpr he)
    _ = r * ε := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_toReal hε_top]

end Error

end ReedSolomon
