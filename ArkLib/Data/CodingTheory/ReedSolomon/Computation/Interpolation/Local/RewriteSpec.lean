/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Local.RewriteMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Local.TranslateSpec
public import Mathlib.Algebra.Ring.Parity
/-!
# Exact local rewrite and projection semantics

Dense visible-jet coordinates denote the canonical finite local variables. The executed branch
expansion multiplies by E+localJetSum, and the executed contact filter is projectLowContact.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.LocalColumnRewriteMachine

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [CommRing F] {d : ℕ}

/-- Higher exponent represented by a materialized list in its fixed coordinate order. -/
def higher (d : ℕ) (xs : List ℕ) : LocalVariable d →₀ ℕ :=
  LocalColumnTranslationMachine.higherExponent (fun j => xs.getD j.val 0)

/-- Complete exponent of a structured output term. -/
def exponent (d : ℕ) (t : Term F) : LocalVariable d →₀ ℕ :=
  LocalColumnTranslationMachine.exponent (higher d t.jets) t.t t.e

/-- The exact polynomial monomial denoted by a structured term. -/
def termPolynomial (d : ℕ) (t : Term F) : LocalPolynomial F d :=
  monomial (exponent d t) t.coefficient

/-- Duplicate materialized terms denote a polynomial sum. -/
def represented (d : ℕ) (ts : List (Term F)) : LocalPolynomial F d :=
  (ts.map (termPolynomial d)).sum

/-- The vector update changes one coordinate and preserves all others. -/
theorem getD_modify (xs : List ℕ) (i j : ℕ) (hi : i < xs.length) :
    (xs.modify i (· + 1)).getD j 0 = xs.getD j 0 + if i = j then 1 else 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases h : i = j
  · subst j
    rw [if_pos rfl, List.getElem?_eq_getElem hi]
    simp
  · simp [h]

/-- Incrementing a valid visible coordinate adds exactly that local variable exponent. -/
theorem higher_bump (xs : List ℕ) (hlen : xs.length = d) (j : Fin d) :
    higher d (xs.modify j.val (· + 1)) = higher d xs + Finsupp.single (localY j) 1 := by
  classical
  ext v
  rcases v with _ | (_ | k)
  · simp [higher, LocalColumnTranslationMachine.higherExponent, localY]
  · simp [higher, LocalColumnTranslationMachine.higherExponent, localY]
  · simp only [higher, LocalColumnTranslationMachine.higherExponent, localY,
      Finsupp.finsetSum_apply, Finsupp.single_apply, Option.some.injEq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finsupp.add_apply]
    rw [getD_modify xs j.val k.val (by omega)]
    congr 1
    simp only [Fin.ext_iff]

/-- Alternating signs are computed by parity and scalar negation, not exponentiation. -/
theorem signed_eq (j : ℕ) (c : F) : signed j c = (-1 : F) ^ j * c := by
  rw [neg_one_pow_eq_pow_mod_two]
  have hmod := Nat.mod_lt j (by decide : 0 < 2)
  by_cases hj : j % 2 = 0
  · simp [signed, hj]
  · have h : j % 2 = 1 := by omega
    simp [signed, h]

/-- A visible branch denotes multiplication by its signed Taylor summand. -/
theorem jetBranch_polynomial (t : Term F) (ht : t.jets.length = d) (j : Fin d) :
    termPolynomial d (jetBranch j.val t) = termPolynomial d t *
      (C ((-1 : F)^j.val) * X (localT d)^j.val * X (localY j)) := by
  classical
  simp only [termPolynomial, exponent, jetBranch, higher_bump t.jets ht j,
    LocalColumnTranslationMachine.exponent, signed_eq, Finsupp.single_add]
  rw [X_pow_eq_monomial]
  simp only [X, C_mul_monomial, monomial_mul, mul_one]
  congr 1
  · abel_nf
  · ring

/-- The E branch increments just the error coordinate. -/
theorem errorBranch_polynomial (t : Term F) :
    termPolynomial d (⟨t.coefficient, t.t, t.e + 1, t.jets⟩ : Term F) =
      termPolynomial d t * X (localE d) := by
  simp only [termPolynomial, exponent, LocalColumnTranslationMachine.exponent,
    X, monomial_mul, mul_one, Finsupp.single_add]
  congr 1
  abel_nf

/-- All visible branches are precisely the signed jet sum, with no summand omitted. -/
theorem jetBranches_polynomial (t : Term F) (ht : t.jets.length = d) :
    represented d (jetBranches d t).1 = termPolynomial d t * localJetSum d := by
  rw [jetBranches_result]
  simp only [represented, List.map_reverse, List.sum_reverse, List.map_ofFn, List.sum_ofFn]
  change (∑ j : Fin d, termPolynomial d (jetBranch j.val t)) = _
  simp_rw [jetBranch_polynomial t ht]
  rw [localJetSum, Finset.mul_sum]

/-- A single executed multiplication is exactly multiplication by the U rewrite polynomial. -/
theorem multiplyU_polynomial (t : Term F) (ht : t.jets.length = d) :
    represented d (multiplyU d t).1 = termPolynomial d t * (X (localE d) + localJetSum d) := by
  simp only [multiplyU, represented, List.map_cons, List.sum_cons]
  rw [errorBranch_polynomial]
  change _ + represented d (jetBranches d t).1 = _
  rw [jetBranches_polynomial t ht, mul_add]

/-- Branch generation preserves the supplied dense layout width. -/
theorem multiplyU_width (t : Term F) (ht : t.jets.length = d) :
    ∀ s ∈ (multiplyU d t).1, s.jets.length = d := by
  intro s hs
  simp only [multiplyU, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact ht
  · rw [jetBranches_result, List.mem_reverse] at hs
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
    simpa [jetBranch] using ht

theorem round_width (ts : List (Term F)) (ht : ∀ t ∈ ts, t.jets.length = d) :
    ∀ t ∈ (round d ts).1, t.jets.length = d := by
  induction ts with
  | nil => simp [round]
  | cons t ts ih =>
    simp only [round, appendCells_correct, List.mem_append]
    intro s hs
    rcases hs with hs | hs
    · exact multiplyU_width t (ht t (by simp)) s hs
    · exact ih (fun s hs => ht s (by simp [hs])) s hs

theorem round_polynomial (ts : List (Term F)) (ht : ∀ t ∈ ts, t.jets.length = d) :
    represented d (round d ts).1 = represented d ts * (X (localE d) + localJetSum d) := by
  induction ts with
  | nil => simp [round, represented]
  | cons t ts ih =>
    simp only [round, appendCells_correct, represented, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons]
    change represented d (multiplyU d t).1 + represented d (round d ts).1 = _
    rw [multiplyU_polynomial t (ht t (by simp)), ih (fun s hs => ht s (by simp [hs]))]
    simp only [add_mul, represented]

theorem power_width (n : ℕ) (ts : List (Term F)) (ht : ∀ t ∈ ts, t.jets.length = d) :
    ∀ t ∈ (power d n ts).1, t.jets.length = d := by
  induction n generalizing ts with
  | zero => exact ht
  | succ n ih => exact ih (round d ts).1 (round_width ts ht)

/-- Iterated actual branch expansion realizes the complete U power. -/
theorem power_polynomial (n : ℕ) (ts : List (Term F)) (ht : ∀ t ∈ ts, t.jets.length = d) :
    represented d (power d n ts).1 =
      represented d ts * (X (localE d) + localJetSum d)^n := by
  induction n generalizing ts with
  | zero => simp [power]
  | succ n ih =>
    simp only [power]
    rw [ih _ (round_width ts ht), round_polynomial ts ht, pow_succ]
    ring


omit [CommRing F] in
/-- The scalar filter computes the exact existing local contact weight. -/
theorem exponent_contact (t : Term F) : localContactOrder d (exponent d t) = t.t + d * t.e := by
  simp [localContactOrder, exponent, LocalColumnTranslationMachine.exponent, higher,
    LocalColumnTranslationMachine.higherExponent, map_add, map_sum, Finsupp.weight_single,
    localContactWeight, localT, localU, localAux, localY, mul_comm]

/-- Filtering one term is exactly the coefficient projection, including cancellation-safe zeros. -/
theorem project_term (m : ℕ) (t : Term F) :
    projectLowContact m (termPolynomial d t) =
      if t.t + d * t.e < m then termPolynomial d t else 0 := by
  classical
  ext e
  rw [projectLowContact, coeff_filterLocalMonomials]
  by_cases he : exponent d t = e
  · subst e
    rw [exponent_contact]
    split_ifs <;> simp
  · split_ifs <;> simp [termPolynomial, coeff_monomial, he]

/-- Executed contact filtering denotes the actual low-contact projection. -/
theorem project_polynomial (m : ℕ) (ts : List (Term F)) :
    represented d (project d m ts).1 = projectLowContact m (represented d ts) := by
  induction ts with
  | nil => simp [project, represented]
  | cons t ts ih =>
    simp only [project, represented, List.map_cons, List.sum_cons, map_add, project_term]
    split_ifs <;> simp_all [represented]

/-- Factor form of the fixed local exponent representation. -/
theorem atom_factor (h : LocalVariable d →₀ ℕ) (t u : ℕ) (c : F) :
    LocalColumnTranslationMachine.atom h t u c =
      C c * X (localT d)^t * X (localE d)^u * monomial h 1 := by
  simp only [LocalColumnTranslationMachine.atom, LocalColumnTranslationMachine.exponent,
    X_pow_eq_monomial, C_mul_monomial, monomial_mul, mul_one]

/-- The rewrite fixes every visible-jet monomial. -/
theorem rewrite_higher (xs : List ℕ) :
    rewriteUToE d (monomial (higher d xs) (1 : F)) = monomial (higher d xs) 1 := by
  classical
  have h (s : Finset (Fin d)) :
      rewriteUToE d (monomial (∑ j ∈ s, Finsupp.single (localY j) (xs.getD j.val 0)) (1 : F)) =
        monomial (∑ j ∈ s, Finsupp.single (localY j) (xs.getD j.val 0)) 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      have he : (monomial (Finsupp.single (localY j) (xs.getD j.val 0) +
          ∑ j ∈ s, Finsupp.single (localY j) (xs.getD j.val 0)) (1 : F)) =
          monomial (Finsupp.single (localY j) (xs.getD j.val 0)) 1 *
            monomial (∑ j ∈ s, Finsupp.single (localY j) (xs.getD j.val 0)) 1 := by
        rw [monomial_mul, mul_one]
      rw [he, map_mul, ih, ← X_pow_eq_monomial, map_pow]
      simp [rewriteUToE, localY]
  exact h Finset.univ

/-- Actual U-power expansion of a translated term has the exact existing rewrite meaning. -/
theorem seed_power_polynomial (xs : List ℕ) (hx : xs.length = d)
    (t : LocalColumnTranslationMachine.Term F) :
    represented d (power d t.u [⟨t.coefficient, t.t, 0, xs⟩]).1 =
      rewriteUToE d (LocalColumnTranslationMachine.atom (higher d xs) t.t t.u t.coefficient) := by
  rw [power_polynomial _ _ (by simpa using hx)]
  simp only [represented, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  change LocalColumnTranslationMachine.atom (higher d xs) t.t 0 t.coefficient * _ = _
  rw [atom_factor, atom_factor]
  simp only [pow_zero, mul_one, map_mul, map_pow, algHom_C, rewrite_higher]
  simp [rewriteUToE, localT, localE, localAux]
  ring

/-- All output terms preserve the caller's fixed visible-vector width. -/
theorem rewrite_width (m : ℕ) (xs : List ℕ) (hx : xs.length = d)
    (ts : List (LocalColumnTranslationMachine.Term F)) :
    ∀ t ∈ (rewrite d m xs ts).1, t.jets.length = d := by
  induction ts with
  | nil => simp [rewrite]
  | cons t ts ih =>
    simp only [rewrite, appendCells_correct, List.mem_append]
    intro s hs
    rcases hs with hs | hs
    · rw [project_correct] at hs
      exact power_width t.u [⟨t.coefficient, t.t, 0, xs⟩] (by simpa using hx) s
        (List.mem_filter.mp hs).1
    · exact ih s hs

/-- The complete executed rewrite and projection is the existing enlarged local map. -/
theorem rewrite_polynomial (m : ℕ) (xs : List ℕ) (hx : xs.length = d)
    (ts : List (LocalColumnTranslationMachine.Term F)) :
    represented d (rewrite d m xs ts).1 =
      enlargedLocalConstraintMap m
        (LocalColumnTranslationMachine.represented (higher d xs) ts) := by
  induction ts with
  | nil => simp [rewrite, represented, LocalColumnTranslationMachine.represented]
  | cons t ts ih =>
    simp only [rewrite, appendCells_correct, represented, List.map_append, List.sum_append,
      LocalColumnTranslationMachine.represented, map_add]
    change represented d (project d m (power d t.u [⟨t.coefficient, t.t, 0, xs⟩]).1).1 +
      represented d (rewrite d m xs ts).1 = _
    rw [project_polynomial, seed_power_polynomial xs hx t, ih]
    rfl

/-- Meaning of a dense term in the common fixed coordinate layout. Malformed short lists
are assigned zero; public execution emits width d+2. -/
def densePolynomial (d : ℕ) (term : DenseTerm F) : LocalPolynomial F d :=
  match term.2 with
  | t :: e :: xs => termPolynomial d ⟨term.1, t, e, xs⟩
  | _ => 0

def denseRepresented (d : ℕ) (ts : List (DenseTerm F)) : LocalPolynomial F d :=
  (ts.map (densePolynomial d)).sum

/-- Prefix allocation preserves represented polynomials. -/
theorem densify_polynomial (ts : List (Term F)) :
    denseRepresented d (densify ts).1 = represented d ts := by
  rw [densify_correct]
  simp [denseRepresented, represented, List.map_map, Function.comp_def, densePolynomial]

/-- The actual emitted dense output denotes projectLowContact after the U-to-E rewrite. -/
theorem execute_polynomial (m : ℕ) (xs : List ℕ) (hx : xs.length = d)
    (ts : List (LocalColumnTranslationMachine.Term F)) :
    denseRepresented d (execute d m xs ts).1 =
      projectLowContact m (rewriteUToE d
        (LocalColumnTranslationMachine.represented (higher d xs) ts)) := by
  rw [execute, densify_polynomial, rewrite_polynomial m xs hx]
  rfl

/-- The promised dense layout is present in every actual output, with no assumed normalization. -/
theorem execute_width (m : ℕ) (xs : List ℕ) (hx : xs.length = d)
    (ts : List (LocalColumnTranslationMachine.Term F)) :
    ∀ t ∈ (execute d m xs ts).1, t.2.length = d + 2 := by
  intro t ht
  rw [execute, densify_correct] at ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  have h := rewrite_width m xs hx ts s hs
  simp [h]

/-- Translation followed by this actual dense expansion represents localConstraintAt itself. -/
theorem execute_column_polynomial (a y : F) (x b m : ℕ) (higherJets : Fin d → ℕ) :
    denseRepresented d (execute d m (List.ofFn higherJets)
      (LocalColumnTranslationMachine.columnSpec a y x b m)).1 =
        localConstraintAt m a y (sourceMonomial x b higherJets) := by
  rw [execute_polynomial m _ (List.length_ofFn)]
  have hh : higher d (List.ofFn higherJets) =
      LocalColumnTranslationMachine.higherExponent higherJets := by
    unfold higher
    congr 1
    funext j
    simp [List.getD_eq_getElem?_getD]
  rw [hh, LocalColumnTranslationMachine.localConstraintAt_eq_enlarged_represented]
  rfl

/-- Every retained term satisfies the strict final contact test. -/
theorem rewrite_contact (m : ℕ) (xs : List ℕ)
    (ts : List (LocalColumnTranslationMachine.Term F)) :
    ∀ t ∈ (rewrite d m xs ts).1, t.t + d * t.e < m := by
  induction ts with
  | nil => simp [rewrite]
  | cons t ts ih =>
    simp only [rewrite, appendCells_correct, List.mem_append]
    intro s hs
    rcases hs with hs | hs
    · rw [project_correct] at hs
      exact of_decide_eq_true (List.mem_filter.mp hs).2
    · exact ih s hs

/-- The preliminary translation gives the needed gap-only U exponent bound. -/
theorem columnSpec_u_bound (a y : F) (x b m : ℕ) :
    ∀ t ∈ LocalColumnTranslationMachine.columnSpec a y x b m, t.u ≤ m := by
  have hr (i k : ℕ) (c : F) (cs : List F) :
      ∀ t ∈ LocalColumnTranslationMachine.rowSpec m i c k cs, t.u ≤ m := by
    induction cs generalizing k with
    | nil => simp [LocalColumnTranslationMachine.rowSpec]
    | cons z zs ih =>
      simp only [LocalColumnTranslationMachine.rowSpec]
      split
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · dsimp; omega
        · exact ih _ _ ht
      · exact ih _
  have hp (i : ℕ) (cs ds : List F) :
      ∀ t ∈ LocalColumnTranslationMachine.pairsSpec m ds i cs, t.u ≤ m := by
    induction cs generalizing i with
    | nil => simp [LocalColumnTranslationMachine.pairsSpec]
    | cons c cs ih =>
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact hr _ _ _ _ t ht
      · exact ih _ t ht
  exact hp _ _ _

/-- A complete scalar-input column program succeeds and denotes the actual local constraint. -/
theorem column_refines (a y : F) (x b m : ℕ) (higherJets : Fin d → ℕ) :
    ∃ ts c, column d m (List.ofFn higherJets) a y x b = (some ts, c) ∧
      denseRepresented d ts =
        localConstraintAt m a y (sourceMonomial x b higherJets) ∧
      (∀ t ∈ ts, t.2.length = d + 2) ∧
      ts.length ≤ (d + 2) ^ (m + 2) * (m * m) ∧
      c ≤ 288 * (x + b + m + 2) * (m + 1) +
        8192 * (m + 2) * (d + 2) ^ (m + 2) * (m * m + 1) + 32 := by
  obtain ⟨c, hc, hcost⟩ := LocalColumnTranslationMachine.construction_correct a y x b m
  have hl : (LocalColumnTranslationMachine.columnSpec a y x b m).length ≤ m * m := by
    simpa [LocalColumnTranslationMachine.columnSpec,
      Polynomial.AffinePowerTruncationMachine.coefficients_length] using
      LocalColumnTranslationMachine.pairsSpec_length_le m 0
        (Polynomial.AffinePowerTruncationMachine.coefficients
          ((Polynomial.C a + Polynomial.X)^x) m 0)
        (Polynomial.AffinePowerTruncationMachine.coefficients
          ((Polynomial.C y + Polynomial.X)^b) m 0)
  obtain ⟨helen, hecost⟩ := execute_bounds d m (List.ofFn higherJets)
    (LocalColumnTranslationMachine.columnSpec a y x b m) (columnSpec_u_bound a y x b m)
  refine ⟨_, 32 + c +
    (execute d m (List.ofFn higherJets) (LocalColumnTranslationMachine.columnSpec a y x b m)).2,
    ?_, execute_column_polynomial a y x b m higherJets,
    execute_width m _ List.length_ofFn _, helen.trans (Nat.mul_le_mul_left _ hl), ?_⟩
  · simp only [column, LocalColumnTranslationMachine.translate, hc]
  · have hf := LocalColumnTranslationMachine.fuel_le x b m
    have hc' : c ≤ 288 * (x + b + m + 2) * (m + 1) := by nlinarith
    have hecost' := hecost.trans (Nat.mul_le_mul_left
      (8192 * (m + 2) * (d + 2) ^ (m + 2)) (Nat.add_le_add_right hl 1))
    omega

omit [CommRing F] in
theorem exponent_T (t : Term F) : exponent d t (localT d) = t.t := by
  simp [exponent, LocalColumnTranslationMachine.exponent, higher,
    LocalColumnTranslationMachine.higherExponent, localT, localU,
    localAux, localY]

omit [CommRing F] in
theorem exponent_E (t : Term F) : exponent d t (localE d) = t.e := by
  simp [exponent, LocalColumnTranslationMachine.exponent, higher,
    LocalColumnTranslationMachine.higherExponent, localT, localU,
    localE, localAux, localY]

omit [CommRing F] in
theorem exponent_Y (t : Term F) (j : Fin d) :
    exponent d t (localY j) = t.jets.getD j.val 0 := by
  simp [exponent, LocalColumnTranslationMachine.exponent, higher,
    LocalColumnTranslationMachine.higherExponent, localT, localU,
    localAux, localY, Finsupp.single_apply]

omit [CommRing F] in
/-- Valid dense vectors have unique exponents, independently of their scalar coefficients. -/
theorem exponent_eq_iff (s t : Term F) (hs : s.jets.length = d) (ht : t.jets.length = d) :
    exponent d s = exponent d t ↔ s.t :: s.e :: s.jets = t.t :: t.e :: t.jets := by
  constructor
  · intro h
    have hT := congrArg (fun e => e (localT d)) h
    have hE := congrArg (fun e => e (localE d)) h
    simp only [exponent_T, exponent_E] at hT hE
    have hj : s.jets = t.jets := by
      apply List.ext_getElem (hs.trans ht.symm)
      intro i hi hi'
      have hy := congrArg (fun e => e (localY (⟨i, by omega⟩ : Fin d))) h
      simpa [exponent_Y, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem hi'] using hy
    simp [hT, hE, hj]
  · intro h
    simp only [List.cons.injEq] at h
    simp [exponent, h.1, h.2.1, h.2.2]

/-- Full-vector duplicate-aware lookup is a polynomial coefficient on valid dense terms. -/
theorem coordinate_coeff (q : Term F) (hq : q.jets.length = d) (ts : List (DenseTerm F))
    (ht : ∀ t ∈ ts, t.2.length = d + 2) :
    coordinate (q.t :: q.e :: q.jets) ts = coeff (exponent d q) (denseRepresented d ts) := by
  induction ts with
  | nil => simp [coordinate, denseRepresented]
  | cons t ts ih =>
    obtain ⟨c, row⟩ := t
    have hw := ht (c, row) (by simp)
    obtain ⟨i, e, xs, rfl⟩ : ∃ i e xs, row = i :: e :: xs := by
      cases row with
      | nil => simp at hw
      | cons i row =>
        cases row with
        | nil => simp at hw
        | cons e xs => exact ⟨i, e, xs, rfl⟩
    have hx : xs.length = d := by simpa using hw
    have hi := ih (fun t hm => ht t (by simp [hm]))
    simp only [coordinate, List.map_cons, List.sum_cons, denseRepresented, coeff_add,
      densePolynomial, termPolynomial, coeff_monomial] at hi ⊢
    simpa only [exponent_eq_iff (⟨c, i, e, xs⟩ : Term F) q hx hq] using congrArg₂ (· + ·)
      (rfl : (if i :: e :: xs = q.t :: q.e :: q.jets then c else 0) = _) hi

/-- A coordinate query on actual execution sums all paths of the existing polynomial map. -/
theorem lookup_execute (m : ℕ) (xs : List ℕ) (hx : xs.length = d)
    (ts : List (LocalColumnTranslationMachine.Term F)) (q : Term F) (hq : q.jets.length = d) :
    (lookup (q.t :: q.e :: q.jets) (execute d m xs ts).1).1 =
      coeff (exponent d q) (projectLowContact m (rewriteUToE d
        (LocalColumnTranslationMachine.represented (higher d xs) ts))) := by
  rw [lookup_result, coordinate_coeff q hq _ (execute_width m xs hx ts),
    execute_polynomial m xs hx]

/-- Public dense output carries the strict contact test in its actual stored coordinates. -/
theorem execute_contact (m : ℕ) (xs : List ℕ)
    (ts : List (LocalColumnTranslationMachine.Term F)) :
    ∀ term ∈ (execute d m xs ts).1,
      ∃ t e jets, term.2 = t :: e :: jets ∧ t + d * e < m := by
  intro term ht
  rw [execute, densify_correct] at ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact ⟨s.t, s.e, s.jets, rfl, rewrite_contact m xs ts s hs⟩

/-- Successful public column queries return the existing local-constraint coefficient. -/
theorem lookup_column (a y : F) (x b m : ℕ) (higherJets : Fin d → ℕ)
    (ts : List (DenseTerm F)) (c : ℕ)
    (hc : column d m (List.ofFn higherJets) a y x b = (some ts, c))
    (q : Term F) (hq : q.jets.length = d) :
    (lookup (q.t :: q.e :: q.jets) ts).1 = coeff (exponent d q)
      (localConstraintAt m a y (sourceMonomial x b higherJets)) := by
  obtain ⟨out, cost, he, hp, hw, _⟩ := column_refines a y x b m higherJets
  have hs : out = ts := by simpa using congrArg (fun r => r.1) (he.symm.trans hc)
  subst out
  rw [lookup_result, coordinate_coeff q hq ts hw, hp]

end
end ReedSolomon.HiddenDerivative.LocalColumnRewriteMachine
