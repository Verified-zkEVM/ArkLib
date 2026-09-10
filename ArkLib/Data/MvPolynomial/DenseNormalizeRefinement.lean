/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.DenseNormalizeMachine
public import ArkLib.Data.MvPolynomial.PartialDerivativeRefinement

/-!
# Sparse aggregation correctness and cost

Exact factor-list keys are aggregated without hidden normalization. A common ordered list of
distinct variables makes these keys injective as monomial exponent vectors, including zero
exponents. This is the representation contract needed before selecting mathematically active
variables in the presence of coefficient cancellation.
-/

@[expose] public section

namespace MvPolynomial.DenseNormalizeMachine

open EvaluationMachine (factorsPolynomial sparsePolynomial)
abbrev totalCost := PartialDerivativeMachine.totalCost

private theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b :=
  PartialDerivativeMachine.total_add a b

private theorem total_charge (a d n e o : ℕ) :
    totalCost (charge a d n e o) = a + 1 + d + n + e + o :=
  PartialDerivativeMachine.total_charge a d n e o

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- Declarative insertion, used as a specification rather than a runtime callback. -/
def insertTerm (c : F) (fs : List (ℕ × ℕ)) : List (Term F) → List (Term F)
  | [] => [(c, fs)]
  | (d, gs) :: rest => if fs = gs then
      if c + d = 0 then rest else (c + d, fs) :: rest
    else (d, gs) :: insertTerm c fs rest

/-- Declarative input fold. Actual execution performs every comparison and restoration. -/
def normalize : List (Term F) → List (Term F) → List (Term F)
  | [], out => out
  | (c, fs) :: ts, out => normalize ts (if c = 0 then out else insertTerm c fs out)

/-- Uniform primitive and fuel bound for `m` terms with at most `L` factors each. -/
def budget (m L : ℕ) : ℕ := (60 + 8 * L) * (m + 1) ^ 2 + 5

omit [DecidableEq F] in
private theorem restore_trace (pre out ts : List (Term F)) :
    Trace (pre.length + 1) (.restore pre out ts)
      ⟨⟨0, 0, pre.length + 1, 5 * pre.length + 3, 0, 0⟩, 0⟩
      (.terms ts (pre.reverse ++ out)) := by
  induction pre generalizing out with
  | nil => simpa [charge, PartialDerivativeMachine.charge] using
      Trace.cons (Step.restored (out := out) (ts := ts)) (Trace.nil _)
  | cons t pre ih =>
      simpa [charge, PartialDerivativeMachine.charge, List.reverse_cons, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons Step.restore (ih (t :: out))

private theorem sum_trace (c : F) (fs : List (ℕ × ℕ)) (rest pre ts : List (Term F)) :
    ∃ k cost, Trace k (.sum c fs rest pre ts) cost
      (.terms ts (pre.reverse ++ (if c = 0 then rest else (c, fs) :: rest))) ∧
      k + totalCost cost ≤ 7 * pre.length + 13 := by
  by_cases hc : c = 0
  · subst c
    have h := Trace.cons (Step.zeroSum (fs := fs)) (restore_trace pre rest ts)
    refine ⟨_, _, by simpa using h, ?_⟩
    simp [totalCost, PartialDerivativeMachine.totalCost, charge, PartialDerivativeMachine.charge]
    omega
  · have h := Trace.cons (Step.nonzeroSum hc) (restore_trace pre ((c, fs) :: rest) ts)
    refine ⟨_, _, by simpa only [if_neg hc] using h, ?_⟩
    simp [totalCost, PartialDerivativeMachine.totalCost, charge, PartialDerivativeMachine.charge]
    omega

omit [DecidableEq F] in
private theorem compare_trace (c : F) (fs : List (ℕ × ℕ)) (t : Term F)
    (left right : List (ℕ × ℕ)) (rest pre ts : List (Term F)) :
    ∃ k cost, Trace k (.compare c fs t left right rest pre ts) cost
      (if left = right then .sum (c + t.1) fs rest pre ts
        else .search c fs rest (t :: pre) ts) ∧
      k + totalCost cost ≤ 8 * left.length + 10 := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil =>
          rcases t with ⟨d, gs⟩
          refine ⟨1, charge 1 4 0 0 0, ?_, ?_⟩
          · simpa using Trace.cons
              (Step.equal (c := c) (fs := fs) (d := d) (gs := gs)) (Trace.nil _)
          · simp [total_charge]
      | cons p right =>
          rcases p with ⟨i, e⟩
          refine ⟨1, charge 0 5 0 0 0, ?_, ?_⟩
          · simpa using Trace.cons (Step.short (c := c) (fs := fs) (t := t)) (Trace.nil _)
          · simp [total_charge]
  | cons p left ih =>
      rcases p with ⟨i, e⟩
      cases right with
      | nil =>
          refine ⟨1, charge 0 5 0 0 0, ?_, ?_⟩
          · simpa using Trace.cons (Step.long (c := c) (fs := fs) (t := t)) (Trace.nil _)
          · simp [total_charge]
      | cons q right =>
          rcases q with ⟨j, f⟩
          by_cases hp : i = j ∧ e = f
          · rcases hp with ⟨rfl, rfl⟩
            obtain ⟨k, cost, ht, hc⟩ := ih right
            refine ⟨k + 1, charge 0 4 2 0 0 + cost, ?_, ?_⟩
            · simpa using Trace.cons Step.pair ht
            · rw [total_add, total_charge]
              simp only [List.length_cons]
              omega
          · refine ⟨1, charge 0 6 2 0 0, ?_, ?_⟩
            · simpa [hp] using
                Trace.cons (Step.different (c := c) (fs := fs) (t := t)
                  (not_and_or.mp hp)) (Trace.nil _)
            · simp [total_charge]

private theorem search_trace (c : F) (fs : List (ℕ × ℕ)) (rest pre ts : List (Term F)) :
    ∃ k cost, Trace k (.search c fs rest pre ts) cost
      (.terms ts (pre.reverse ++ insertTerm c fs rest)) ∧
      k + totalCost cost ≤ (30 + 8 * fs.length) * (rest.length + 1) + 7 * pre.length + 13 := by
  induction rest generalizing pre with
  | nil =>
      have h := Trace.cons Step.newKey (restore_trace pre [(c, fs)] ts)
      refine ⟨_, _, by simpa only [insertTerm] using h, ?_⟩
      simp [totalCost, PartialDerivativeMachine.totalCost, charge, PartialDerivativeMachine.charge]
      omega
  | cons t rest ih =>
      rcases t with ⟨d, gs⟩
      obtain ⟨kc, cc, ht, hc⟩ := compare_trace c fs (d, gs) fs gs rest pre ts
      by_cases he : fs = gs
      · rw [if_pos he] at ht
        obtain ⟨ks, cs, hs, hsc⟩ := sum_trace (c + d) fs rest pre ts
        have h := Trace.cons Step.candidate (ht.trans hs)
        refine ⟨_, _, by simpa only [insertTerm, if_pos he] using h, ?_⟩
        simp only [total_add, total_charge]
        simp only [List.length_cons]
        nlinarith
      · rw [if_neg he] at ht
        obtain ⟨ks, cs, hs, hsc⟩ := ih ((d, gs) :: pre)
        have h := Trace.cons Step.candidate (ht.trans hs)
        refine ⟨kc + ks + 1, charge 0 8 0 0 0 + (cc + cs), ?_, ?_⟩
        · simpa [insertTerm, he, List.reverse_cons, List.append_assoc] using h
        · simp only [total_add, total_charge]
          simp only [List.length_cons] at hsc ⊢
          nlinarith

/-- Insertion can add at most one term. -/
theorem insertTerm_length_le (c : F) (fs : List (ℕ × ℕ)) (ts : List (Term F)) :
    (insertTerm c fs ts).length ≤ ts.length + 1 := by
  induction ts with
  | nil => simp [insertTerm]
  | cons t ts ih =>
      rcases t with ⟨d, gs⟩
      simp only [insertTerm]
      split_ifs <;> simp_all; omega

private theorem terms_trace (M L : ℕ) (ts out : List (Term F))
    (hlen : ∀ t ∈ ts, t.2.length ≤ L) (hsize : ts.length + out.length ≤ M) :
    ∃ k cost, Trace k (.terms ts out) cost (.done (normalize ts out)) ∧
      k + totalCost cost ≤ ts.length * ((60 + 8 * L) * (M + 1)) + 5 := by
  induction ts generalizing out with
  | nil =>
      refine ⟨1, charge 0 2 0 0 1, ?_, ?_⟩
      · simpa [normalize] using Trace.cons (Step.emit (out := out)) (Trace.nil _)
      · simp [total_charge]
  | cons t ts ih =>
      rcases t with ⟨c, fs⟩
      have htail : ∀ t ∈ ts, t.2.length ≤ L := fun t ht => hlen t (by simp [ht])
      by_cases hc : c = 0
      · subst c
        obtain ⟨k, cost, ht, hb⟩ := ih out htail (by simp at hsize; omega)
        refine ⟨k + 1, charge 0 2 0 1 0 + cost, ?_, ?_⟩
        · simpa [normalize] using Trace.cons Step.skipZero ht
        · rw [total_add, total_charge]
          simp only [List.length_cons]
          nlinarith [Nat.zero_le (L * M)]
      · obtain ⟨ks, cs, hs, hsc⟩ := search_trace c fs out [] ts
        have hi := insertTerm_length_le c fs out
        obtain ⟨k, cost, ht, hb⟩ := ih (insertTerm c fs out) htail (by simp at hsize; omega)
        have h := Trace.cons (Step.term hc) (hs.trans ht)
        refine ⟨ks + k + 1, charge 0 6 0 1 0 + (cs + cost),
          by simpa [normalize, hc] using h, ?_⟩
        simp only [total_add, total_charge]
        have hf : fs.length ≤ L := hlen (c, fs) (by simp)
        have hm : out.length + 1 ≤ M + 1 := by simp at hsize; omega
        have hc' : (30 + 8 * fs.length) * (out.length + 1) ≤ (30 + 8 * L) * (M + 1) :=
          Nat.mul_le_mul (by omega) hm
        simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hsc
        simp only [List.length_cons]
        nlinarith [Nat.zero_le M]

/-- Bounded execution performs the specified aggregation; no canonicality premise is needed
for this operational theorem. `L` bounds materialized factor-list lengths, not exponents. -/
theorem evaluation_runFuel (L : ℕ) (ts : List (Term F))
    (hlen : ∀ t ∈ ts, t.2.length ≤ L) :
    ∃ cost, runFuel (budget ts.length L) (.terms ts []) = (.done (normalize ts []), cost) ∧
      totalCost cost ≤ budget ts.length L := by
  obtain ⟨k, c, ht, hb⟩ := terms_trace ts.length L ts [] hlen (by simp)
  have hw : k + totalCost c ≤ budget ts.length L := by
    unfold budget
    nlinarith [Nat.zero_le (8 * L * ts.length)]
  have hrun := ht.runFuel_done (budget ts.length L - k)
  rw [show k + (budget ts.length L - k) = budget ts.length L by omega] at hrun
  exact ⟨c, hrun, by omega⟩

/-- Aggregation preserves the represented polynomial, even without a layout premise. -/
theorem insertTerm_polynomial (c : F) (fs : List (ℕ × ℕ)) (out : List (Term F)) :
    sparsePolynomial (insertTerm c fs out) =
      C c * factorsPolynomial fs + sparsePolynomial out := by
  induction out with
  | nil => simp [insertTerm, sparsePolynomial]
  | cons t out ih =>
      rcases t with ⟨d, gs⟩
      by_cases he : fs = gs
      · subst gs
        by_cases hc : c + d = 0
        · have hz : C c * factorsPolynomial fs + C d * factorsPolynomial fs = 0 := by
            rw [← add_mul, ← map_add, hc, map_zero, zero_mul]
          simp only [insertTerm, ite_true, if_pos hc, sparsePolynomial]
          rw [← add_assoc, hz, zero_add]
        · simp only [insertTerm, ite_true, if_neg hc, sparsePolynomial, map_add, add_mul]
          ring
      · simp only [insertTerm, if_neg he, sparsePolynomial, ih]
        ac_rfl

/-- Folding the input into an accumulator preserves their sum. -/
theorem normalize_polynomial (ts out : List (Term F)) :
    sparsePolynomial (normalize ts out) = sparsePolynomial ts + sparsePolynomial out := by
  induction ts generalizing out with
  | nil => simp [normalize, sparsePolynomial]
  | cons t ts ih =>
      rcases t with ⟨c, fs⟩
      by_cases hc : c = 0
      · subst c
        simpa [normalize, sparsePolynomial] using ih out
      · simp only [normalize, if_neg hc, ih, insertTerm_polynomial, sparsePolynomial]
        ac_rfl

/-- All stored coefficients are nonzero and all exact factor-list keys are distinct. -/
def Normalized (ts : List (Term F)) : Prop :=
  (ts.map Prod.snd).Nodup ∧ ∀ t ∈ ts, t.1 ≠ 0

/-- A dense factor representation retains one fixed ordered list of distinct variables. -/
def DenseLayout (vars : List ℕ) (ts : List (Term F)) : Prop :=
  vars.Nodup ∧ ∀ t ∈ ts, t.2.map Prod.fst = vars

/-- Insertion only retains old keys or the inserted key. -/
theorem insertTerm_keys (c : F) (fs : List (ℕ × ℕ)) (out : List (Term F))
    (t : Term F) (ht : t ∈ insertTerm c fs out) :
    t.2 = fs ∨ t.2 ∈ out.map Prod.snd := by
  induction out with
  | nil =>
      have he : t = (c, fs) := by simpa [insertTerm] using ht
      exact Or.inl (congrArg Prod.snd he)
  | cons u out ih =>
      rcases u with ⟨d, gs⟩
      simp only [insertTerm] at ht
      split_ifs at ht with he hc
      · exact Or.inr (by simp [List.mem_map_of_mem ht])
      · rcases List.mem_cons.mp ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (by simp [List.mem_map_of_mem ht])
      · rcases List.mem_cons.mp ht with rfl | ht
        · exact Or.inr (by simp)
        · rcases ih ht with h | h
          · exact Or.inl h
          · exact Or.inr (by simp [h])

/-- Nonzero insertion preserves uniqueness and removes a key when its sum cancels. -/
theorem insertTerm_normalized (c : F) (fs : List (ℕ × ℕ)) (out : List (Term F))
    (hc : c ≠ 0) (hout : Normalized out) : Normalized (insertTerm c fs out) := by
  induction out with
  | nil => simpa [insertTerm, Normalized] using hc
  | cons u out ih =>
      rcases u with ⟨d, gs⟩
      obtain ⟨hkeys, hcoeff⟩ := hout
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hkeys
      have hd : d ≠ 0 := hcoeff (d, gs) (by simp)
      have htail : Normalized out := ⟨hnodup, fun t ht => hcoeff t (by simp [ht])⟩
      by_cases he : fs = gs
      · subst gs
        by_cases hz : c + d = 0
        · simpa [insertTerm, hz] using htail
        · simpa [insertTerm, hz, Normalized] using And.intro
            (List.nodup_cons.mpr ⟨hnot, hnodup⟩) (And.intro hz htail.2)
      · obtain ⟨hik, hic⟩ := ih htail
        have hn : gs ∉ (insertTerm c fs out).map Prod.snd := by
          intro h
          obtain ⟨t, ht, heq⟩ := List.mem_map.mp h
          rcases insertTerm_keys c fs out t ht with hk | hk
          · exact he (hk.symm.trans heq)
          · exact hnot (heq ▸ hk)
        simpa [insertTerm, he, Normalized] using And.intro
          (List.nodup_cons.mpr ⟨hn, hik⟩) (And.intro hd hic)

/-- The complete fold preserves the accumulator invariant. -/
theorem normalize_normalized (ts out : List (Term F)) (hout : Normalized out) :
    Normalized (normalize ts out) := by
  induction ts generalizing out with
  | nil => exact hout
  | cons t ts ih =>
      rcases t with ⟨c, fs⟩
      by_cases hc : c = 0
      · simpa [normalize, hc] using ih out hout
      · simpa [normalize, hc] using ih _ (insertTerm_normalized c fs out hc hout)

/-- The fold preserves every property of keys shared by input and accumulator. -/
theorem normalize_keys (P : List (ℕ × ℕ) → Prop) (ts out : List (Term F))
    (hts : ∀ t ∈ ts, P t.2) (hout : ∀ t ∈ out, P t.2) :
    ∀ t ∈ normalize ts out, P t.2 := by
  induction ts generalizing out with
  | nil => exact hout
  | cons u ts ih =>
      rcases u with ⟨c, fs⟩
      have htail : ∀ t ∈ ts, P t.2 := fun t ht => hts t (by simp [ht])
      simp only [normalize]
      split_ifs
      · exact ih out htail hout
      · apply ih _ htail
        intro t ht
        rcases insertTerm_keys c fs out t ht with hk | hk
        · rw [hk]
          exact hts (c, fs) (by simp)
        · obtain ⟨u, hu, heq⟩ := List.mem_map.mp hk
          rw [← heq]
          exact hout u hu

/-- Dense layouts survive aggregation, including coefficient cancellation. -/
theorem normalize_denseLayout (vars : List ℕ) (ts : List (Term F))
    (h : DenseLayout vars ts) : DenseLayout vars (normalize ts []) :=
  ⟨h.1, normalize_keys (fun fs => fs.map Prod.fst = vars) ts [] h.2 (by simp)⟩

/-- Semantic exponent vector; this specification is never evaluated by the machine. -/
noncomputable def factorExponents : List (ℕ × ℕ) → (ℕ →₀ ℕ)
  | [] => 0
  | (i, e) :: fs => Finsupp.single i e + factorExponents fs

omit [DecidableEq F] in
/-- Transport the explicit factors to the generic multivariate monomial representation. -/
theorem factorsPolynomial_eq_monomial (fs : List (ℕ × ℕ)) :
    factorsPolynomial (F := F) fs = monomial (factorExponents fs) 1 := by
  induction fs with
  | nil => simp [factorsPolynomial, factorExponents]
  | cons p fs ih =>
      rcases p with ⟨i, e⟩
      simp [factorsPolynomial, factorExponents, ih, X_pow_eq_monomial, monomial_mul]

private theorem factorExponents_of_absent (fs : List (ℕ × ℕ)) (i : ℕ)
    (h : i ∉ fs.map Prod.fst) : factorExponents fs i = 0 := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
      rcases p with ⟨j, e⟩
      simp only [List.map_cons, List.mem_cons, not_or] at h
      simp [factorExponents, Ne.symm h.1, ih h.2]

/-- Ordered distinct variables make dense exponent vectors injective, including zero entries. -/
theorem factorExponents_injective_of_layout (fs gs : List (ℕ × ℕ))
    (hvars : fs.map Prod.fst = gs.map Prod.fst) (hn : (fs.map Prod.fst).Nodup)
    (he : factorExponents fs = factorExponents gs) : fs = gs := by
  induction fs generalizing gs with
  | nil =>
      cases gs with
      | nil => rfl
      | cons q gs => simp at hvars
  | cons p fs ih =>
      rcases p with ⟨i, e⟩
      cases gs with
      | nil => simp at hvars
      | cons q gs =>
          rcases q with ⟨j, f⟩
          simp only [List.map_cons, List.cons.injEq] at hvars
          obtain ⟨rfl, hvars⟩ := hvars
          obtain ⟨hi, hn⟩ := List.nodup_cons.mp hn
          have hj : i ∉ gs.map Prod.fst := hvars ▸ hi
          have hef := congrArg (fun v : ℕ →₀ ℕ => v i) he
          simp only [factorExponents, Finsupp.add_apply, Finsupp.single_eq_same,
            factorExponents_of_absent fs i hi, factorExponents_of_absent gs i hj,
            add_zero] at hef
          subst f
          have htail : factorExponents fs = factorExponents gs := add_left_cancel he
          exact congrArg (List.cons (i, e)) (ih gs hvars hn htail)

omit [DecidableEq F] in
/-- Under the layout contract, normalized keys give distinct semantic monomials. -/
theorem normalized_monomials (vars : List ℕ) (out : List (Term F))
    (hn : Normalized out) (hl : DenseLayout vars out) :
    (out.map (fun t => factorExponents t.2)).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  have hp := List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp hn.1)
  apply hp.imp_of_mem
  intro a b ha hb hne he
  exact hne (factorExponents_injective_of_layout a.2 b.2
    ((hl.2 a ha).trans (hl.2 b hb).symm) (hl.2 a ha ▸ hl.1) he)

omit [DecidableEq F] in
private theorem coeff_sparse_of_absent (out : List (Term F)) (v : ℕ →₀ ℕ)
    (h : v ∉ out.map (fun t => factorExponents t.2)) : coeff v (sparsePolynomial out) = 0 := by
  induction out with
  | nil => simp [sparsePolynomial]
  | cons t out ih =>
      rcases t with ⟨c, fs⟩
      simp only [List.map_cons, List.mem_cons, not_or] at h
      simp [sparsePolynomial, factorsPolynomial_eq_monomial, C_mul_monomial,
        coeff_monomial, Ne.symm h.1, ih h.2]

omit [DecidableEq F] in
/-- Distinct semantic keys ensure each stored scalar is the actual polynomial coefficient. -/
theorem coeff_sparse_of_distinct (out : List (Term F))
    (hn : (out.map (fun t => factorExponents t.2)).Nodup) (t : Term F) (ht : t ∈ out) :
    coeff (factorExponents t.2) (sparsePolynomial out) = t.1 := by
  induction out with
  | nil => simp at ht
  | cons u out ih =>
      rcases u with ⟨c, fs⟩
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with rfl | ht
      · simp [sparsePolynomial, factorsPolynomial_eq_monomial, C_mul_monomial,
          coeff_sparse_of_absent out _ hnot]
      · have hne : factorExponents fs ≠ factorExponents t.2 := by
          intro he
          apply hnot
          simpa only [he] using List.mem_map_of_mem (f := fun t : Term F =>
            factorExponents t.2) ht
        simp [sparsePolynomial, factorsPolynomial_eq_monomial, C_mul_monomial,
          coeff_monomial, hne, ih hnodup ht]

/-- Every normalized dense term stores its true, nonzero coefficient in the original polynomial. -/
theorem normalize_coefficient (vars : List ℕ) (ts : List (Term F))
    (hl : DenseLayout vars ts) (t : Term F) (ht : t ∈ normalize ts []) :
    coeff (factorExponents t.2) (sparsePolynomial ts) = t.1 ∧ t.1 ≠ 0 := by
  have hn := normalize_normalized ts [] (by simp [Normalized])
  have hd := normalized_monomials vars _ hn (normalize_denseLayout vars ts hl)
  have hc := coeff_sparse_of_distinct _ hd t ht
  simpa [normalize_polynomial, sparsePolynomial] using And.intro hc (hn.2 t ht)

/-- The normalized dense keys are exactly the nonzero monomials of the original polynomial. -/
theorem normalize_coeff_ne_zero_iff (vars : List ℕ) (ts : List (Term F))
    (hl : DenseLayout vars ts) (v : ℕ →₀ ℕ) :
    coeff v (sparsePolynomial ts) ≠ 0 ↔
      ∃ t ∈ normalize ts [], factorExponents t.2 = v := by
  constructor
  · intro hc
    by_contra h
    have ha : v ∉ (normalize ts []).map (fun t => factorExponents t.2) := by
      simpa only [List.mem_map] using h
    have hz := coeff_sparse_of_absent (normalize ts []) v ha
    exact hc (by simpa [normalize_polynomial, sparsePolynomial] using hz)
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨he, hn⟩ := normalize_coefficient vars ts hl t ht
    exact he ▸ hn

/-- Actual bounded execution returns a polynomial-equivalent normalized dense representation. -/
theorem dense_runFuel (vars : List ℕ) (ts : List (Term F)) (hl : DenseLayout vars ts) :
    ∃ cost, runFuel (budget ts.length vars.length) (.terms ts []) =
        (.done (normalize ts []), cost) ∧
      totalCost cost ≤ budget ts.length vars.length ∧
      sparsePolynomial (normalize ts []) = sparsePolynomial ts ∧
      Normalized (normalize ts []) ∧ DenseLayout vars (normalize ts []) ∧
      ∀ t ∈ normalize ts [],
        coeff (factorExponents t.2) (sparsePolynomial ts) = t.1 ∧ t.1 ≠ 0 := by
  obtain ⟨cost, hr, hc⟩ := evaluation_runFuel vars.length ts (by
    intro t ht
    have h := congrArg List.length (hl.2 t ht)
    simpa using h.le)
  exact ⟨cost, hr, hc, by simp [normalize_polynomial, sparsePolynomial],
    normalize_normalized ts [] (by simp [Normalized]), normalize_denseLayout vars ts hl,
    normalize_coefficient vars ts hl⟩

end MvPolynomial.DenseNormalizeMachine
