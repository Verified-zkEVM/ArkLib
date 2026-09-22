/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Fri.Spec.Agreement

/-!
# Execution semantics of FRI queries

These lemmas evaluate the existing oracle verifier against arbitrary committed words.
No honesty or low-degree assumption is imposed on the intermediate oracles.
-/

namespace Fri.Spec

open OracleComp OracleSpec ProtocolSpec Domain Finset

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F} (s : Fin (k + 1) → ℕ+)

/-- A non-final word in the heterogeneous final oracle history. -/
def committedWord (o : ∀ j, FinalOracleStatement s ω j) (i : Fin (k + 1)) :
    (ω.subdomain (∑ j ∈ finRangeTo (k + 1) i.val, (s j).val)).toFinset → F :=
  cast (by
    simp [FinalOracleStatement, show i.val ≠ k + 1 by omega]
    rfl) (o i.castSucc)

/-- The words and the final polynomial determine the retained commitment history. -/
theorem oracleHistory_ext {o o' : ∀ j, FinalOracleStatement s ω j}
    (hw : ∀ i, committedWord s o i = committedWord s o' i)
    (hp : finalPolynomial s o = finalPolynomial s o') : o = o' := by
  funext j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · apply eq_of_heq
    exact (cast_heq _ _).symm.trans ((heq_of_eq hp).trans (cast_heq _ _))
  · apply eq_of_heq
    exact (cast_heq _ _).symm.trans ((heq_of_eq (hw i)).trans (cast_heq _ _))

/-- Ambient-field extension of the committed history; values outside each word's domain
are immaterial. The last entry is evaluation of the transmitted polynomial. -/
def committedFunction (o : ∀ j, FinalOracleStatement s ω j)
    (i : Fin (k + 2)) (x : F) : F :=
  if h : i.val < k + 1 then
    if hx : x ∈ (ω.subdomain (foldingPrefix s i)).toFinset then
      committedWord s o ⟨i.val, h⟩ ⟨x, hx⟩
    else 0
  else (finalPolynomial s o).eval x

@[simp]
theorem committedFunction_castSucc (o : ∀ j, FinalOracleStatement s ω j)
    (i : Fin (k + 1))
    (x : (ω.subdomain (foldingPrefix s i.castSucc)).toFinset) :
    committedFunction s o i.castSucc x.val = committedWord s o i x := by
  simp only [committedFunction, Fin.val_castSucc, i.isLt, ↓reduceDIte, x.property]
  rfl

@[simp]
theorem committedFunction_last (o : ∀ j, FinalOracleStatement s ω j) (x : F) :
    committedFunction s o (Fin.last (k + 1)) x = (finalPolynomial s o).eval x := by
  simp [committedFunction]

namespace QueryRound

omit [Fintype F] in
@[simp]
theorem queryBlock_length (hs : (∑ j, (s j).val) ≤ n) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset) :
    (queryBlock s hs i x).length = 2 ^ (s i).val := by
  have hi : (s i).val ≤ n :=
    (Finset.single_le_sum (f := fun j ↦ (s j : ℕ)) (by simp) (by simp)).trans hs
  simp only [queryBlock, FftDomain.toList, List.length_map, List.length_finRange]
  exact congrArg (fun a ↦ 2 ^ a) (Nat.sub_sub_self hi)

omit [Fintype F] in
/-- Every point in the enumerated block has the same image under folding. -/
theorem queryBlock_pow (hs : (∑ j, (s j).val) ≤ n) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset)
    (q : (ω.subdomain (∑ j ∈ finRangeTo (k + 1) i.val, (s j).val)).toFinset)
    (hq : q ∈ queryBlock s hs i x) :
    q.val ^ (2 ^ (s i).val) = (queryPoint s hs i x).val ^ (2 ^ (s i).val) := by
  have hi : (s i).val ≤ n :=
    (Finset.single_le_sum (f := fun j ↦ (s j : ℕ)) (by simp) (by simp)).trans hs
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
  obtain ⟨j, hj⟩ := FftDomain.mem_toFinset_iff_mem.mp r.property
  have hroot : r.val ^ (2 ^ (s i).val) = 1 := by
    rw [← hj]
    have hn : (2 ^ (s i).val) • j = 0 := by
      have hcard := card_nsmul_eq_zero (x := j)
      simp only [Fintype.card_fin] at hcard
      change 2 ^ (n - (n - (s i).val)) • j = 0 at hcard
      rw [Nat.sub_sub_self hi] at hcard
      exact hcard
    rw [← FftDomainClass.apply_nsmul, hn, FftDomainClass.apply_zero_eq_one]
  change (r.val * (queryPoint s hs i x).val) ^ _ = _
  rw [mul_pow, hroot, one_mul]

omit [Fintype F] in
/-- The executable query enumeration contains each point of the folding block once. -/
theorem queryBlock_nodup (hs : (∑ j, (s j).val) ≤ n) (i : Fin (k + 1))
    (x : (ω.subdomain 0).toFinset) : (queryBlock s hs i x).Nodup := by
  unfold queryBlock FftDomain.toList
  rw [List.map_map]
  apply List.Nodup.map _ (List.nodup_finRange _)
  intro a b hab
  apply FftDomain.injective (ω := ω.toFftDomain.subdomain (n - (s i).val))
  apply mul_right_cancel₀ (CosetFftDomainClass.ne_zero_dep (queryPoint s hs i x))
  exact congrArg Subtype.val hab

private theorem cast_query {ι : Type} {spec : OracleSpec ι} {A B : Type}
    (h : A = B) (h' : OracleQuery spec A = OracleQuery spec B) (q : OracleQuery spec A) :
    cast h' q = cast h <$> q := by
  subst B
  exact (id_map q).symm

@[simp]
theorem eval_queryCodeword (o : ∀ j, FinalOracleStatement s ω j) (i : Fin (k + 1))
    (x : (ω.subdomain (∑ j ∈ finRangeTo (k + 1) i.val, (s j).val)).toFinset) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (queryCodeword k s x) = committedWord s o i x := by
  unfold queryCodeword
  rw [cast_query (range_lem₁ s _)]
  rw [simulateQ_query]
  dsimp [OracleInterface.simOracle0, OracleInterface.answer, finalOracleStatementInterface]
  unfold finalOracleStatementInterface
  simp only [finRangeTo, show i.val ≠ k + 1 by omega, ReaderT.run, read, readThe,
    MonadReaderOf.read, ReaderT.read, Lean.Elab.WF.paramLet, ↓reduceDIte, cast_cast,
    bind_pure_comp, committedWord]
  simp only [Functor.map, Pure.pure]
  apply eq_of_heq
  apply HEq.trans (cast_heq _ _)
  apply HEq.trans (cast_heq _ _)
  exact heq_of_eq (congr_heq ((cast_heq _ _).trans (cast_heq _ _).symm) (cast_heq _ _))

@[simp]
theorem eval_getConst (o : ∀ j, FinalOracleStatement s ω j) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (getConst k s) = finalPolynomial s o := by
  unfold getConst
  rw [cast_query (range_lem₂ s _)]
  rw [simulateQ_query]
  dsimp [OracleInterface.simOracle0, OracleInterface.answer, finalOracleStatementInterface]
  unfold finalOracleStatementInterface
  simp only [finRangeTo, Fin.val_last, ReaderT.run, read, readThe,
    MonadReaderOf.read, ReaderT.read, Lean.Elab.WF.paramLet, ↓reduceDIte, cast_cast,
    bind_pure_comp, finalPolynomial]
  simp only [Functor.map, Pure.pure]
  exact eq_of_heq ((cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm))

/-- Evaluate a local check using precisely the committed answers and the FFT block. -/
theorem eval_queryNext (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j)
    (i : Fin (k + 1)) (x : (ω.subdomain 0).toFinset) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (queryNext s hs (finalPolynomial s o) i x) =
      committedFunction s o i.succ (x.val ^ (2 ^ foldingPrefix s i.succ)) := by
  have hpow : (queryPoint s hs i x).val ^ (2 ^ (s i).val) =
      x.val ^ (2 ^ foldingPrefix s i.succ) := by
    rw [foldingPrefix_succ, pow_add, pow_mul]
    rfl
  unfold queryNext
  split_ifs with hi
  · rw [eval_queryCodeword]
    have hx : x.val ^ (2 ^ foldingPrefix s i.succ) ∈
        (ω.subdomain (foldingPrefix s i.succ)).toFinset :=
      CosetFftDomainClass.pow_mem_subdomain_of_mem_subdomain_0_toFinset
        ((foldingPrefix_le s i.succ).trans hs) x.property
    simp only [committedFunction, Fin.val_succ, show i.val + 1 < k + 1 by omega,
      ↓reduceDIte, hx]
    congr 1
    exact Subtype.ext hpow
  · have hiLast : i = Fin.last k := Fin.ext (by simp; omega)
    subst i
    simp only [simulateQ_pure, Fin.succ_last, committedFunction_last]
    rw [hpow]
    rfl

/-- Evaluate a local check using precisely the committed answers and the FFT block. -/
theorem eval_checkRound (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (p : CompPoly.CPolynomial F)
    (α : F) (i : Fin (k + 1)) (x : (ω.subdomain 0).toFinset) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (checkRound s hs p α i x) =
    RoundConsistency.roundConsistencyCheck α
      ((queryBlock s hs i x).map (fun q ↦ (q.val, committedWord s o i q))).get
      (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
        (queryNext s hs p i x)) := by
  simp only [checkRound, finRangeTo, bind_pure_comp, simulateQ_bind, simulateQ_list_mapM,
    simulateQ_map, eval_queryCodeword]
  change (List.mapM (m := Id) (fun q ↦ (q.val, committedWord s o i q))
    (queryBlock s hs i x) >>= fun pts ↦
      RoundConsistency.roundConsistencyCheck α pts.get _) = _
  rw [show List.mapM (m := Id) (fun q ↦ (q.val, committedWord s o i q))
      (queryBlock s hs i x) =
      (queryBlock s hs i x).map (fun q ↦ (q.val, committedWord s o i q)) from
    List.mapM_pure]
  rfl

/-- The actual local verifier accepts exactly when the corresponding algebraic fold agrees. -/
theorem eval_checkRound_eq_true_iff (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (p : CompPoly.CPolynomial F)
    (α : F) (i : Fin (k + 1)) (x : (ω.subdomain 0).toFinset) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (checkRound s hs p α i x) = true ↔
    ProximityGap.foldValue
      (ω.subdomain (∑ j ∈ finRangeTo (k + 1) i.val, (s j).val))
      (fun z ↦ committedWord s o i
        ⟨ω.subdomain (∑ j ∈ finRangeTo (k + 1) i.val, (s j).val) z,
          CosetFftDomain.mem_toFinset_self⟩)
      (s i).val α ((queryPoint s hs i x).val ^ (2 ^ (s i).val)) =
      simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
        (queryNext s hs p i x) := by
  rw [eval_checkRound]
  let qs := queryBlock s hs i x
  have h := RoundConsistency.roundConsistencyCheck_eq_foldValue_of_domainPoints
    (ω.subdomain (∑ j ∈ finRangeTo (k + 1) i.val, (s j).val))
    (committedWord s o i) (queryBlock_length s hs i x) qs.get
    (List.nodup_iff_injective_get.mp (queryBlock_nodup s hs i x))
    ((queryPoint s hs i x).val ^ (2 ^ (s i).val)) α
    (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (queryNext s hs p i x))
    (fun j ↦ queryBlock_pow s hs i x (qs.get j) (List.get_mem _ _))
  rw [RoundConsistency.roundConsistencyCheck_map_get]
  exact h

/-- The executable check, expressed in the original-domain coordinates used by the
backwards agreement induction. -/
theorem eval_checkRound_iff_schedule (hs : (∑ j, (s j).val) ≤ n)
    (o : ∀ j, FinalOracleStatement s ω j) (α : F)
    (i : Fin (k + 1)) (x : (ω.subdomain 0).toFinset) :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement s ω) o)
      (checkRound s hs (finalPolynomial s o) α i x) = true ↔
    ProximityGap.foldValue (ω.subdomain (foldingPrefix s i.castSucc))
      (fun z ↦ committedFunction s o i.castSucc
        (ω.subdomain (foldingPrefix s i.castSucc) z))
      (s i).val α (x.val ^ (2 ^ foldingPrefix s i.succ)) =
      committedFunction s o i.succ (x.val ^ (2 ^ foldingPrefix s i.succ)) := by
  rw [eval_checkRound_eq_true_iff, eval_queryNext]
  have hpow : (queryPoint s hs i x).val ^ (2 ^ (s i).val) =
      x.val ^ (2 ^ foldingPrefix s i.succ) := by
    rw [foldingPrefix_succ, pow_add, pow_mul]
    rfl
  rw [hpow]
  have hw : (fun z ↦ committedWord s o i
      ⟨ω.subdomain (foldingPrefix s i.castSucc) z, CosetFftDomain.mem_toFinset_self⟩) =
      (fun z ↦ committedFunction s o i.castSucc
        (ω.subdomain (foldingPrefix s i.castSucc) z)) := by
    funext z
    exact (committedFunction_castSucc s o i
      ⟨_, CosetFftDomain.mem_toFinset_self⟩).symm
  exact Iff.of_eq (congrArg (fun f ↦
    ProximityGap.foldValue (ω.subdomain (foldingPrefix s i.castSucc)) f (s i).val α
      (x.val ^ (2 ^ foldingPrefix s i.succ)) =
      committedFunction s o i.succ (x.val ^ (2 ^ foldingPrefix s i.succ))) hw)

end QueryRound

end Fri.Spec
