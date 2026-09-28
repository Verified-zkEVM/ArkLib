/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.ProofSystem.Fri.Spec.General
public import ArkLib.ProofSystem.Fri.Spec.Execution
public import ArkLib.OracleReduction.Security.BadEvents

/-!
# The chronology of FRI commitments and challenges

These indices belong to the existing composed protocol, not to a separate execution model.
In particular each word is fixed strictly before the challenge used to fold it.
-/

@[expose] public section

namespace Fri.Spec

open OracleComp OracleSpec ProtocolSpec Domain Finset

variable {F : Type} [NonBinaryField F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (l : ℕ)

/-- Challenge of a non-final folding round in the complete protocol. -/
def nonfinalChallenge (i : Fin k) : (pSpec k (ω := ω) s l).ChallengeIdx :=
  ChallengeIdx.inl (ChallengeIdx.inl (sigmaChallengeIdxToSeqCompose
    (pSpec := fun j ↦ FoldPhase.pSpec (ω := ω) s j) i ⟨0, rfl⟩))

/-- Commitment sent after a non-final folding challenge. -/
def nonfinalMessage (i : Fin k) : (pSpec k (ω := ω) s l).MessageIdx :=
  MessageIdx.inl (MessageIdx.inl (sigmaMessageIdxToSeqCompose
    (pSpec := fun j ↦ FoldPhase.pSpec (ω := ω) s j) i ⟨1, rfl⟩))

/-- Last folding challenge, preceding the final polynomial. -/
def finalChallenge : (pSpec k (ω := ω) s l).ChallengeIdx :=
  ChallengeIdx.inl (ChallengeIdx.inr ⟨0, rfl⟩)

/-- The final polynomial message. -/
def finalMessage : (pSpec k (ω := ω) s l).MessageIdx :=
  MessageIdx.inl (MessageIdx.inr ⟨1, rfl⟩)

/-- The query vector is sampled only after every commitment. -/
def queryChallenge : (pSpec k (ω := ω) s l).ChallengeIdx :=
  ChallengeIdx.inr ⟨0, rfl⟩

@[simp]
theorem nonfinalChallenge_val (i : Fin k) :
    (nonfinalChallenge (ω := ω) s l i).val.val = 2 * i.val := by
  simp [nonfinalChallenge, ChallengeIdx.inl, sigmaChallengeIdxToSeqCompose,
    Fin.val_embedSum, mul_comm]

@[simp]
theorem nonfinalMessage_val (i : Fin k) :
    (nonfinalMessage (ω := ω) s l i).val.val = 2 * i.val + 1 := by
  simp [nonfinalMessage, MessageIdx.inl, sigmaMessageIdxToSeqCompose,
    Fin.val_embedSum, mul_comm]

@[simp]
theorem finalChallenge_val : (finalChallenge (ω := ω) s l).val.val = 2 * k := by
  simp [finalChallenge, ChallengeIdx.inl, ChallengeIdx.inr, Fin.vsum_eq_univ_sum, mul_comm]

@[simp]
theorem finalMessage_val : (finalMessage (ω := ω) s l).val.val = 2 * k + 1 := by
  simp [finalMessage, MessageIdx.inl, MessageIdx.inr, Fin.vsum_eq_univ_sum, mul_comm]

@[simp]
theorem queryChallenge_val : (queryChallenge (ω := ω) s l).val.val = 2 * k + 2 := by
  simp [queryChallenge, ChallengeIdx.inr, Fin.vsum_eq_univ_sum, mul_comm]

@[simp]
theorem nonfinalChallenge_type (i : Fin k) :
    (pSpec k (ω := ω) s l).Challenge (nonfinalChallenge s l i) = F := by
  simp [nonfinalChallenge, ChallengeIdx.inl, sigmaChallengeIdxToSeqCompose,
    Challenge, pSpec, pSpecFold, ProtocolSpec.append, ProtocolSpec.seqCompose, FoldPhase.pSpec]

@[simp]
theorem finalChallenge_type :
    (pSpec k (ω := ω) s l).Challenge (finalChallenge s l) = F := by
  simp [finalChallenge, ChallengeIdx.inl, ChallengeIdx.inr,
    Challenge, pSpec, ProtocolSpec.append, FinalFoldPhase.pSpec]

@[simp]
theorem queryChallenge_type :
    (pSpec k (ω := ω) s l).Challenge (queryChallenge s l) =
      (Fin l → (ω.subdomain 0).toFinset) := by
  simp [queryChallenge, ChallengeIdx.inr,
    Challenge, pSpec, ProtocolSpec.append, QueryRound.pSpec]

@[simp]
theorem nonfinalMessage_type (i : Fin k) :
    (pSpec k (ω := ω) s l).Message (nonfinalMessage s l i) =
      ((ω.subdomain (∑ j ∈ finRangeTo (k + 1) (i.val + 1), (s j).val)).toFinset → F) := by
  simp [nonfinalMessage, MessageIdx.inl, sigmaMessageIdxToSeqCompose,
    Message, pSpec, pSpecFold, ProtocolSpec.append, ProtocolSpec.seqCompose, FoldPhase.pSpec]
  rfl

@[simp]
theorem finalMessage_type :
    (pSpec k (ω := ω) s l).Message (finalMessage s l) = CompPoly.CPolynomial F := by
  simp [finalMessage, MessageIdx.inl, MessageIdx.inr,
    Message, pSpec, ProtocolSpec.append, FinalFoldPhase.pSpec]

/-- Uniform indexing of all folding challenges, including the final fold. -/
def foldChallenge (i : Fin (k + 1)) : (pSpec k (ω := ω) s l).ChallengeIdx :=
  if h : i.val < k then nonfinalChallenge s l ⟨i.val, h⟩ else finalChallenge s l

@[simp]
theorem foldChallenge_val (i : Fin (k + 1)) :
    (foldChallenge (ω := ω) s l i).val.val = 2 * i.val := by
  unfold foldChallenge
  split_ifs with h
  · simp
  · have hi : i.val = k := by omega
    simp [hi]

@[simp]
theorem foldChallenge_type (i : Fin (k + 1)) :
    (pSpec k (ω := ω) s l).Challenge (foldChallenge s l i) = F := by
  unfold foldChallenge
  split_ifs
  · exact nonfinalChallenge_type s l _
  · exact finalChallenge_type s l

/-- Every verifier move is either a folding challenge or the final query vector. -/
theorem challenge_cases (j : (pSpec k (ω := ω) s l).ChallengeIdx) :
    (∃ i, j = foldChallenge s l i) ∨ j = queryChallenge s l := by
  obtain ⟨j, rfl⟩ := (ChallengeIdx.sumEquiv
    (pSpec₁ := pSpecFold k (ω := ω) s ++ₚ FinalFoldPhase.pSpec F)
    (pSpec₂ := QueryRound.pSpec (ω := ω) l)).surjective j
  rcases j with j | j
  · obtain ⟨j, rfl⟩ := (ChallengeIdx.sumEquiv
      (pSpec₁ := pSpecFold k (ω := ω) s)
      (pSpec₂ := FinalFoldPhase.pSpec F)).surjective j
    rcases j with j | j
    · obtain ⟨⟨i, j⟩, rfl⟩ :=
        (seqComposeChallengeEquiv (fun i ↦ FoldPhase.pSpec (ω := ω) s i)).surjective j
      have hj : j = ⟨0, rfl⟩ := by
        rcases j with ⟨j, hj⟩
        fin_cases j
        · rfl
        · change Direction.P_to_V = Direction.V_to_P at hj
          contradiction
      subst j
      refine Or.inl ⟨i.castSucc, ?_⟩
      simp only [foldChallenge, Fin.val_castSucc, dite_eq_left i.isLt]
      rfl
    · have hj : j = ⟨0, rfl⟩ := by
        rcases j with ⟨j, hj⟩
        fin_cases j
        · rfl
        · change Direction.P_to_V = Direction.V_to_P at hj
          contradiction
      subst j
      refine Or.inl ⟨Fin.last k, ?_⟩
      simp only [foldChallenge, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
      rfl
  · have hj : j = ⟨0, rfl⟩ := Subtype.ext (Fin.fin_one_eq_zero j.val)
    subst j
    exact Or.inr rfl

/-- Different folding rounds occupy different challenge positions. -/
theorem foldChallenge_injective : Function.Injective (foldChallenge (ω := ω) s l) := by
  intro i j hij
  have h := congrArg (fun x : (pSpec k (ω := ω) s l).ChallengeIdx ↦ x.val.val) hij
  simp only [foldChallenge_val] at h
  apply Fin.ext
  omega

@[simp]
theorem foldChallenge_ne_query (i : Fin (k + 1)) :
    foldChallenge (ω := ω) s l i ≠ queryChallenge s l := by
  intro h
  have hval := congrArg (fun x : (pSpec k (ω := ω) s l).ChallengeIdx ↦ x.val.val) h
  simp only [foldChallenge_val, queryChallenge_val] at hval
  omega

/-- Read an already sampled folding challenge from a partial transcript. -/
def readFoldChallenge {m : Fin (((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1) + 1)}
    (tr : (pSpec k (ω := ω) s l).Transcript m) (i : Fin (k + 1))
    (hi : 2 * i.val < m.val) : F :=
  cast (foldChallenge_type s l i)
    (tr.read (foldChallenge s l i).val (by simpa only [foldChallenge_val] using hi))

/-- Read the word committed before a folding challenge. The first word is the input;
every later word is the preceding prover message, strictly before position `2 * i`. -/
def readWord (f : (ω.subdomain 0).toFinset → F)
    {m : Fin (((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1) + 1)}
    (tr : (pSpec k (ω := ω) s l).Transcript m) (i : Fin (k + 1))
    (hi : 2 * i.val ≤ m.val) :
    (ω.subdomain (foldingPrefix s i.castSucc)).toFinset → F :=
  if hzero : i.val = 0 then
    cast (congrArg (fun a ↦ (ω.subdomain a).toFinset → F)
      (show 0 = foldingPrefix s i.castSucc by
        have hi0 : i = 0 := Fin.ext hzero
        subst i
        exact (foldingPrefix_zero s).symm)) f
  else
    let j : Fin k := ⟨i.val - 1, by omega⟩
    let w := cast (nonfinalMessage_type s l j)
      (tr.read (nonfinalMessage s l j).val (by
        rw [nonfinalMessage_val]
        dsimp only [j]
        omega))
    cast (congrArg (fun a ↦ (ω.subdomain a).toFinset → F) (show
        ∑ z ∈ finRangeTo (k + 1) (j.val + 1), (s z).val =
        ∑ z ∈ finRangeTo (k + 1) i.val, (s z).val
      from by rw [show j.val + 1 = i.val by dsimp [j]; omega])) w

/-- Reading a fixed word is unaffected by a later message or challenge. -/
theorem readWord_concat (f : (ω.subdomain 0).toFinset → F)
    {m : Fin ((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1)}
    (tr : (pSpec k (ω := ω) s l).Transcript m.castSucc)
    (msg : (pSpec k (ω := ω) s l).«Type» m) (i : Fin (k + 1))
    (hi : 2 * i.val ≤ m.val) :
    readWord s l f (tr.concat msg) i (by simp only [Fin.val_succ]; omega) =
      readWord s l f tr i hi := by
  unfold readWord
  split_ifs with hzero
  · rfl
  · have hj : (nonfinalMessage (ω := ω) s l ⟨i.val - 1, by omega⟩).val.val < m.val := by
      rw [nonfinalMessage_val]
      dsimp only
      omega
    dsimp only
    congr 1
    congr 1
    exact Transcript.read_concat_lt tr msg _ hj

@[simp]
theorem readFoldChallenge_concat (i : Fin (k + 1))
    (tr : (pSpec k (ω := ω) s l).Transcript (foldChallenge s l i).val.castSucc)
    (α : (pSpec k (ω := ω) s l).Challenge (foldChallenge s l i)) :
    readFoldChallenge s l (tr.concat α) i (by simp) = cast (foldChallenge_type s l i) α := by
  unfold readFoldChallenge
  rw [Transcript.read_concat_last]

/-- Restricting a transcript after a word's commitment preserves that word. -/
@[simp]
theorem readWord_restrict (f : (ω.subdomain 0).toFinset → F)
    {a b : Fin (((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1) + 1)}
    (hab : a.val ≤ b.val) (tr : (pSpec k (ω := ω) s l).Transcript b)
    (i : Fin (k + 1)) (hi : 2 * i.val ≤ a.val) :
    readWord s l f (tr.restrict hab) i hi = readWord s l f tr i (hi.trans hab) := by
  unfold readWord
  split_ifs <;> rfl

/-- A challenge's value is preserved by taking any prefix that already contains it. -/
@[simp]
theorem readFoldChallenge_restrict
    {a b : Fin (((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1) + 1)}
    (hab : a.val ≤ b.val) (tr : (pSpec k (ω := ω) s l).Transcript b)
    (i : Fin (k + 1)) (hi : 2 * i.val < a.val) :
    readFoldChallenge s l (tr.restrict hab) i hi =
      readFoldChallenge s l tr i (hi.trans_le hab) := rfl

/-- The final polynomial is a prover message fixed before the query vector. -/
def readFinalPolynomial
    {m : Fin (((Fin.vsum fun (_ : Fin k) ↦ 2) + 2 + 1) + 1)}
    (tr : (pSpec k (ω := ω) s l).Transcript m) (hi : 2 * k + 1 < m.val) :
    CompPoly.CPolynomial F :=
  cast (finalMessage_type s l)
    (tr.read (finalMessage s l).val (by simpa only [finalMessage_val] using hi))

variable [Fintype F]

/-- The retained commitment history at the start of the query phase. -/
def queryHistory (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc) :
    ∀ j, FinalOracleStatement s ω j := fun j ↦
  if h : j.val = k + 1 then
    cast (by simp only [FinalOracleStatement, h, ↓reduceIte])
      (readFinalPolynomial s l tr (by simp))
  else
    let i : Fin (k + 1) := ⟨j.val, by omega⟩
    cast (by simp only [FinalOracleStatement, h, ↓reduceIte]; rfl)
      (readWord s l f tr i (by simp only [Fin.val_castSucc, queryChallenge_val]; dsimp [i]; omega))

/-- The challenge vector at the start of the query phase. -/
def queryFoldChallenges
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc) :
    FinalStatement F k := fun i ↦
  readFoldChallenge s l tr i (by simp only [Fin.val_castSucc, queryChallenge_val]; omega)

@[simp]
theorem committedWord_queryHistory (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc)
    (i : Fin (k + 1)) :
    committedWord s (queryHistory s l f tr) i =
      readWord s l f tr i (by simp only [Fin.val_castSucc, queryChallenge_val]; omega) := by
  unfold committedWord queryHistory
  simp only [Fin.val_castSucc, show i.val ≠ k + 1 by omega, ↓reduceDIte]
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

@[simp]
theorem finalPolynomial_queryHistory (f : (ω.subdomain 0).toFinset → F)
    (tr : (pSpec k (ω := ω) s l).Transcript (queryChallenge (ω := ω) s l).val.castSucc) :
    finalPolynomial s (queryHistory s l f tr) = readFinalPolynomial s l tr (by simp) := by
  unfold finalPolynomial queryHistory
  simp only [Fin.val_last, ↓reduceDIte]
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

end Fri.Spec
