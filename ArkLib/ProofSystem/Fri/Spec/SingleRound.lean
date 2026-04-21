/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/


import ArkLib.Data.CodingTheory.ReedSolomon.FftDomain
import ArkLib.OracleReduction.Basic
import CompPoly.Fields.Basic
import ArkLib.ProofSystem.Fri.RoundConsistency
import ArkLib.ToMathlib.Finset.Basic

/-!
# The FRI protocol

  We describe the FRI oracle reduction as a composition of many single rounds, and a final
  (zero-interaction) query round where the oracle verifier makes all queries to all received oracle
  codewords.

  This formalisation tries to encompass all of the generalisations of the FRI
  low-degree test covered in [FRI1216].

## References

* [Haböck, U., *A summary on the FRI low degree test*][FRI1216]

 -/

namespace Fri

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset NNReal

namespace Spec

/- FRI parameters:
   - `F` a non-binary finite field.
   - `D` the cyclic subgroup of order `2 ^ n` we will to construct the evaluation domains.
   - `x` the element of `Fˣ` we will use to construct our evaluation domain.
   - `k` the number of, non final, folding rounds the protocol will run.
   - `s` the "folding degree" of each round,
         a folding degree of `1` this corresponds to the standard "even-odd" folding.
   - `d` the degree bound on the final polynomial returned in the final folding round.
   - `domain_size_cond`, a proof that the initial evaluation domain is large enough to test
      for proximity of a polynomial of appropriate degree.
  - `i` the index of the current folding round.
-/

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ} 
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (domain_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) (i : Fin k)
variable {ω : ReedSolomon.SmoothCosetFftDomain n F}


lemma round_bound {n k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+}
    (domain_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) :
  (∑ i, (s i).1) ≤ n := by
    have : 2 ^ (∑ i, (s i).1) ≤ 2 ^ n :=
      le_of_mul_le_of_one_le_left domain_size_cond
        (Nat.zero_lt_of_ne_zero (Nat.ne_zero_of_lt d.2))
    rw [Nat.pow_le_pow_iff_right (by decide)] at this
    exact this


/-- For the `i`-th round of the protocol, the input statement is equal to the challenges sent from
    rounds `0` to `i - 1`. After the `i`-th round, we append the `i`-th challenge to the statement.
-/
@[reducible]
def Statement (F : Type) (i : Fin (k + 1)) : Type := Fin i.val → F

@[reducible]
def FinalStatement (F : Type) (k : ℕ) : Type := Fin (k + 1) → F

/-- For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the
  beginning purported codeword, and `i` more for each of the rounds `0` to `i - 1`. After the `i`-th
  round, we append the `i`-th message sent by the prover to the oracle statement. -/
@[reducible]
def OracleStatement {F : Type} [Field F] [DecidableEq F] [Fintype F]
  (ω : ReedSolomon.SmoothCosetFftDomain n F)
  (i : Fin (k + 1)) : Fin (i.val + 1) → Type :=
  fun j ↦
    (ω.subdomainNatReversed (∑ j' ∈ finRangeTo (k + 1) j.1, s j')).toFinset
    → F

@[reducible]
def FinalOracleStatement
  {F : Type} [Field F] [DecidableEq F] [Fintype F]
  (ω : ReedSolomon.SmoothCosetFftDomain n F)
  : Fin (k + 2) → Type :=
  fun j ↦
    if j.1 = k + 1
    then F[X]
    else ((ω.subdomainNatReversed (∑ j' ∈ finRangeTo _ j.1, (s j').1)).toFinset → F)

/-- The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in
  the oracle statement. -/
@[reducible]
noncomputable def Witness (F : Type) [NonBinaryField F] {k : ℕ}
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (i : Fin (k + 2)) :=
  F⦃< 2^((∑ j', (s j').1) - (∑ j' ∈ finRangeTo _ i.1, (s j').1)) * d⦄[X]

private lemma witness_lift {F : Type} [NonBinaryField F]
  {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+} {p : F[X]} {α : F} {i : Fin (k + 1)} :
    p ∈ Witness F s d i.castSucc →
      FoldingPolynomial.polyFold p (2 ^ (s i).1) α ∈ Witness F s d i.succ := by
  intro deg_bound
  unfold Witness at deg_bound ⊢
  rw [Polynomial.mem_degreeLT] at deg_bound ⊢
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Fin.val_succ] at deg_bound ⊢
  by_cases h : p = 0
  · subst h
    rw [FoldingPolynomial.polyFold_zero_eq_zero, degree_zero]
    exact WithBot.bot_lt_coe _
  · by_cases h' : FoldingPolynomial.polyFold p (2 ^ (s i).1) α = 0
    · rw [h', degree_zero]
      exact WithBot.bot_lt_coe _
    · erw [Polynomial.degree_eq_natDegree h, WithBot.coe_lt_coe] at deg_bound
      erw [Polynomial.degree_eq_natDegree h', WithBot.coe_lt_coe]
      norm_cast at deg_bound ⊢
      have : 2 ^ (s i).1 > 0 := by
        simp only [gt_iff_lt, Nat.ofNat_pos, pow_pos]
      apply lt_of_le_of_lt FoldingPolynomial.polyFold_natDegree_le
      have arith {a b c : ℕ} (h : b ≥ c) (h' : a ≤ c) : a + (b - c) = b - (c - a) := by
        rw [Nat.sub_sub_right b h', Nat.sub_add_comm h, Nat.add_comm]
      rw [Iff.symm (Nat.mul_lt_mul_left this)]
      apply lt_of_le_of_lt (Nat.mul_div_le _ _)
      rw [←mul_assoc, ←pow_add, arith]
      · convert deg_bound
        rw [sum_finRangeTo_add_one]
        simp
      · simp only [ge_iff_le]
        apply sum_le_univ_sum_of_nonneg
        simp
      · apply Finset.single_le_sum (f := fun j ↦ ↑(s j)) (fun _ _ => Nat.zero_le _)
        simp only [finRangeTo, List.mem_toFinset]
        apply List.mem_take_iff_getElem.mpr
        use i.1
        use
          (by
            have := i.2
            simp only [List.length_finRange, Nat.add_min_add_right, gt_iff_lt]
            by_cases h : i.1 = 0
            · rw [h]
              simp
            · have : 1 ≤ i.1 := by omega
              refine (Nat.sub_lt_iff_lt_add this).mp ?_
              rw [Nat.lt_min]
              omega
          )
        simp

instance {i : Fin (k + 1)} : ∀ j, OracleInterface (OracleStatement s ω i j) :=
  fun _ ↦ inferInstance

instance finalOracleStatementInterface :
  ∀ j, OracleInterface (FinalOracleStatement s ω j) := fun j ↦
  { Query := if j = k + 1 then Unit else (ω.subdomainNatReversed (∑ j' ∈ finRangeTo _ j.1, s j')).toFinset
    toOC.spec := fun _ ↦ if j = k + 1 then F[X] else F
    toOC.impl := fun q ↦ do
      if h : j = k + 1 then
        let st : F[X] := cast (by simp [FinalOracleStatement, h]) (← read)
        return cast (by simp [h]) st
      else
        let st : (ω.subdomainNatReversed (∑ j' ∈ finRangeTo _ j.1, s j')).toFinset
          → F :=
          cast (by {
            simp [FinalOracleStatement, h]
            rfl
          }) (← read)
        let pt : (ω.subdomainNatReversed (∑ j' ∈ finRangeTo _ j.1, s j')).toFinset :=
          cast (by {
            simp [Domain, h]
          }) q
        return cast (by simp [h]) (st pt) }

@[simp]
lemma range_lem₁ {i : Fin (k + 1)} (q) :
    [FinalOracleStatement s ω]ₒ.Range ⟨⟨i.1, Nat.lt_succ_of_lt i.2⟩, q⟩ = F := by
  unfold OracleSpec.Range FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query OracleInterface.Response
  unfold finalOracleStatementInterface
  simp [Nat.ne_of_lt i.2]

@[simp]
lemma range_lem₂ (q) : [FinalOracleStatement s ω]ₒ.Range ⟨(Fin.last (k + 1)), q⟩ = F[X] := by
  unfold OracleSpec.Range FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query OracleInterface.Response
  unfold finalOracleStatementInterface
  simp

@[simp]
lemma query_lem (j) :
    (finalOracleStatementInterface (ω := ω) s j).Query =
      if j = k + 1 then Unit else (ω.subdomainNatReversed (∑ j' ∈ finRangeTo _ j.1, s j')).toFinset := by
  rfl

-- omit [Finite F] in
-- @[simp]
-- lemma domain_lem₂ :
--   [FinalOracleStatement D x s]ₒ.domain (Fin.last (k + 1)) = Unit := by
--   unfold OracleSpec.domain FinalOracleStatement OracleInterface.toOracleSpec
--   unfold OracleInterface.Query
--   unfold instOracleInterfaceFinalOracleStatement
--   simp

namespace FoldPhase

-- /- Definition of the non-final folding rounds of the FRI protocol. -/

-- /- Folding total round consistency predicate, checking of two subsequent code words will pass
--    the round consistency at all points. -/
-- def roundConsistent {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
--   [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k : ℕ} {s : Fin (k + 1) → ℕ+}
--   (cond : (∑ i, (s i).1) ≤ n) {i : Fin (k + 1)} [DecidableEq F] {j : Fin i}
--     (f : OracleStatement D x s i j.castSucc)
--     (f' : OracleStatement D x s i j.succ)
--     (x₀ : F) : Prop :=
--   ∀ s₀ : evalDomain D x (∑ j' ∈ (List.take j.1 (List.finRange (k + 1))).toFinset, s j'),
--       let queries :
--           List (evalDomain D x (∑ j' ∈ (List.take j.1 (List.finRange (k + 1))).toFinset, s j')) :=
--             List.map
--               (
--                 fun r =>
--                   ⟨
--                     _,
--                     CosetDomain.mul_root_of_unity
--                       D
--                       (Nat.le_sub_of_add_le (by nlinarith [cond, j.2, i.2]))
--                       s₀.2
--                       r.2
--                   ⟩
--               )
--               (Domain.rootsOfUnity D n s);
--       let pts := List.map (fun q => (q.1.1, f q)) queries;
--       let β := f' ⟨_, CosetDomain.pow_lift D x s s₀.2⟩;
--         RoundConsistency.roundConsistencyCheck x₀ pts β

-- /- Checks for the total Folding round consistency of all rounds up to the current one. -/
-- def statementConsistent {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
--   [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k s : ℕ} {i : Fin (k + 1)} [DecidableEq F]
--       (cond : (k + 1) * s ≤ n)
--       (stmt : Statement F i)
--       (ostmt : ∀ j, OracleStatement D x s i j) : Prop :=
--   ∀ j : Fin i,
--     let f  := ostmt j.castSucc;
--     let f' := ostmt j.succ;
--     let x₀  := stmt j;
--     roundConsistent cond f f' x₀

/- The FRI non-final folding round input relation, with proximity parameter `δ`, f
   for the `i`th round. -/
def inputRelation (cond : ∑ i, (s i).1 ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (Statement F i.castSucc × (∀ j, OracleStatement s ω i.castSucc j)) ×
        Witness F s d i.castSucc.castSucc
      ) := sorry

/- The FRI non-final folding round output relation, with proximity parameter `δ`,
   for the `i`th round. -/
def outputRelation (cond : ∑ i, (s i).1 ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (Statement F i.succ × (∀ j, OracleStatement s ω i.succ j)) ×
        Witness F s d i.succ.castSucc
      ) := sorry

/-- Each round of the FRI protocol begins with the verifier sending a random field element as the
  challenge to the prover, and ends with the prover sending an oracle to
  the verifier, commiting to evaluation of the witness at all points in the appropriate evaluation
  domain. -/
@[reducible]
def pSpec : ProtocolSpec 2 :=
  ⟨
    !v[.V_to_P, .P_to_V],
    !v[
        F,
        (ω.subdomainNatReversed (∑ j' ∈ finRangeTo (k + 1) (i.1 + 1), (s j').1)).toFinset → F
      ]
  ⟩

/- `OracleInterface` instance for `pSpec` of the non-final folding rounds. -/
instance {i : Fin k} : ∀ j, OracleInterface ((pSpec s (ω := ω) i).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => by
      unfold pSpec Message
      simp only [Fin.vcons_fin_zero, Nat.reduceAdd, Fin.isValue, Fin.vcons_one]
      infer_instance

instance {i : Fin k} : ∀ j, OracleInterface ((pSpec s (ω := ω) i).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance {i : Fin k} : ∀ j, Inhabited ((pSpec s (ω := ω) i).Challenge j) := by
  intro j
  letI : Inhabited F := ⟨0⟩
  rcases j with ⟨j, hj⟩
  have h_j_eq_0 : j = 0 := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j1 =>
        cases j1 using Fin.cases with
        | zero => simp [pSpec] at hj
        | succ j2 => exact j2.elim0
  subst h_j_eq_0
  simpa [pSpec, Challenge] using (inferInstance : Inhabited F)

noncomputable instance {i : Fin k} : ∀ j, Fintype ((pSpec s (ω := ω) i).Challenge j) := by
  intro j
  letI : Fintype F := Fintype.ofFinite _
  rcases j with ⟨j, hj⟩
  have h_j_eq_0 : j = 0 := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j1 =>
        cases j1 using Fin.cases with
        | zero => simp [pSpec] at hj
        | succ j2 => exact j2.elim0
  subst h_j_eq_0
  simpa [pSpec, Challenge] using (inferInstance : Fintype F)

/-- The prover for the `i`-th round of the FRI protocol. It first receives the challenge,
    then does an `s` degree split of this polynomial. Finally, it returns the evaluation of
    this polynomial on the next evaluation domain. -/
noncomputable def foldProver :
  OracleProver []ₒ
    (Statement F i.castSucc) (OracleStatement s ω i.castSucc) (Witness F s d i.castSucc.castSucc)
    (Statement F i.succ) (OracleStatement s ω i.succ) (Witness F s d i.castSucc.succ)
    (pSpec (ω := ω) s i) where
  PrvState
  | 0 =>
    (Statement F i.castSucc × ((j : Fin (↑i.castSucc + 1)) → OracleStatement s ω i.castSucc j)) ×
      Witness F s d i.castSucc.castSucc
  | _ =>
    (Statement F i.succ × ((j : Fin (↑i.castSucc + 1)) → OracleStatement s ω i.castSucc j)) ×
      Witness F s d i.castSucc.succ

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨chals, o⟩, p⟩ ↦
    pure ⟨fun x ↦ p.1.eval x.1, ⟨⟨chals, o⟩, p⟩⟩

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨⟨chals, o⟩, p⟩ ↦ pure <|
    fun (α : F) ↦
      ⟨
        ⟨Fin.append chals (fun (_ : Fin 1) => α), o⟩,
        ⟨FoldingPolynomial.polyFold p.1 (2 ^ (s i.castSucc).1) α, witness_lift p.2⟩
      ⟩
  | ⟨1, h⟩ => nomatch h

  output := fun ⟨⟨chals, o⟩, p⟩ ↦ pure <|
    ⟨
      ⟨
        chals,
        fun j ↦
          if h : j.1 < i.1
          then by
            simpa [OracleStatement] using o ⟨j.1, by
              rw [Fin.coe_castSucc]
              exact Nat.lt_add_right 1 h
            ⟩
          else fun x ↦ p.1.eval x.1
      ⟩,
      p
    ⟩

/-- The oracle verifier for the `i`-th non-final folding round of the FRI protocol. -/
noncomputable def foldVerifier :
  OracleVerifier []ₒ
    (Statement F i.castSucc) (OracleStatement s ω i.castSucc)
    (Statement F i.succ) (OracleStatement s ω i.succ)
    (pSpec (ω := ω) s i) where
  verify := fun prevChallenges roundChallenge ↦
    pure (Fin.vappend prevChallenges (fun _ ↦ roundChallenge ⟨0, by simp⟩))
  embed :=
    ⟨
      fun j ↦
        if h : j.val = (i.val + 1)
        then Sum.inr ⟨1, by simp⟩
        else Sum.inl ⟨j.val, by have := Nat.lt_succ_iff_lt_or_eq.mp j.2; aesop⟩,
      by intros _; aesop
    ⟩
  hEq := by
    unfold OracleStatement pSpec
    intros j
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.vcons_fin_zero,
      Nat.reduceAdd, MessageIdx, Fin.isValue, DFunLike.coe,
      Message]
    split_ifs with h
    · rcases j with ⟨j, hj⟩
      aesop
    · rfl

/-- The oracle reduction that is the `i`-th round of the FRI protocol. -/
noncomputable def foldOracleReduction :
  OracleReduction []ₒ
    (Statement F i.castSucc) (OracleStatement s ω i.castSucc) (Witness F s d i.castSucc.castSucc)
    (Statement F i.succ) (OracleStatement s ω i.succ) (Witness F s d i.succ.castSucc)
    (pSpec (ω := ω) s i) where
  prover := foldProver s d i
  verifier := foldVerifier s i

end FoldPhase

namespace FinalFoldPhase

/- Definition of the final folding round of the FRI protocol. -/

-- /- Folding total round consistency predicate, for the final round. -/
-- def roundConsistent {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
--   [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} {k : ℕ} {s : ℕ}
--   (cond : (k + 1) * s ≤ n) [DecidableEq F]
--     (f : FinalOracleStatement D x s (Fin.last k).castSucc)
--     (f' : FinalOracleStatement D x s (Fin.last (k + 1)))
--     (x₀ : F) : Prop :=
--   let f : evalDomain D x (s * k) → F := by
--     unfold FinalOracleStatement at f
--     simp only [Fin.coe_castSucc, Fin.val_last, Nat.left_eq_add, one_ne_zero, ↓reduceIte] at f
--     exact f
--   let f' : F[X] := by
--     unfold FinalOracleStatement at f'
--     simp only [Fin.val_last, ↓reduceIte] at f'
--     exact f' ()
--   ∀ s₀ : evalDomain D x (s * k),
--       let queries :
--           List (evalDomain D x (s * k)) :=
--             List.map
--               (
--                 fun r =>
--                   ⟨
--                     _,
--                     CosetDomain.mul_root_of_unity
--                       D
--                       (Nat.le_sub_of_add_le
--                         (by
--                           rw [Nat.add_mul, one_mul, mul_comm] at cond
--                           exact cond
--                         )
--                       )
--                       s₀.2
--                       r.2
--                   ⟩
--               )
--               (Domain.rootsOfUnity D n s);
--       let pts := List.map (fun q => (q.1.1, f q)) queries;
--       let β := f'.eval (s₀.1.1 ^ (2 ^ s));
--         RoundConsistency.roundConsistencyCheck x₀ pts β

/- Input relation for the final folding round. This is currently sorried out, to be filled in later.
-/
def inputRelation (cond : ∑ i, (s i).1 ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (
          Statement F (Fin.last k) ×
          (∀ j, OracleStatement s ω (Fin.last k) j)
        ) ×
        Witness F s d (Fin.last k).castSucc
      ) := sorry

/- Output relation for the final folding round. This is currently sorried out, to be filled in
later. -/
def outputRelation (cond : ∑ i, (s i).1 ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (FinalStatement F k × ∀ j, FinalOracleStatement s ω j) ×
        Witness F s d (Fin.last (k + 1))
      ) := sorry

/-- The final folding round of the FRI protocol begins with the verifier sending a random field
  element as the challenge to the prover, then in contrast to the previous folding rounds simply
  sends the folded polynomial to the verifier. -/
@[reducible]
def pSpec (F : Type) [Semiring F] : ProtocolSpec 2 :=
  ⟨!v[.V_to_P, .P_to_V], !v[F, F[X]]⟩

/- `OracleInterface` instance for the `pSpec` of the final folding round of the FRI protocol. -/
instance : ∀ j, OracleInterface ((pSpec F).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => OracleInterface.instDefault

/- `OracleInterface` instance for the `pSpec` of the final folding round of the FRI protocol. -/
instance : ∀ j, OracleInterface ((pSpec F).Challenge j) := ProtocolSpec.challengeOracleInterface

instance : ∀ j, Inhabited ((pSpec F).Challenge j) := by
  intro j
  letI : Inhabited F := ⟨0⟩
  rcases j with ⟨j, hj⟩
  have h_j_eq_0 : j = 0 := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j1 =>
        cases j1 using Fin.cases with
        | zero => simp [pSpec] at hj
        | succ j2 => exact j2.elim0
  subst h_j_eq_0
  simpa [pSpec, Challenge] using (inferInstance : Inhabited F)

noncomputable instance : ∀ j, Fintype ((pSpec F).Challenge j) := by
  intro j
  letI : Fintype F := Fintype.ofFinite _
  rcases j with ⟨j, hj⟩
  have h_j_eq_0 : j = 0 := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j1 =>
        cases j1 using Fin.cases with
        | zero => simp [pSpec] at hj
        | succ j2 => exact j2.elim0
  subst h_j_eq_0
  simpa [pSpec, Challenge] using (inferInstance : Fintype F)

/- Prover for the final folding round of the FRI protocol. -/
noncomputable def finalFoldProver :
  OracleProver []ₒ
    (Statement F (Fin.last k)) (OracleStatement s ω (Fin.last k))
      (Witness F s d (Fin.last k).castSucc)
    (FinalStatement F k) (FinalOracleStatement s ω)
      (Witness F s d (Fin.last (k + 1)))
    (pSpec F) where
  PrvState
  | 0 =>
    (Statement F (Fin.last k) × ((j : Fin (k + 1)) → OracleStatement s ω (Fin.last k) j)) ×
      Witness F s d (Fin.last k).castSucc
  | _ =>
    (FinalStatement F k × ((j : Fin (k + 1)) → OracleStatement s ω (Fin.last k) j)) ×
      Witness F s d (Fin.last (k + 1))

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨chals, o⟩, p⟩ ↦
    pure ⟨p.1, ⟨⟨chals, o⟩, p⟩⟩

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨⟨chals, o⟩, p⟩ ↦ pure <|
    fun (α : F) ↦
      ⟨
        ⟨Fin.vappend chals !v[α], o⟩,
        ⟨
          FoldingPolynomial.polyFold p.1 (2 ^ (s (Fin.last k)).1) α,
          by
            simpa only [(rfl : (Fin.last k).succ = (Fin.last (k + 1)))] using
              witness_lift p.2
        ⟩
      ⟩
  | ⟨1, h⟩ => nomatch h

  output := fun ⟨⟨chals, o⟩, p⟩ ↦ pure <|
    ⟨
      ⟨
        chals,
        fun j ↦ by
          unfold FinalOracleStatement
          if h : j.1 = k + 1
          then
            simp_all only [↓reduceIte]
            obtain ⟨val, property⟩ := p
            exact val
          else
          simpa [h, ↓reduceIte, OracleStatement] using
            o ⟨j.1, Nat.lt_of_le_of_ne (Fin.is_le j) h⟩
      ⟩,
      p
    ⟩

/- Used to fetch the polynomial sent by the prover. -/
def getConst (F : Type) [NonBinaryField F] : OracleComp [(pSpec F).Message]ₒ F[X] :=
  liftM <| OracleQuery.query (spec := [(pSpec F).Message]ₒ)
    ⟨⟨1, by rfl⟩, (by simpa using ())⟩


/-- The oracle verifier for the final folding round of the FRI protocol.
    Checks if the returned polynomial has degree less than `d`. -/
noncomputable def finalFoldVerifier :
  OracleVerifier []ₒ
    (Statement F (Fin.last k)) (OracleStatement s ω (Fin.last k))
    (FinalStatement F k) (FinalOracleStatement s ω)
    (pSpec F)  where
  verify := fun prevChallenges roundChallenge ↦ do
    let p ← getConst F
    guard (p.natDegree < d)
    pure (Fin.append prevChallenges (fun _ ↦ roundChallenge ⟨0, by simp⟩))
  embed :=
    ⟨
      fun j ↦
        if h : j.val = (k + 1)
        then Sum.inr ⟨1, by simp⟩
        else Sum.inl ⟨j.val, by have := Nat.lt_succ_iff_lt_or_eq.mp j.2; aesop⟩,
      by intros _; aesop
    ⟩
  hEq := by
    unfold OracleStatement pSpec
    intros j
    simp only [
      Fin.vcons_fin_zero, Nat.reduceAdd, MessageIdx, Fin.isValue,
      DFunLike.coe, Message
    ]
    split_ifs with h
    · simp
    · rfl

/-- The oracle reduction that is the final folding round of the FRI protocol. -/
noncomputable def finalFoldOracleReduction :
  OracleReduction []ₒ
    (Statement F (Fin.last k)) (OracleStatement s ω (Fin.last k))
      (Witness F s d (Fin.last k).castSucc)
    (FinalStatement F k) (FinalOracleStatement s ω)
      (Witness F s d (Fin.last (k + 1)))
    (pSpec F) where
  prover := finalFoldProver s d
  verifier := finalFoldVerifier s d

end FinalFoldPhase

namespace QueryRound

/- Definition of the query round of the FRI protocol. -/

/-  Parameter for the number of round consistency checks to be
    run by the query round. -/
variable (l : ℕ) [NeZero l]

/- Input/Output relations for the query round of the FRI protocol -/
def inputRelation (cond : ∑ i, (s i).1 ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (FinalStatement F k × ∀ j, FinalOracleStatement s ω j) ×
        Witness F s d (Fin.last (k + 1))
      )
  := FinalFoldPhase.outputRelation s d cond δ

def outputRelation (cond : ∑ i, (s i).1 ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (FinalStatement F k × ∀ j, FinalOracleStatement s ω j) ×
        Witness F s d (Fin.last (k + 1))
      )
  := FinalFoldPhase.outputRelation s d cond δ

/- The query round consistens of the verifier sending `l` elements of the
   the first evaluation domain, which will be used as a basis for the round
   consistency checks. This makes this implementation a public-coin protocol.
-/
@[reducible]
def pSpec : ProtocolSpec 1 :=
  ⟨!v[.V_to_P], !v[Fin l → (ω.subdomainNatReversed 0).toFinset]⟩

/- `OracleInterface` instances for the query round `pSpec`. -/
instance : ∀ j, OracleInterface ((pSpec (ω := ω) l).Message j) := fun j ↦
  match j with
  | ⟨0, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpec (ω := ω) l).Challenge j) := fun j ↦
  by
    unfold Challenge
    rw [Fin.fin_one_eq_zero j.1]
    exact OracleInterface.instFunction

noncomputable instance : ∀ j, Inhabited ((pSpec (ω := ω) l).Challenge j) := by
  rintro ⟨j, hj⟩
  have h_j_eq_0 : j = 0 := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j1 => exact j1.elim0
  subst h_j_eq_0
  simp only [Challenge, Nat.succ_eq_add_one, Nat.sub_zero, Fin.ofNat_eq_cast, Fin.val_natCast,
   Fin.isValue, Fin.vcons_zero]
  exact ⟨fun _ ↦ Inhabited.default⟩

noncomputable instance : ∀ j, Fintype ((pSpec (ω := ω) l).Challenge j) := by
  intro j
  letI : Fintype (ω.subdomainNatReversed 0).toFinset := Fintype.ofFinite _
  rcases j with ⟨j, hj⟩
  have h_j_eq_0 : j = 0 := by
    cases j using Fin.cases with
    | zero => rfl
    | succ j1 => exact j1.elim0
  subst h_j_eq_0
  simp only [Challenge, Nat.sub_zero, ReedSolomon.CosetFftDomain.mem_coset, Fin.isValue,
    Fin.vcons_zero]
  infer_instance

/- Query round prover, does nothing. After BCS transform is applied to
   construct the non-interactive FRI protocol, it will have to respond with
   appropriate Merkle proofs against the commitments sent in the non final folding
   rounds. -/
noncomputable def queryProver :
  OracleProver []ₒ
    (FinalStatement F k) (FinalOracleStatement s ω) (Witness F s d (Fin.last (k + 1)))
    (FinalStatement F k) (FinalOracleStatement s ω) (Witness F s d (Fin.last (k + 1)))
    (pSpec (ω := ω) l) where
  PrvState
  | _ =>
    (FinalStatement F k × ((i : Fin (k + 2)) → FinalOracleStatement s ω i)) ×
      Witness F s d (Fin.last (k + 1))

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h

  receiveChallenge
  | ⟨1, _⟩ => fun x ↦ pure <| fun _ ↦ x

  output := pure

/- Used by the verified to query the `i`th oracle at `w`, a point of the
   appropriate evaluation domain. -/
def queryCodeword (k : ℕ) (s : Fin (k + 1) → ℕ+) {i : Fin (k + 1)}
      (w :
        (ω.subdomainNatReversed
          (∑ j' ∈ finRangeTo (k + 1) i.1, (s j').1)).toFinset) :
    OracleComp [FinalOracleStatement s ω]ₒ F :=
  liftM (cast (β := OracleQuery [FinalOracleStatement s ω]ₒ F)
    (by {
     simp
  } )
    (query (spec := [FinalOracleStatement s ω]ₒ) ⟨⟨i.1, by omega⟩,
      (by simpa [Nat.ne_of_lt i.2] using w)⟩))

/- Used by the verifier to fetch the polynomial sent in final folding round. -/
def getConst (k : ℕ) (s : Fin (k + 1) → ℕ+) : OracleComp [FinalOracleStatement s ω]ₒ F[X] :=
  liftM (cast (β := OracleQuery [FinalOracleStatement s ω]ₒ F[X])
    (by simp [FinalOracleStatement])
    (query (spec := [FinalOracleStatement s ω]ₒ) ⟨(Fin.last (k + 1)), (by
      simpa using ())⟩))

/- Verifier for query round of the FRI protocol. Runs `l` checks on uniformly
   sampled points in the first evaluation domain against the oracles sent during
   every folding round. -/
open ReedSolomon.CosetFftDomain in
open ReedSolomon.FftDomain in
noncomputable def queryVerifier (k_le_n : (∑ j', (s j').1) ≤ n) (l : ℕ) [DecidableEq F] :
  OracleVerifier []ₒ
    (FinalStatement F k) (FinalOracleStatement s ω)
    (FinalStatement F k) (FinalOracleStatement s ω)
    (pSpec (ω := ω) l) where
  verify := fun prevChallenges roundChallenge ↦ do
    let (p : F[X]) ← getConst (ω := ω) k s
    for m in (List.finRange l) do
      let s₀ := roundChallenge ⟨1, by aesop⟩ m
      discard <|
        (List.finRange (k + 1)).mapM
              (fun i ↦
                do
                  let x₀ := prevChallenges i
                  let s₀ :
                    (ω.subdomainNatReversed
                      (∑ j' ∈ finRangeTo _ i.1, (s j').1)).toFinset :=
                    ⟨s₀ ^ (2 ^ (∑ j' ∈ finRangeTo _ i.1, (s j').1)), 
                      subdomainNatReversed_pow_property_main_domain_toFinset (Nat.le_trans 
                      (Finset.sum_le_sum_of_subset (t := Finset.univ) (by simp))
                      (k_le_n)) s₀.2⟩
                  let queries :
                    List (
                      ω.subdomainNatReversed
                        (∑ j' ∈ finRangeTo _ i.1, (s j').1)
                    ).toFinset :=
                    List.map
                      (fun (r : (ω.fftDomain.subdomainNatReversed (n - (s i).1)).toFinset) ↦
                        ⟨
                          r * s₀,
                          by {
                            rw [mul_comm, mem_coset_finset_iff_mem_coset_domain]
                            exact 
                              subdomainNatReversed_mul_property (by {
                                rw [Nat.le_sub_iff_add_le (by {
                                  exact Nat.le_trans (m := ∑ j', ↑(s j')) 
                                    (by {
                                      apply Finset.single_le_sum (f := fun i ↦ (s i : ℕ)) (by simp) (by simp)
                                    }) k_le_n 
                                })]
                                rw [←sum_finRangeTo_add_one]
                                trans
                                exact (Finset.sum_le_sum_of_subset (t := Finset.univ) (by simp))
                                exact k_le_n
                                 
                              }) (by omega) (mem_coset_finset_iff_mem_coset_domain.1 s₀.2) (mem_finset_iff_mem_domain.1 r.2)
                          }
                        ⟩
                      )
                      (ω.fftDomain.subdomainNatReversed (n - (s i).1)).toList
                  let (pts : List (F × F)) ←
                    List.mapM
                      (fun q ↦ queryCodeword (ω := ω) k s q >>= fun v ↦ pure (q.1, v))
                      queries
                  let β ←
                    if h : i.1 < k
                    then
                      queryCodeword (ω := ω) k s (i := ⟨i.1.succ, Order.lt_add_one_iff.mpr h⟩)
                        ⟨s₀.1 ^ (2 ^ (s i).1), by {
                          simp only
                          rw [sum_finRangeTo_add_one, mem_coset_finset_iff_mem_coset_domain]
                          apply subdomainNatReversed_pow_property'
                            (i := s i)
                            (h := mem_coset_finset_iff_mem_coset_domain.1 s₀.2)
                          trans (∑ j' ∈ finRangeTo (k + 1) (↑i : ℕ).succ, (s j').1)
                          rw [Nat.succ_eq_add_one, sum_finRangeTo_add_one]
                          rfl
                          trans 
                          exact (Finset.sum_le_sum_of_subset (t := Finset.univ) (by simp))
                          exact k_le_n
                        }⟩
                    else
                      pure (p.eval (s₀.1 ^ (2 ^ (s (Fin.last k)).1)))
                  guard (RoundConsistency.roundConsistencyCheck x₀ (List.get pts) β)
              )
    pure prevChallenges
  embed :=
    ⟨
      fun j ↦ Sum.inl j,
      by intros _; aesop
    ⟩
  hEq := by intros _; aesop

/- Query round oracle reduction. -/
noncomputable def queryOracleReduction [DecidableEq F] :
  OracleReduction []ₒ
    (FinalStatement F k) (FinalOracleStatement s ω) (Witness F s d (Fin.last (k + 1)))
    (FinalStatement F k) (FinalOracleStatement s ω) (Witness F s d (Fin.last (k + 1)))
    (pSpec (ω := ω) l) where
  prover := queryProver s d l
  verifier := queryVerifier s (round_bound domain_size_cond) l

end QueryRound

end Spec

end Fri
