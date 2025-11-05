/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši, Julian Sutherland, Ilia Vlasov
-/


import ArkLib.OracleReduction.Basic
import ArkLib.ProofSystem.Fri.Domain
import ArkLib.ProofSystem.Fri.RoundConsistency
import ArkLib.ToMathlib.Finset.Basic

/-!
# The FRI protocol

  We describe the FRI oracle reduction as a composition of many single rounds, and a final
  (zero-interaction) query round where the oracle verifier makes all queries to all received oracle
  codewords.

  This formalisation tries to encompass all of the generalisations of the FRI
  low-degree test covered in the "A summary on the {FRI} low degree test" paper
  by Ulrich Haböck (Cryptology ePrint Archive, Paper 2022/1216), see:
  https://eprint.iacr.org/2022/1216

 -/

namespace Fri

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset CosetDomain NNReal

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

variable {F : Type} [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (domain_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) (i : Fin k)


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
def OracleStatement (i : Fin (k + 1)) : Fin (i.val + 1) → Type :=
  fun j =>
    evalDomain D x (∑ j' ∈ finRangeTo j.1, s j')
      → F

@[reducible]
def FinalOracleStatement : Fin (k + 2) → Type :=
  fun j =>
    if j.1 = k + 1
    then (Unit → F[X])
    else (evalDomain D x (∑ j' ∈ finRangeTo j.1, s j') → F)

/-- The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in
  the oracle statement. -/
@[reducible]
def Witness (F : Type) [NonBinaryField F] {k : ℕ}
    (s : Fin (k + 1) → ℕ+) (d : ℕ+) (i : Fin (k + 2)) :=
  F⦃< 2^((∑ j', (s j').1) - (∑ j' ∈ finRangeTo i.1, (s j').1)) * d⦄[X]

private lemma sum_add_one {i : Fin (k + 1)} :
  ∑ j' ∈ finRangeTo (i.1 + 1), (s j').1 = (∑ j' ∈ finRangeTo i.1, (s j').1) + (s i).1 := by
          rw [finRangeTo, List.take_add, List.toFinset_append]
          rw
            [
              Finset.sum_union
                (by
                  rw [Finset.disjoint_iff_ne]
                  intros a h b h'
                  rw [List.mem_toFinset] at h h'
                  rw [List.mem_take_iff_getElem] at h h'
                  rcases h with ⟨ai, ah, ah'⟩
                  rcases h' with ⟨bi, bh, bh'⟩
                  have h₁ : ai < i.1 := by omega
                  have h₂ : bi = 0 := by omega
                  simp only [h₂, List.getElem_drop, add_zero, List.getElem_finRange, Fin.cast_mk,
                    Fin.eta] at bh'
                  simp only [List.getElem_finRange, Fin.cast_mk] at ah'
                  rw [←bh', ←ah']
                  rcases i with ⟨i, _⟩
                  simp only [ne_eq, Fin.mk.injEq]
                  linarith
                )
            ]
          apply Nat.add_left_cancel_iff.mpr
          have : (List.take 1 (List.drop (↑i) (List.finRange (k + 1)))).toFinset = {i} := by
            apply eq_singleton_iff_unique_mem.mpr
            apply And.intro
            · rw [List.mem_toFinset]
              apply List.mem_take_iff_getElem.mpr
              use 0
              use
                (by
                  rw [Nat.lt_min]
                  simp
                )
              rw [List.getElem_drop]
              simp
            · simp only [List.mem_toFinset]
              intros x h
              (expose_names; rw [List.mem_take_iff_getElem] at h)
              rcases h with ⟨j, h, h'⟩
              have : j = 0 := by
                omega
              simp only [this, List.getElem_drop, add_zero, List.getElem_finRange, Fin.cast_mk,
                Fin.eta] at h'
              exact h'.symm
          rw [this]
          simp

omit [Finite F] in
private lemma witness_lift {F : Type} [NonBinaryField F]
  {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+} {p : F[X]} {α : F} {i : Fin (k + 1)} :
    p ∈ Witness F s d i.castSucc →
      p.foldNth (2 ^ (s i).1) α ∈ Witness F s d i.succ := by
  intro deg_bound
  unfold Witness at deg_bound ⊢
  rw [Polynomial.mem_degreeLT] at deg_bound ⊢
  simp only [Fin.coe_castSucc, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Fin.val_succ] at deg_bound ⊢
  by_cases h : p = 0
  · rw [h, foldNth_zero, degree_zero]
    exact WithBot.bot_lt_coe _
  · by_cases h' : foldNth (2 ^ (s i).1) p α = 0
    · rw [h', degree_zero]
      exact WithBot.bot_lt_coe _
    · erw [Polynomial.degree_eq_natDegree h, WithBot.coe_lt_coe] at deg_bound
      erw [Polynomial.degree_eq_natDegree h', WithBot.coe_lt_coe]
      norm_cast at deg_bound ⊢
      have : 2 ^ (s i).1 > 0 := by
        simp only [gt_iff_lt, Nat.ofNat_pos, pow_pos]
      rw [Iff.symm (Nat.mul_lt_mul_left this)]
      apply lt_of_le_of_lt foldNth_degree_le'
      have arith {a b c : ℕ} (h : b ≥ c) (h' : a ≤ c) : a + (b - c) = b - (c - a) := by
        rw [Nat.sub_sub_right b h', Nat.sub_add_comm h, Nat.add_comm]
      rw [←mul_assoc, ←pow_add, arith]
      · convert deg_bound
        rw [sum_add_one]
        simp
      · simp only [ge_iff_le]
        apply sum_le_univ_sum_of_nonneg
        simp
      · apply @CanonicallyOrderedAddCommMonoid.single_le_sum (Fin (k + 1)) ℕ _ _ _
            (fun j => (s j).1)
            (List.take (↑i + 1) (List.finRange (k + 1))).toFinset i
        rw [List.mem_toFinset]
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

instance {i : Fin (k + 1)} : ∀ j, OracleInterface (OracleStatement D x s i j) :=
  fun _ => inferInstance

instance : ∀ j, OracleInterface (FinalOracleStatement D x s j) :=
  fun j =>
    if h : j = k + 1
    then {
           Query := Unit
           Response := F[X]
           answer := cast (by simp [h, FinalOracleStatement])
                          (id (α := Unit → F[X]))
         }
    else {
           Query :=
            ↑(
              evalDomain D x
              (∑ j' ∈ finRangeTo j.1, s j')
            )
           Response := F
           answer := cast (by simp [h, FinalOracleStatement])
                          (id (α := ↑(evalDomain D x (∑ j' ∈ finRangeTo j.1, s j')) → F))
         }

omit [Finite F] in
@[simp]
lemma range_lem₁ {i : Fin (k + 1)} :
    [FinalOracleStatement D x s]ₒ.range ⟨i.1, Nat.lt_succ_of_lt i.2⟩ = F := by
  unfold OracleSpec.range FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query
  unfold instOracleInterfaceFinalOracleStatement
  simp [Nat.ne_of_lt i.2]

omit [Finite F] in
@[simp]
lemma domain_lem₁ {i : Fin (k + 1)} :
    [FinalOracleStatement D x s]ₒ.domain ⟨i.1, Nat.lt_succ_of_lt i.2⟩ =
      evalDomain D x (∑ j' ∈ finRangeTo i.1, s j') := by
  unfold OracleSpec.domain FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query
  unfold instOracleInterfaceFinalOracleStatement
  simp [Nat.ne_of_lt i.2]

omit [Finite F] in
@[simp]
lemma range_lem₂ : [FinalOracleStatement D x s]ₒ.range (Fin.last (k + 1)) = F[X] := by
  unfold OracleSpec.range FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query
  unfold instOracleInterfaceFinalOracleStatement
  simp

omit [Finite F] in
@[simp]
lemma domain_lem₂ :
  [FinalOracleStatement D x s]ₒ.domain (Fin.last (k + 1)) = Unit := by
  unfold OracleSpec.domain FinalOracleStatement OracleInterface.toOracleSpec
  unfold OracleInterface.Query
  unfold instOracleInterfaceFinalOracleStatement
  simp

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
        (Statement F i.castSucc × (∀ j, OracleStatement D x s i.castSucc j)) ×
        Witness F s d i.castSucc.castSucc
      ) := sorry

/- The FRI non-final folding round output relation, with proximity parameter `δ`,
   for the `i`th round. -/
def outputRelation (cond : ∑ i, (s i).1 ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (Statement F i.succ × (∀ j, OracleStatement D x s i.succ j)) ×
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
        (evalDomain D x (∑ j' ∈ (List.take (i.1 + 1) (List.finRange (k + 1))).toFinset, s j')) → F
      ]
  ⟩

/- `OracleInterface` instance for `pSpec` of the non-final folding rounds. -/
instance {i : Fin k} : ∀ j, OracleInterface ((pSpec D x s i).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => by
      unfold pSpec Message
      simp only [Fin.vcons_fin_zero, Nat.reduceAdd, Fin.isValue, Fin.vcons_one]
      infer_instance

/-- The prover for the `i`-th round of the FRI protocol. It first receives the challenge,
    then does an `s` degree split of this polynomial. Finally, it returns the evaluation of
    this polynomial on the next evaluation domain. -/
noncomputable def foldProver :
  OracleProver []ₒ
    (Statement F i.castSucc) (OracleStatement D x s i.castSucc) (Witness F s d i.castSucc.castSucc)
    (Statement F i.succ) (OracleStatement D x s i.succ) (Witness F s d i.castSucc.succ)
    (pSpec D x s i) where
  PrvState
  | 0 =>
    (Statement F i.castSucc × ((j : Fin (↑i.castSucc + 1)) → OracleStatement D x s i.castSucc j)) ×
      Witness F s d i.castSucc.castSucc
  | _ =>
    (Statement F i.succ × ((j : Fin (↑i.castSucc + 1)) → OracleStatement D x s i.castSucc j)) ×
      Witness F s d i.castSucc.succ

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨chals, o⟩, p⟩ =>
    pure ⟨fun x => p.1.eval x.1.1, ⟨⟨chals, o⟩, p⟩⟩

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨⟨chals, o⟩, p⟩ => pure <|
    fun (α : F) =>
      ⟨
        ⟨Fin.append chals (fun (_ : Fin 1) => α), o⟩,
        ⟨p.1.foldNth (2 ^ (s i.castSucc).1) α, witness_lift p.2⟩
      ⟩
  | ⟨1, h⟩ => nomatch h

  output := fun ⟨⟨chals, o⟩, p⟩ => pure <|
    ⟨
      ⟨
        chals,
        fun j =>
          if h : j.1 < i.1
          then by
            simpa [OracleStatement, evalDomain] using o ⟨j.1, by
              rw [Fin.coe_castSucc]
              exact Nat.lt_add_right 1 h
            ⟩
          else fun x => p.1.eval x.1.1
      ⟩,
      p
    ⟩

/-- The oracle verifier for the `i`-th non-final folding round of the FRI protocol. -/
noncomputable def foldVerifier :
  OracleVerifier []ₒ
    (Statement F i.castSucc) (OracleStatement D x s i.castSucc)
    (Statement F i.succ) (OracleStatement D x s i.succ)
    (pSpec D x s i) where
  verify := fun prevChallenges roundChallenge =>
    pure (Fin.vappend prevChallenges (fun _ => roundChallenge ⟨0, by simp⟩))
  embed :=
    ⟨
      fun j =>
        if h : j.val = (i.val + 1)
        then Sum.inr ⟨1, by simp⟩
        else Sum.inl ⟨j.val, by have := Nat.lt_succ_iff_lt_or_eq.mp j.2; aesop⟩,
      by intros _; aesop
    ⟩
  hEq := by
    unfold OracleStatement pSpec
    intros j
    simp only [Fin.val_succ, Fin.coe_castSucc, Fin.vcons_fin_zero,
      Nat.reduceAdd, MessageIdx, Fin.isValue, Function.Embedding.coeFn_mk,
      Message]
    split_ifs with h
    · simp [h]
    · rfl

/-- The oracle reduction that is the `i`-th round of the FRI protocol. -/
noncomputable def foldOracleReduction :
  OracleReduction []ₒ
    (Statement F i.castSucc) (OracleStatement D x s i.castSucc) (Witness F s d i.castSucc.castSucc)
    (Statement F i.succ) (OracleStatement D x s i.succ) (Witness F s d i.succ.castSucc)
    (pSpec D x s i) where
  prover := foldProver D x s d i
  verifier := foldVerifier D x s i

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
          (∀ j, OracleStatement D x s (Fin.last k) j)
        ) ×
        Witness F s d (Fin.last k).castSucc
      ) := sorry

/- Output relation for the final folding round. This is currently sorried out, to be filled in
later. -/
def outputRelation (cond : ∑ i, (s i).1 ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (FinalStatement F k × ∀ j, FinalOracleStatement D x s j) ×
        Witness F s d (Fin.last (k + 1))
      ) := sorry

/-- The final folding round of the FRI protocol begins with the verifier sending a random field
  element as the challenge to the prover, then in contrast to the previous folding rounds simply
  sends the folded polynomial to the verifier. -/
@[reducible]
def pSpec (F : Type) [Semiring F] : ProtocolSpec 2 := ⟨!v[.V_to_P, .P_to_V], !v[F, Unit → F[X]]⟩

/- `OracleInterface` instance for the `pSpec` of the final folding round of the FRI protocol. -/
instance : ∀ j, OracleInterface ((pSpec F).Message j)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => by
      unfold pSpec Message
      simp only [Fin.vcons_fin_zero, Nat.reduceAdd, Fin.isValue, Fin.vcons_one]
      exact OracleInterface.instFunction

/- Prover for the final folding round of the FRI protocol. -/
noncomputable def finalFoldProver :
  OracleProver []ₒ
    (Statement F (Fin.last k)) (OracleStatement D x s (Fin.last k))
      (Witness F s d (Fin.last k).castSucc)
    (FinalStatement F k) (FinalOracleStatement D x s)
      (Witness F s d (Fin.last (k + 1)))
    (pSpec F) where
  PrvState
  | 0 =>
    (Statement F (Fin.last k) × ((j : Fin (k + 1)) → OracleStatement D x s (Fin.last k) j)) ×
      Witness F s d (Fin.last k).castSucc
  | _ =>
    (FinalStatement F k × ((j : Fin (k + 1)) → OracleStatement D x s (Fin.last k) j)) ×
      Witness F s d (Fin.last (k + 1))

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨⟨chals, o⟩, p⟩ =>
    pure ⟨fun x => p.1, ⟨⟨chals, o⟩, p⟩⟩

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨⟨chals, o⟩, p⟩ => pure <|
    fun (α : F) =>
      ⟨
        ⟨Fin.vappend chals !v[α], o⟩,
        ⟨
          p.1.foldNth (2 ^ (s (Fin.last k)).1) α,
          by
            simpa only [(rfl : (Fin.last k).succ = (Fin.last (k + 1)))] using
              witness_lift p.2
        ⟩
      ⟩
  | ⟨1, h⟩ => nomatch h

  output := fun ⟨⟨chals, o⟩, p⟩ => pure <|
    ⟨
      ⟨
        chals,
        fun j => by
          unfold FinalOracleStatement
          if h : j.1 = k + 1
          then
            simpa [h] using fun x => p.1
          else
          simpa [h, ↓reduceIte, OracleStatement, evalDomain] using
            o ⟨j.1, Nat.lt_of_le_of_ne (Fin.is_le j) h⟩
      ⟩,
      p
    ⟩

/- Used to fetch the polynomial sent by the prover. -/
def getConst (F : Type) [NonBinaryField F] : OracleComp [(pSpec F).Message]ₒ F[X] :=
  OracleComp.lift
    (by exact
          OracleSpec.query
            (spec := [(pSpec F).Message]ₒ)
            ⟨1, by rfl⟩
            (by simpa using ())
    )

/-- The oracle verifier for the final folding round of the FRI protocol.
    Checks if the returned polynomial has degree less than `d`. -/
noncomputable def finalFoldVerifier :
  OracleVerifier []ₒ
    (Statement F (Fin.last k)) (OracleStatement D x s (Fin.last k))
    (FinalStatement F k) (FinalOracleStatement D x s)
    (pSpec F)  where
  verify := fun prevChallenges roundChallenge => do
    let p ← getConst F
    guard (p.natDegree < d)
    pure (Fin.append prevChallenges (fun _ => roundChallenge ⟨0, by simp⟩))
  embed :=
    ⟨
      fun j =>
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
      Function.Embedding.coeFn_mk, Message
    ]
    split_ifs with h
    · simp
    · rfl

/-- The oracle reduction that is the final folding round of the FRI protocol. -/
noncomputable def finalFoldOracleReduction :
  OracleReduction []ₒ
    (Statement F (Fin.last k)) (OracleStatement D x s (Fin.last k))
      (Witness F s d (Fin.last k).castSucc)
    (FinalStatement F k) (FinalOracleStatement D x s)
      (Witness F s d (Fin.last (k + 1)))
    (pSpec F) where
  prover := finalFoldProver D x s d
  verifier := finalFoldVerifier D x s d

end FinalFoldPhase

namespace QueryRound

/- Definition of the query round of the FRI protocol. -/

/-  Parameter for the number of round consistency checks to be
    run by the query round. -/
variable (l : ℕ)

/- Input/Output relations for the query round of the FRI protocol -/
def inputRelation (cond : ∑ i, (s i).1 ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (FinalStatement F k × ∀ j, FinalOracleStatement D x s j) ×
        Witness F s d (Fin.last (k + 1))
      )
  := FinalFoldPhase.outputRelation D x s d cond δ

def outputRelation (cond : ∑ i, (s i).1 ≤ n) [DecidableEq F] (δ : ℝ≥0) :
    Set
      (
        (FinalStatement F k × ∀ j, FinalOracleStatement D x s j) ×
        Witness F s d (Fin.last (k + 1))
      )
  := FinalFoldPhase.outputRelation D x s d cond δ

/- The query round consistens of the verifier sending `l` elements of the
   the first evaluation domain, which will be used as a basis for the round
   consistency checks. This makes this implementation a public-coin protocol.
-/
@[reducible]
def pSpec : ProtocolSpec 1 :=
  ⟨!v[.V_to_P], !v[Fin l → evalDomain D x 0]⟩

/- `OracleInterface` instances for the query round `pSpec`. -/
instance : ∀ j, OracleInterface ((pSpec D x l).Message j) := fun j =>
  match j with
  | ⟨0, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((pSpec D x l).Challenge j) := fun j =>
  by
    unfold Challenge
    rw [Fin.fin_one_eq_zero j.1]
    exact OracleInterface.instFunction

/- Query round prover, does nothing. After BCS transform is applied to
   construct the non-interactive FRI protocol, it will have to respond with
   appropriate Merkle proofs against the commitments sent in the non final folding
   rounds. -/
noncomputable def queryProver :
  OracleProver []ₒ
    (FinalStatement F k) (FinalOracleStatement D x s) (Witness F s d (Fin.last (k + 1)))
    (FinalStatement F k) (FinalOracleStatement D x s) (Witness F s d (Fin.last (k + 1)))
    (pSpec D x l) where
  PrvState
  | _ =>
    (FinalStatement F k × ((i : Fin (k + 2)) → FinalOracleStatement D x s i)) ×
      Witness F s d (Fin.last (k + 1))

  input := id

  sendMessage
  | ⟨0, h⟩ => nomatch h

  receiveChallenge
  | ⟨1, _⟩ => fun x => pure <| fun _ => x

  output := pure

/- Used by the verified to query the `i`th oracle at `w`, a point of the
   appropriate evaluation domain. -/
def queryCodeword (k : ℕ) (s : Fin (k + 1) → ℕ+) {i : Fin (k + 1)}
      (w : evalDomain D x (∑ j' ∈ (List.take i.1 (List.finRange (k + 1))).toFinset, (s j').1)) :
    OracleComp [FinalOracleStatement D x s]ₒ F :=
      OracleComp.lift <| by
        simpa using
          OracleSpec.query
            (spec := [FinalOracleStatement D x s]ₒ)
            ⟨i.1, Nat.lt_succ_of_lt i.2⟩
            (by simpa using w)

/- Used by the verifier to fetch the polynomial sent in final folding round. -/
def getConst (k : ℕ) (s : Fin (k + 1) → ℕ+) : OracleComp [FinalOracleStatement D x s]ₒ F[X] :=
  OracleComp.lift
    (by
        simpa using
          OracleSpec.query
            (spec := [FinalOracleStatement D x s]ₒ)
            (Fin.last (k + 1))
            (by simpa using ())
    )

private lemma roots_of_unity_lem {s : Fin (k + 1) → ℕ+} {i : Fin (k + 1)}
    (k_le_n : (∑ j', (s j').1) ≤ n) :
  (∑ j' ∈ finRangeTo i.1, (s j').1) ≤ n - (s i).1 := by
    apply Nat.le_sub_of_add_le
    rw [←sum_add_one]
    transitivity
    · exact sum_le_univ_sum_of_nonneg (by simp)
    · exact k_le_n

/- Verifier for query round of the FRI protocol. Runs `l` checks on uniformly
   sampled points in the first evaluation domain against the oracles sent during
   every folding round. -/
noncomputable def queryVerifier (k_le_n : (∑ j', (s j').1) ≤ n) (l : ℕ) [DecidableEq F] :
  OracleVerifier []ₒ
    (FinalStatement F k) (FinalOracleStatement D x s)
    (FinalStatement F k) (FinalOracleStatement D x s)
    (pSpec D x l) where
  verify := fun prevChallenges roundChallenge => do
    let (p : F[X]) ← getConst D x k s
    for m in (List.finRange l) do
      let s₀ := roundChallenge ⟨1, by aesop⟩ m
      discard <|
        (List.finRange (k + 1)).mapM
              (fun i =>
                do
                  let x₀ := prevChallenges i
                  let s₀ :
                    evalDomain D x
                      (∑ j' ∈ finRangeTo i.1, (s j').1) :=
                    ⟨_, pow_2_pow_i_mem_Di_of_mem_D _ s₀.2⟩
                  let queries :
                    List (
                      evalDomain D x
                        (∑ j' ∈ finRangeTo i.1, (s j').1)
                    ) :=
                    List.map
                      (fun r =>
                        ⟨
                          _,
                          CosetDomain.mul_root_of_unity D (roots_of_unity_lem k_le_n) s₀.2 r.2
                        ⟩
                      )
                      (Domain.rootsOfUnity D n (s i))
                  let (pts : List (F × F)) ←
                    List.mapM
                      (fun q => queryCodeword D x k s q >>= fun v => pure (q.1.1, v))
                      queries
                  let β ←
                    if h : i.1 < k
                    then
                      have := CosetDomain.pow_lift D x (s i).1 s₀.2
                      queryCodeword D x k s (i := ⟨i.1.succ, Order.lt_add_one_iff.mpr h⟩)
                        ⟨_, by rw [←sum_add_one] at this; exact this⟩
                    else
                      pure (p.eval (s₀.1.1 ^ (2 ^ (s (Fin.last k)).1)))
                  guard (RoundConsistency.roundConsistencyCheck x₀ pts β)
              )
    pure prevChallenges
  embed :=
    ⟨
      fun j => Sum.inl j,
      by intros _; aesop
    ⟩
  hEq := by intros _; aesop

/- Query round oracle reduction. -/
noncomputable def queryOracleReduction [DecidableEq F] :
  OracleReduction []ₒ
    (FinalStatement F k) (FinalOracleStatement D x s) (Witness F s d (Fin.last (k + 1)))
    (FinalStatement F k) (FinalOracleStatement D x s) (Witness F s d (Fin.last (k + 1)))
    (pSpec D x l) where
  prover := queryProver D x s d l
  verifier := queryVerifier D x s (round_bound domain_size_cond) l

end QueryRound

end Spec

end Fri
