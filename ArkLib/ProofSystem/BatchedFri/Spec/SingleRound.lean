import ArkLib.OracleReduction.Basic
import ArkLib.ProofSystem.Fri.Domain
import ArkLib.ProofSystem.Fri.RoundConsistency
import ArkLib.ProofSystem.Fri.Spec.SingleRound

/-!
# The Batched FRI protocol

  We describe the Batched FRI oracle reduction as a random linear combination round,
  and the FRI oracle reduction.

 -/

namespace BatchedFri

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset Fri CosetDomain NNReal

namespace Spec

/- FRI parameters:
   - `F` a non-binary finite field.
   - `D` the cyclic subgroup of order `2 ^ n` we will to construct the evaluation domains.
   - `x` the element of `Fˣ` we will use to construct our evaluation domain.
   - `k` the number of, non final, folding rounds the protocol will run.
   - `s` the "folding degree", for `s = 1` this corresponds to the standard "even-odd" folding.
   - `d` the degree bound on the final polynomial returned in the final folding round.
   - `m` the number of polynomials batched
-/
variable {F : Type} [NonBinaryField F] [Finite F] (D : Subgroup Fˣ)
variable {n : ℕ} [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D] (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (m : ℕ)


/-- An oracle for each batched polynomial. -/
@[reducible]
def OracleStatement : Fin (m + 1) → Type :=
  fun _ => evalDomain D x 0 → F

/-- The Batched FRI protocol has as witness for each batched polynomial
    that is supposed to correspond to the putative codewords in the oracle statement. -/
@[reducible]
def Witness (F : Type) [Semiring F] {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+) (m : ℕ) :=
  Fin (m + 1) → F⦃< 2 ^ (∑ i, (s i).1) * d⦄[X]

instance : ∀ j, OracleInterface (OracleStatement D x m j) :=
  fun _ => inferInstance

namespace BatchingRound

def inputRelation :
    Set
      (
        (Unit × (∀ j, OracleStatement D x m j)) ×
        Witness F s d m
      ) := sorry

/- The FRI non-final folding round output relation, with proximity parameter `δ`,
   for the `i`th round. -/
def outputRelation :
    Set
      (
        (Fri.Spec.Statement F (0 : Fin (k + 1)) ×
        (∀ j, Fri.Spec.OracleStatement D x s (0 : Fin (k + 1)) j)) ×
        Fri.Spec.Witness F s d (0 : Fin (k + 2))
      ) := sorry

/-- The verifier send `m` field elements to batch the `m + 1` batched polynomials,
    the prover then returns the putative codeword corresponding to the batched polynomial -/
@[reducible]
def batchSpec (F : Type) (m : ℕ) : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Fin m → F]⟩

/- `OracleInterface` instance for `pSpec` of the non-final folding rounds. -/
instance : ∀ j, OracleInterface ((batchSpec F m).Message j)
  | ⟨0, h⟩ => nomatch h

/-- The batching round oracle prover. -/
noncomputable def batchProver :
  OracleProver []ₒ
    Unit (OracleStatement D x m) (Witness F s d m)
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1)))
      (OracleStatement D x m) (Fri.Spec.Witness F s d (0 : Fin (k + 2)))
    (batchSpec F m) where
  PrvState
  | 0 => (∀j, OracleStatement D x m j) × Witness F s d m
  | 1 => (Fin m → F) × (∀j, OracleStatement D x m j) × Fri.Spec.Witness F s d (0 : Fin (k + 2))

  input := fun i => ⟨i.1.2, i.2⟩

  sendMessage
  | ⟨0, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨os, ps⟩ => pure <|
    fun (cs : Fin m → F) =>
      ⟨cs, os,
        ⟨
          ps 0 + ∑ i, Polynomial.C (cs i) * (ps i.succ).1,
          by
            unfold Fri.Spec.Witness
            simp only [List.toFinset_finRange, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.take_zero,
              List.toFinset_nil, sum_empty, tsub_zero]
            apply mem_degreeLT.mpr
            by_cases h : ↑(ps 0) + ∑ i, Polynomial.C (cs i) * ↑(ps i.succ) = 0
            · rw [h]
              simp
              exact compareOfLessAndEq_eq_lt.mp rfl
            · rw [Polynomial.degree_eq_natDegree h]
              norm_cast
              apply Nat.lt_of_le_pred (by simp)
              transitivity
              · exact Polynomial.natDegree_add_le _ _
              · apply Nat.max_le_of_le_of_le
                · have := mem_degreeLT.mp (ps 0).2
                  by_cases h₀ : (ps 0).1 = 0
                  · rw [h₀]
                    simp
                  · have := mem_degreeLT.mp (ps 0).2
                    erw
                      [
                        Polynomial.degree_eq_natDegree h₀,
                        WithBot.coe_lt_coe,
                        Nat.cast_id, Nat.cast_id
                      ] at this
                    exact Nat.le_pred_of_lt this
                · apply Polynomial.natDegree_sum_le_of_forall_le
                  intros i _
                  by_cases h : Polynomial.C (cs i) = 0
                  · rw [h]
                    simp
                  · by_cases h' : (ps i.succ).1 = 0
                    · rw [h']
                      simp
                    · rw [Polynomial.natDegree_mul h h', Polynomial.natDegree_C, zero_add]
                      have := mem_degreeLT.mp (ps i.succ).2
                      erw
                        [
                          Polynomial.degree_eq_natDegree h',
                          WithBot.coe_lt_coe,
                          Nat.cast_id, Nat.cast_id
                        ] at this
                      exact Nat.le_pred_of_lt this
        ⟩
      ⟩

  output := fun ⟨cs, os, p⟩ => pure <|
    ⟨⟨⟨cs, Fin.elim0⟩, os⟩, p⟩

/-- The batching round oracle verifier. -/
noncomputable def batchVerifier :
  OracleVerifier []ₒ
    Unit (OracleStatement D x m)
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1)))
    (OracleStatement D x m)
    (batchSpec F m) where
  verify := fun _ chals => pure ⟨chals ⟨0, by simp⟩, Fin.elim0⟩
  embed :=
    ⟨
      fun i => Sum.inl i,
      by intros _; aesop
    ⟩
  hEq := by simp

/-- The batching round oracle reduction. -/
noncomputable def batchOracleReduction :
  OracleReduction []ₒ
    Unit (OracleStatement D x m) (Witness F s d m)
    ((Fin m → F) × Fri.Spec.Statement F (0 : Fin (k + 1)))
    (OracleStatement D x m)
    (Fri.Spec.Witness F s d (0 : Fin (k + 2)))
    (batchSpec F m) where
  prover := batchProver D x s d m
  verifier := batchVerifier (k := k) D x m

end BatchingRound

end Spec

end BatchedFri
