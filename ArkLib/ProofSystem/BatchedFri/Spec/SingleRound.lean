/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Quang Dao, Alexander Hicks, Devon Tuma, Ilia Vlasov
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
public import ArkLib.OracleReduction.Basic
public import ArkLib.ProofSystem.Fri.RoundConsistency
public import ArkLib.ProofSystem.Fri.Spec.InputRelation
public import CompPoly.Univariate.Basic
public import CompPoly.Univariate.Linear
public import CompPoly.Univariate.ToPoly.Impl

/-!
# The Batched FRI protocol

A uniformly sampled seed `x : S` determines coefficients `G x` through a proximity generator.
The batching round emits their linear combination as a virtual oracle and is followed by FRI.
Independent coefficients, powers, and multilinear monomials share the same input and output
relations. Their bounds are supplied in `BatchedFri/Security.lean`.

 -/

@[expose] public section

namespace BatchedFri

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset Fri NNReal Domain

namespace Spec

/- FRI parameters:
   - `F` a non-binary finite field.
   - `D` the cyclic subgroup of order `2 ^ n` we will to construct the evaluation domains.
   - `x` the element of `Fˣ` we will use to construct our evaluation domain.
   - `k` the number of, non final, folding rounds the protocol will run.
   - `s` the "folding degree", for `s = 1` this corresponds to the standard "even-odd" folding.
   - `d` the degree bound on the final polynomial returned in the final folding round.
   - `m` is one less than the number of batched input polynomials
-/
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ}
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (m : ℕ)
variable {ω : SmoothCosetFftDomain n F}


/-- An oracle for each batched polynomial. -/
@[reducible]
def OracleStatement (ω : SmoothCosetFftDomain n F) : Fin (m + 1) → Type :=
  fun _ => ω.toFinset → F

/-- The Batched FRI protocol has as witness for each batched polynomial
    that is supposed to correspond to the putative codewords in the oracle statement.
    We use `CompPoly.CPolynomial`, the computable representation, by way of the
    iso to Mathlib's `Polynomial`. -/
@[reducible]
def Witness (F : Type) [Zero F] {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ+) (m : ℕ) :=
  Fin (m + 1) → CompPoly.CPolynomial.degreeLT (R := F) (2 ^ (∑ i, (s i).1) * d)

instance : ∀ j, OracleInterface (OracleStatement m ω j) :=
  fun _ => inferInstance

namespace BatchingRound

variable {S : Type} [Fintype S] [Nonempty S]
variable (G : CoreDefinitions.Generator S (Fin (m + 1)) F)

/-- View a coordinate of FRI's initial domain as a coordinate of the batched
input domain.  The two domains have the same carrier; spelling out the bridge
here keeps the virtual-oracle implementation independent of proof terms in the
two subtype presentations. -/
def initialDomainPoint (j : Fin 1)
    (v : (ω.subdomain
      (∑ j' ∈ finRangeTo (k + 1) j.1, s j')).toFinset) : ω.toFinset := by
  rcases j with ⟨j, hj⟩
  have hj0 : j = 0 := by omega
  subst j
  rcases v with ⟨v, hv⟩
  refine ⟨v, ?_⟩
  simp only [CosetFftDomainClass.mem_toFinset_iff_mem] at hv ⊢
  exact CosetFftDomainClass.mem_subdomain_0_iff_mem.mp hv

/-- The generator-selected linear combination of the input codewords, represented at the
exact oracle type consumed by the first FRI round. -/
def combinedOracle (cs : S) (oStmt : ∀ j, OracleStatement m ω j) :
    ∀ j, Fri.Spec.OracleStatement s ω (0 : Fin (k + 1)) j :=
  fun j v =>
    ((List.finRange (m + 1)).map fun i =>
      G cs i * oStmt i (initialDomainPoint (s := s) j v)).sum

/-- The words agree with their degree-bounded polynomial witnesses on one common set
of relative size at least `1 - δ` in the initial evaluation domain. -/
def inputRelation (δ : ℝ≥0) :
    Set ((Unit × (∀ j, OracleStatement m ω j)) × Witness F s d m) :=
  {sw | ∃ S : Finset (Fin (2 ^ n)),
    (1 - δ) * Fintype.card (Fin (2 ^ n)) ≤ S.card ∧
    ∀ i, ∀ z ∈ S, sw.1.2 i (ω.equivToFinset z) = (sw.2 i).1.eval (ω z)}

/-- The batching output relation is exactly the initial FRI relation at the same radius. -/
def outputRelation (dom_size_cond : 2 ^ (∑ i, (s i).1) * d ≤ 2 ^ n) (δ : ℝ≥0) :=
  Fri.Spec.inputRelation k (ω := ω) s d dom_size_cond δ

/-- The verifier sends one seed in `S`. The combined word is a virtual oracle;
the prover sends no message in this round. -/
@[reducible]
def batchSpec (S : Type) : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[S]⟩

/- `OracleInterface` instance for `pSpec` of the non-final folding rounds. -/
instance : ∀ j, OracleInterface ((batchSpec S).Message j)
  | ⟨0, h⟩ => nomatch h

instance : ∀ j, OracleInterface ((batchSpec S).Challenge j) :=
  ProtocolSpec.challengeOracleInterface

instance [Inhabited S] : ∀ j, Inhabited ((batchSpec S).Challenge j) := by
  rintro ⟨j, hj⟩
  have hz : j = 0 := Fin.eq_zero j
  subst j
  exact inferInstanceAs (Inhabited S)

instance : ∀ j, Fintype ((batchSpec S).Challenge j) := by
  rintro ⟨j, hj⟩
  have hz : j = 0 := Fin.eq_zero j
  subst j
  exact inferInstanceAs (Fintype S)

/-- Query one batched input codeword in the verifier's full oracle context. -/
def queryInput (i : Fin (m + 1)) (x : ω.toFinset) :
    OracleComp ([]ₒ + ([OracleStatement m ω]ₒ + [(batchSpec S).Message]ₒ)) F :=
  liftM <| OracleSpec.query
    (show ([]ₒ + ([OracleStatement m ω]ₒ + [(batchSpec S).Message]ₒ)).Domain from
      Sum.inr (Sum.inl ⟨i, x⟩))

omit [Fintype F] [Fintype S] [Nonempty S] in
@[simp]
theorem simulateQ_queryInput
    (oStmt : ∀ i, OracleStatement m ω i) (messages : (batchSpec S).Messages)
    (i : Fin (m + 1)) (x : ω.toFinset) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt messages)
        (queryInput (F := F) (S := S) m i x) = pure (oStmt i x) := by
  simp only [MessageIdx, Message, OracleInterface.simOracle2, QueryImpl.addLift,
    queryInput, Lean.Elab.WF.paramLet]
  change id <$> (pure (oStmt i x) : OracleComp []ₒ F) = pure (oStmt i x)
  simp only [map_pure, id_eq]

/-- The degree-bounded polynomial carried into FRI by honest batching. -/
def combinedWitness (cs : S) (ps : Witness F s d m) :
    Fri.Spec.Witness F s d (0 : Fin (k + 2)) :=
  let q : CompPoly.CPolynomial F :=
    ∑ i, CompPoly.CPolynomial.C (G cs i) * (ps i).1
  ⟨
    q, by
      unfold Fri.Spec.Witness
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod]
      rw [CompPoly.CPolynomial.degreeLT_toPoly]
      change ((∑ i, CompPoly.CPolynomial.C (G cs i) * (ps i).1) :
        CompPoly.CPolynomial F).toPoly ∈ _
      rw [CompPoly.CPolynomial.toPoly_sum]
      simp only [CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.C_toPoly]
      simp only [finRangeTo, List.take_zero, List.toFinset_nil, sum_empty, tsub_zero]
      apply Submodule.sum_mem
      intro i _
      rw [← Polynomial.smul_eq_C_mul]
      exact Submodule.smul_mem _ _ (CompPoly.CPolynomial.degreeLT_toPoly.mp (ps i).2)
  ⟩

/-- The batching round oracle prover. -/
def batchProver :
    OracleProver []ₒ
    Unit (OracleStatement m ω) (Witness F s d m)
    (Fri.Spec.Statement F (0 : Fin (k + 1)))
      (Fri.Spec.OracleStatement s ω (0 : Fin (k + 1)))
      (Fri.Spec.Witness F s d (0 : Fin (k + 2)))
    (batchSpec S) where
  PrvState
  | 0 => (∀j, OracleStatement m ω j) × Witness F s d m
  | 1 => S × (∀j, OracleStatement m ω j) × Fri.Spec.Witness F s d (0 : Fin (k + 2))

  input := fun i => ⟨i.1.2, i.2⟩

  sendMessage
  | ⟨0, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, _⟩ => fun ⟨os, ps⟩ => pure <|
    fun (cs : S) =>
      ⟨cs, os, combinedWitness s d m G cs ps⟩

  output := fun ⟨cs, os, p⟩ => pure <|
    ⟨⟨Fin.elim0, combinedOracle (s := s) m G cs os⟩, p⟩

/-- Virtual implementation of the random-linear-combination codeword.  Every
downstream coordinate query is answered by querying the corresponding
coordinate of all batched input codewords. -/
def outputSimulation :
    OracleOutputSimulation []ₒ (OracleStatement m ω)
      (Fri.Spec.OracleStatement s ω (0 : Fin (k + 1))) (batchSpec S) where
  materializeOutput := fun challenges oStmt _ =>
    combinedOracle (s := s) m G (challenges ⟨0, by simp⟩) oStmt
  simulateOutputQuery := fun challenges q => do
    let x := initialDomainPoint (s := s) q.1 q.2
    let fs ← (List.finRange (m + 1)).mapM fun (i : Fin (m + 1)) => do
      let fi ← queryInput (F := F) (S := S) m i x
      pure (G (challenges ⟨0, by simp⟩) i * fi)
    pure fs.sum
  simulateOutputQuery_eq := by
    intro challenges oStmt messages q
    rcases q with ⟨j, v⟩
    simp only [simulateQ_bind, simulateQ_queryInput, simulateQ_list_mapM,
      List.mapM_pure, pure_bind, simulateQ_pure]
    rfl

/-- The batching round oracle verifier. -/
def batchVerifier :
    OracleVerifier []ₒ
    Unit (OracleStatement m ω)
    (Fri.Spec.Statement F (0 : Fin (k + 1)))
    (Fri.Spec.OracleStatement s ω (0 : Fin (k + 1)))
    (batchSpec S) where
  verify := fun _ _ => pure Fin.elim0
  outputOracle := .inr (outputSimulation (s := s) m G)

/-- The batching round oracle reduction. -/
def batchOracleReduction :
    OracleReduction []ₒ
    Unit (OracleStatement m ω) (Witness F s d m)
    (Fri.Spec.Statement F (0 : Fin (k + 1)))
    (Fri.Spec.OracleStatement s ω (0 : Fin (k + 1)))
    (Fri.Spec.Witness F s d (0 : Fin (k + 2)))
    (batchSpec S) where
  prover := batchProver s d m G
  verifier := batchVerifier s m G

end BatchingRound

end Spec

end BatchedFri
