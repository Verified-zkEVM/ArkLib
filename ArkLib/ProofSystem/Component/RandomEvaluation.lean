/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Component.RandomQuery

/-!
# Random evaluation

Polynomial identity testing as an instance of `RandomQuery`. The claim `P = 0`, for a
multivariate polynomial `P` in `m` variables determined by the statement and oracle statements,
is reduced to the claim `P(τ) = 0` at a uniform point `τ : Fin m → F`. Under the evaluation oracle
interface of `MvPolynomial`, this is `RandomQuery` comparing `f := P` with `g := 0`, with query
type `Fin m → F`. The definitions below are abbreviations of the `RandomQuery` ones; the protocol
stays computable even though polynomial evaluation is not.

`P` may be virtual: the verifier never evaluates or queries it. By Schwartz–Zippel, round-by-round
knowledge soundness has error `d / |F|` when every `P` has total degree at most `d`, and `m / |F|`
when every `P` is multilinear.

A zero-check over the Boolean hypercube (as in Spartan) is an instance: the hypercube identity is
rewritten as the vanishing of a polynomial, and this reduction tests that polynomial.
-/

@[expose] public section

open OracleComp OracleInterface MvPolynomial
open scoped NNReal ENNReal

namespace RandomEvaluation

/-- An evaluation query to a polynomial is answered by its value at the query point. -/
@[simp]
theorem answer_eq_eval {F : Type} [CommSemiring F] {m : ℕ} (P : MvPolynomial (Fin m) F)
    (τ : Query (MvPolynomial (Fin m) F)) : answer P τ = eval τ P := rfl

instance {F : Type} [CommSemiring F] [SampleableType F] {m : ℕ} :
    SampleableType (Query (MvPolynomial (Fin m) F)) :=
  inferInstanceAs (SampleableType (Fin m → F))

section Protocol

variable {ι : Type} (oSpec : OracleSpec ι) (F : Type) (m : ℕ) (Statement : Type) {κ : Type}
    (OStatement : κ → Type) [∀ i, OracleInterface (OStatement i)]

/-- One uniformly sampled point. -/
abbrev pSpec := RandomQuery.pSpec (Fin m → F)

/-- The prover retains the context and receives the point. -/
abbrev oracleProver := RandomQuery.oracleProver oSpec Statement OStatement (Fin m → F)

/-- The verifier forwards the point and retains every input oracle. -/
abbrev oracleVerifier := RandomQuery.oracleVerifier oSpec Statement OStatement (Fin m → F)

/-- The random-evaluation reduction. -/
abbrev oracleReduction := RandomQuery.oracleReduction oSpec Statement OStatement (Fin m → F)

/-- The verifier's always-true guard. -/
abbrev guardedForm := RandomQuery.guardedForm oSpec Statement OStatement (Fin m → F)

/-- The round-by-round extractor retains the unique witness. -/
abbrev rbrExtractor := RandomQuery.rbrExtractor oSpec Statement OStatement (Fin m → F)

variable [CommSemiring F] (P : Statement → (∀ i, OStatement i) → MvPolynomial (Fin m) F)

/-- The input relation: `P = 0`. -/
abbrev relIn := RandomQuery.relIn Statement OStatement (MvPolynomial (Fin m) F) P 0

/-- The output relation: `P` vanishes at the sampled point. -/
abbrev relOut := RandomQuery.relOut Statement OStatement (MvPolynomial (Fin m) F) P 0

omit [∀ i, OracleInterface (OStatement i)] in
theorem mem_relIn_iff {s : (Statement × (∀ i, OStatement i)) × Unit} :
    s ∈ relIn F m Statement OStatement P ↔ P s.1.1 s.1.2 = 0 := Iff.rfl

omit [∀ i, OracleInterface (OStatement i)] in
theorem mem_relOut_iff {s : (((Fin m → F) × Statement) × (∀ i, OStatement i)) × Unit} :
    s ∈ relOut F m Statement OStatement P ↔ eval s.1.1.1 (P s.1.1.2 s.1.2) = 0 := by
  change eval s.1.1.1 (P s.1.1.2 s.1.2) = eval s.1.1.1 (0 : MvPolynomial (Fin m) F) ↔ _
  rw [map_zero]

variable [SampleableType F] {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Perfect completeness: the zero polynomial vanishes everywhere. -/
theorem oracleReduction_completeness :
    (oracleReduction oSpec F m Statement OStatement).perfectCompleteness init impl
      (relIn F m Statement OStatement P) (relOut F m Statement OStatement P) :=
  RandomQuery.oracleReduction_completeness oSpec Statement OStatement
    (MvPolynomial (Fin m) F) P 0

/-- Before sampling, knowledge means `P = 0`; afterwards it means `P` vanishes at the point. -/
noncomputable abbrev knowledgeStateFunction :
    (oracleVerifier oSpec F m Statement OStatement).KnowledgeStateFunction init impl
      (relIn F m Statement OStatement P) (relOut F m Statement OStatement P)
      (rbrExtractor oSpec F m Statement OStatement) :=
  RandomQuery.knowledgeStateFunction oSpec Statement OStatement (MvPolynomial (Fin m) F) P 0

end Protocol

section Agreement

variable {F : Type} [Field F] [Fintype F] [SampleableType F] {m : ℕ}

/-- Schwartz–Zippel in the form `RandomQuery` uses: a nonzero polynomial of total degree at most
`d` agrees with `0` at a uniform evaluation point with probability at most `d / |F|`. -/
theorem prob_answer_eq_zero_le (Q : MvPolynomial (Fin m) F) (hQ : Q ≠ 0) (d : ℕ)
    (hd : Q.totalDegree ≤ d) :
    Pr{let τ ← $ᵗ Query (MvPolynomial (Fin m) F)}[answer Q τ = answer 0 τ] ≤
      ((d : ℝ≥0) / Fintype.card F : ℝ≥0) := by
  have hdenom : (Fintype.card F : ℝ≥0) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.coe_div hdenom]
  simp only [answer_eq_eval, map_zero, ENNReal.coe_natCast]
  exact prob_eval_zero_univ_le_div Q hQ hd

end Agreement

section Soundness

variable {ι : Type} (oSpec : OracleSpec ι) (F : Type) [Field F] [Fintype F] [SampleableType F]
    (m : ℕ) (Statement : Type) {κ : Type}
    (OStatement : κ → Type) [∀ i, OracleInterface (OStatement i)]
    (P : Statement → (∀ i, OStatement i) → MvPolynomial (Fin m) F)
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- Fixed-prefix knowledge soundness, with error `d / |F|` when every polynomial has total degree
at most `d`. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWith
    (d : ℕ) (hP : ∀ stmt oracles, (P stmt oracles).totalDegree ≤ d) :
    (oracleVerifier oSpec F m Statement OStatement).toVerifier.rbrKnowledgeSoundnessWith
      init impl (relIn F m Statement OStatement P) (relOut F m Statement OStatement P)
      (fun _ => Unit) (rbrExtractor oSpec F m Statement OStatement)
      (knowledgeStateFunction oSpec F m Statement OStatement P)
      (fun _ => (d : ℝ≥0) / Fintype.card F) :=
  RandomQuery.oracleVerifier_rbrKnowledgeSoundnessWith oSpec Statement OStatement
    (MvPolynomial (Fin m) F) P 0 _
    fun stmt oracles hP0 => prob_answer_eq_zero_le (P stmt oracles) hP0 d (hP stmt oracles)

/-- Fixed-prefix round-by-round knowledge soundness, with error `d / |F|`. -/
theorem oracleVerifier_rbrKnowledgeSoundness
    (d : ℕ) (hP : ∀ stmt oracles, (P stmt oracles).totalDegree ≤ d) :
    (oracleVerifier oSpec F m Statement OStatement).toVerifier.rbrKnowledgeSoundness
      init impl (relIn F m Statement OStatement P) (relOut F m Statement OStatement P)
      (fun _ => (d : ℝ≥0) / Fintype.card F) :=
  ⟨fun _ => Unit, rbrExtractor oSpec F m Statement OStatement,
    knowledgeStateFunction oSpec F m Statement OStatement P,
    oracleVerifier_rbrKnowledgeSoundnessWith oSpec F m Statement OStatement P d hP⟩

/-- The multilinear case of `oracleVerifier_rbrKnowledgeSoundnessWith`, with error
`m / |F|`. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWith_of_degreeOf_le_one
    (hP : ∀ stmt oracles i, degreeOf i (P stmt oracles) ≤ 1) :
    (oracleVerifier oSpec F m Statement OStatement).toVerifier.rbrKnowledgeSoundnessWith
      init impl (relIn F m Statement OStatement P) (relOut F m Statement OStatement P)
      (fun _ => Unit) (rbrExtractor oSpec F m Statement OStatement)
      (knowledgeStateFunction oSpec F m Statement OStatement P)
      (fun _ => (m : ℝ≥0) / Fintype.card F) :=
  oracleVerifier_rbrKnowledgeSoundnessWith oSpec F m Statement OStatement P m
    fun stmt oracles => by
      simpa using totalDegree_le_card_of_degreeOf_le_one _ (hP stmt oracles)

/-- The multilinear case of `oracleVerifier_rbrKnowledgeSoundness`, with error
`m / |F|`. -/
theorem oracleVerifier_rbrKnowledgeSoundness_of_degreeOf_le_one
    (hP : ∀ stmt oracles i, degreeOf i (P stmt oracles) ≤ 1) :
    (oracleVerifier oSpec F m Statement OStatement).toVerifier.rbrKnowledgeSoundness
      init impl (relIn F m Statement OStatement P) (relOut F m Statement OStatement P)
      (fun _ => (m : ℝ≥0) / Fintype.card F) :=
  ⟨fun _ => Unit, rbrExtractor oSpec F m Statement OStatement,
    knowledgeStateFunction oSpec F m Statement OStatement P,
    oracleVerifier_rbrKnowledgeSoundnessWith_of_degreeOf_le_one
      oSpec F m Statement OStatement P hP⟩

end Soundness

end RandomEvaluation
