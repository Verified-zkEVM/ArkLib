/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Commitment
public import ArkLib.ProofSystem.Binius.BinaryBasefold.General
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations.Initial
public import ArkLib.OracleReduction.Security.GuardedBridges
public import ArkLib.ProofSystem.Component.ReduceClaim
-- The strict initial relation exposes dependent fold-index proof terms.
import all ArkLib.ProofSystem.Binius.BinaryBasefold.Relations
-- The initial-fold identity unfolds the dependent fold implementation.
import all ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude.Folding

/-!
# Opening a product claim with Binary Basefold

The sum-check-and-fold loop starts from a product claim `s = ∑_{y ∈ {0,1}^ℓ} A(y) · t(y)`, for a
public multilinear multiplier `A` determined by the context and a committed multilinear `t`.
This file gives the canonical round-`0` witness of such a claim (its statement is
`Sumcheck.Structured.initialStatement`) and two facts about it:

* `sum_eq_and_firstOracleWitnessConsistent_of_mem_roundRelation_zero`: a relaxed round-`0` witness
  certifies the product claim for its own polynomial, together with unique-radius compatibility
  of that polynomial with the committed first oracle. Proximity is not upgraded to equality.
* `mem_strictRoundRelation_zero_initialWitness`: the product claim and an exact first encoding
  give the strict round-`0` relation used for perfect completeness.

`ProductClaim.openingVerifier` and `ProductClaim.openingReduction` then open such a claim: a
zero-message front end, the claim reduction `ReduceClaim.oracleReduction`, maps the input
statement to its context and target and builds the canonical witness, and the full Binary
Basefold protocol runs at the multiplier. The security theorems hold for any input relation
containing `ProductClaim.inputRelation` (round-by-round knowledge soundness) or contained in
`ProductClaim.strictInputRelation` (perfect completeness): the product claim with unique-radius
compatibility or with the exact encoding.

An evaluation claim `s = t(r)` is the product claim at `A = eq̃(r, ·)` (`Opening`); the unrolled
FRI-Binius protocol uses the ring-switching multiplier.

The front-end reduction is noncomputable because the canonical witness is: prefix fixing of the
residual polynomial and the folded codewords are noncomputable. The opening is noncomputable
because the Binary Basefold phases are.
-/

@[expose] public section

open OracleSpec OracleComp ProtocolSpec AdditiveNTT MvPolynomial Sumcheck.Structured

namespace Binius.BinaryBasefold

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K] [Fact (Fintype.card K = 2)] [Algebra K L]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
variable (β : Fin r → L) [Fact (LinearIndependent K β)]
variable {ℓ R : ℕ} [NeZero R] {h_rate : ℓ + R < r}
variable {Context : Type} (multpoly : Context → MultilinearPoly L ℓ)

/-- The canonical round-`0` witness of `t`: the residual polynomial is `A(ctx) · t` and the
folded word is the encoding of `t`. -/
noncomputable def initialWitness (ctx : Context) (t : MultilinearPoly L ℓ) :
    Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0 where
  t := t
  H := fixPrefix ℓ 0 (computeInitialSumcheckPoly ℓ t (multpoly ctx)) Fin.elim0
  f := getMidCodewords K β (h_ℓ_add_R_rate := h_rate) t Fin.elim0

/-- The initial residual polynomial is the multiplier times the committed polynomial. -/
theorem initialWitness_H_val (ctx : Context) (t : MultilinearPoly L ℓ) :
    (initialWitness K β multpoly (h_rate := h_rate) ctx t).H.val = (multpoly ctx).val * t.val := by
  simp [initialWitness, fixPrefix, MvPolynomial.fixFirstVariablesOfMQP_zero]

/-- The canonical witness satisfies the structural invariant of the loop, independently of the
committed oracle. -/
theorem initialWitness_structural (ctx : Context) (target : L) (t : MultilinearPoly L ℓ) :
    WitnessStructuralInvariant K β (multpoly := multpoly) (h_ℓ_add_R_rate := h_rate)
      (initialStatement ctx target) (initialWitness K β multpoly ctx t) :=
  ⟨rfl, rfl⟩

/-- Boolean sum-check consistency of the canonical witness is the product claim. -/
theorem sumcheckConsistencyProp_initialWitness_iff (ctx : Context) (target : L)
    (t : MultilinearPoly L ℓ) :
    sumcheckConsistencyProp (boolDomain L ℓ) target
      (initialWitness K β multpoly (h_rate := h_rate) ctx t).H ↔
      target = ∑ y : Fin ℓ → Fin 2,
        (multpoly ctx).val.eval (y : Fin ℓ → L) * t.val.eval (y : Fin ℓ → L) := by
  unfold sumcheckConsistencyProp
  rw [sum_cube_boolDomain]
  simp only [initialWitness_H_val, eval_mul]

variable [Fact (β 0 = 1)] [NeZero ℓ] {ϑ : ℕ} [NeZero ϑ] [Fact (ϑ ∣ ℓ)]

/-- A relaxed round-`0` witness certifies the product claim for its own polynomial and the
unique-radius compatibility of that polynomial with the committed first oracle. -/
theorem sum_eq_and_firstOracleWitnessConsistent_of_mem_roundRelation_zero
    (ctx : Context) (target : L)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)
    (w : Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0)
    (h : ((initialStatement ctx target, ost), w) ∈
      roundRelation (multpoly := multpoly) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0) :
    target = ∑ y : Fin ℓ → Fin 2,
        (multpoly ctx).val.eval (y : Fin ℓ → L) * w.t.val.eval (y : Fin ℓ → L) ∧
      FirstOracleWitnessConsistent K β w.t (getFirstOracle K β ost) := by
  rw [mem_roundRelation_zero_iff] at h
  obtain ⟨hsum, hstruct, hfirst, _⟩ := h
  have hH : w.H = (initialWitness K β multpoly (h_rate := h_rate) ctx w.t).H := hstruct.1
  rw [hH] at hsum
  exact ⟨(sumcheckConsistencyProp_initialWitness_iff K β multpoly ctx target w.t).mp hsum, hfirst⟩

omit [Fact (β 0 = 1)] in
-- The strict initial fold identity compares definitionally equal dependent domains.
set_option backward.isDefEq.respectTransparency false in
/-- The product claim and an exact first encoding give the strict round-`0` relation. -/
theorem mem_strictRoundRelation_zero_initialWitness
    (ctx : Context) (target : L) (t : MultilinearPoly L ℓ)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)
    (hs : target = ∑ y : Fin ℓ → Fin 2,
      (multpoly ctx).val.eval (y : Fin ℓ → L) * t.val.eval (y : Fin ℓ → L))
    (ho : getFirstOracle K β ost = firstOracleEncoding K β t) :
    ((initialStatement ctx target, ost), initialWitness K β multpoly ctx t) ∈
      strictRoundRelation (multpoly := multpoly) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0 := by
  classical
  dsimp only [strictRoundRelation, StrictRoundRelated, StrictOracleWitnessConsistent]
  refine ⟨(sumcheckConsistencyProp_initialWitness_iff K β multpoly ctx target t).mpr hs,
    initialWitness_structural K β multpoly ctx target t, ?_⟩
  change StrictOracleFoldingConsistent K β t (0 : Fin (ℓ + 1)) Fin.elim0 ost
  dsimp only [StrictOracleFoldingConsistent]
  rintro ⟨j, hj⟩
  have hj0 : j = 0 := Nat.lt_one_iff.mp
    (lt_of_lt_of_eq hj (toOutCodewordsCount_zero ℓ ϑ))
  subst j
  funext y
  rw [iteratedFold_congr_steps_index K β (h_ℓ_add_R_rate := h_rate) (steps' := 0)
    (h_destIdx := by simp only [Nat.zero_mod, Nat.zero_mul, Fin.coe_ofNat_eq_mod,
      Nat.zero_add])
    (h_destIdx_le := by simp only [Nat.zero_mul, Nat.zero_le])
    (h_steps_eq_steps' := by simp only [Nat.zero_mul])]
  rw [iteratedFold_zero_steps K β (h_ℓ_add_R_rate := h_rate) (i := 0)
    (h_destIdx := by simp only [Nat.zero_mod, Nat.zero_mul, Fin.coe_ofNat_eq_mod])]
  have hy := congrFun ho (cast (by simp only [Fin.mk_zero', Nat.zero_mul]) y)
  simpa [getFirstOracle, firstOracleEncoding] using hy

end Binius.BinaryBasefold

namespace Binius.BinaryBasefold.ProductClaim

open OracleSpec OracleComp ProtocolSpec AdditiveNTT MvPolynomial Sumcheck.Structured
open scoped NNReal

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Algebra K L]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
variable (β : Fin r → L) [Fact (LinearIndependent K β)] [Fact (β 0 = 1)]
variable {ℓ R ϑ : ℕ} [NeZero ℓ] [NeZero R] [NeZero ϑ] {h_rate : ℓ + R < r} [Fact (ϑ ∣ ℓ)]
variable {Context : Type} (multiplier : Multiplier Context L ℓ)
variable {StmtIn WitIn : Type} (toClaim : StmtIn → Context × L)
  (witnessEquiv : WitIn ≃ MultilinearPoly L ℓ)

/-! ## Relations -/

/-- The product claim of a statement for the polynomial of a witness, with that polynomial
unique-radius compatible with the first oracle. -/
def inputRelation : Set ((StmtIn × (∀ j, OracleStatement K β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_rate) 0 j)) × WitIn) :=
  { ⟨⟨s, ost⟩, w⟩ |
    (toClaim s).2 = ∑ y : Fin ℓ → Fin 2,
        (multiplier (toClaim s).1).val.eval (y : Fin ℓ → L) *
          (witnessEquiv w).val.eval (y : Fin ℓ → L) ∧
      FirstOracleWitnessConsistent K β (witnessEquiv w) (getFirstOracle K β ost) }

/-- The product claim of a statement for the polynomial of a witness, with the first oracle its
exact encoding. -/
def strictInputRelation : Set ((StmtIn × (∀ j, OracleStatement K β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_rate) 0 j)) × WitIn) :=
  { ⟨⟨s, ost⟩, w⟩ |
    (toClaim s).2 = ∑ y : Fin ℓ → Fin 2,
        (multiplier (toClaim s).1).val.eval (y : Fin ℓ → L) *
          (witnessEquiv w).val.eval (y : Fin ℓ → L) ∧
      getFirstOracle K β ost = firstOracleEncoding K β (witnessEquiv w) }

/-! ## Protocol definitions -/

/-- The front end is the zero-message claim reduction (`ReduceClaim.oracleReduction`): it maps a
statement to the initial statement of its claim and a witness to the canonical initial witness of
its polynomial, and leaves the oracles unchanged. -/
noncomputable def frontReduction := ReduceClaim.oracleReduction []ₒ
  (OStmtIn := OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0)
  (OStmtOut := OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0)
  (fun s : StmtIn => initialStatement (L := L) (ℓ := ℓ) (toClaim s).1 (toClaim s).2)
  (fun s w => initialWitness K β multiplier.polynomial (h_rate := h_rate) (toClaim s).1
    (witnessEquiv w))
  (Function.Embedding.refl _) (fun _ => rfl) (fun _ => HEq.rfl)

/-- The front-end verifier: it outputs the initial statement of the claim. -/
def frontVerifier := ReduceClaim.oracleVerifier []ₒ
  (OStmtIn := OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0)
  (OStmtOut := OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0)
  (fun s : StmtIn => initialStatement (L := L) (ℓ := ℓ) (toClaim s).1 (toClaim s).2)
  (Function.Embedding.refl _) (fun _ => rfl) (fun _ => HEq.rfl)

/-- The front-end verifier always accepts. -/
def frontGuard :
    (frontVerifier K β toClaim (ϑ := ϑ) (h_rate := h_rate)).toVerifier.GuardedForm :=
  ReduceClaim.oracleVerifierGuardedForm []ₒ _ _ _ _

instance instMessageInterface (γ : ℕ) : ∀ j, OracleInterface
    (((!p[] : ProtocolSpec 0) ++ₚ fullPSpec K β γ (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate)).Message j) :=
  instOracleInterfaceMessageAppend

noncomputable instance instChallengeSampleable (γ : ℕ) : ∀ j, SampleableType
    (((!p[] : ProtocolSpec 0) ++ₚ fullPSpec K β γ (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate)).Challenge j) :=
  instSampleableTypeChallengeAppend

/-- The front end followed by the full Binary Basefold verifier at `multiplier`. -/
noncomputable def openingVerifier (γ : ℕ) := OracleVerifier.append
  (Stmt₃ := Bool) (OStmt₃ := fun _ : Empty => Unit)
  (Oₛ₃ := fun i : Empty => nomatch i)
  (frontVerifier K β toClaim (ϑ := ϑ) (h_rate := h_rate))
  (FullBinaryBasefold.fullOracleVerifier K β multiplier γ (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L))

/-- The honest front end followed by the full Binary Basefold reduction at `multiplier`. -/
noncomputable def openingReduction (γ : ℕ) := OracleReduction.append
  (Stmt₃ := Bool) (Wit₃ := Unit) (OStmt₃ := fun _ : Empty => Unit)
  (Oₛ₃ := fun i : Empty => nomatch i)
  (frontReduction K β multiplier toClaim witnessEquiv (ϑ := ϑ) (h_rate := h_rate))
  (FullBinaryBasefold.fullOracleReduction K β multiplier γ (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L))

/-- The Binary Basefold challenge errors, with no error for the front end. -/
noncomputable def openingError (γ : ℕ)
    (j : ((!p[] : ProtocolSpec 0) ++ₚ fullPSpec K β γ (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate)).ChallengeIdx) : ℝ≥0 :=
  Sum.elim (fun _ => 0)
    (FullBinaryBasefold.fullRbrKnowledgeError K β γ (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_rate)) (ChallengeIdx.sumEquiv.symm j)

/-! ## Security -/

omit [SampleableType L] [DecidableEq K] [Fact (β 0 = 1)] in
/-- The opening's challenge-error sum is at most the Binary Basefold bound. -/
theorem openingError_sum_le_concrete (γ : ℕ) :
    (∑ j, openingError K β γ (ϑ := ϑ) (h_rate := h_rate) j) ≤
      FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ R γ := by
  classical
  let f : ((!p[] : ProtocolSpec 0).ChallengeIdx ⊕
      (fullPSpec K β γ (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate)).ChallengeIdx) → ℝ≥0 :=
    Sum.elim (fun _ => 0)
      (FullBinaryBasefold.fullRbrKnowledgeError K β γ (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate))
  change (∑ j, f (ChallengeIdx.sumEquiv.symm j)) ≤ _
  rw [Equiv.sum_comp (e := ChallengeIdx.sumEquiv.symm) (g := f), Fintype.sum_sum_type]
  simp only [f, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero, zero_add]
  exact FullBinaryBasefold.fullRbrKnowledgeError_sum_le_concrete K β γ

variable (relIn : Set ((StmtIn × (∀ j, OracleStatement K β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_rate) 0 j)) × WitIn))

/-! ### Round-by-round knowledge soundness -/

omit [SampleableType L] [DecidableEq K] in
/-- A relaxed round-`0` witness for the claim of `s` yields a witness of any relation containing
`inputRelation`. -/
theorem mem_of_mem_roundRelation_zero
    (hrel : inputRelation K β multiplier toClaim witnessEquiv (ϑ := ϑ) (h_rate := h_rate) ⊆ relIn)
    (s : StmtIn) (ost : (∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j))
    (w : Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0)
    (h : ((initialStatement (toClaim s).1 (toClaim s).2, ost), w) ∈
      roundRelation (multpoly := multiplier.polynomial) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0) :
    ((s, ost), witnessEquiv.symm w.t) ∈ relIn := by
  obtain ⟨hsum, hfirst⟩ := sum_eq_and_firstOracleWitnessConsistent_of_mem_roundRelation_zero K β
    multiplier.polynomial (toClaim s).1 (toClaim s).2 ost w h
  apply hrel
  change _ = _ ∧ _
  rw [Equiv.apply_symm_apply]
  exact ⟨hsum, hfirst⟩

omit [SampleableType L] [DecidableEq K] in
/-- The front end is round-by-round knowledge sound, with no error, at the claim reduction's
extractor and knowledge-state function, for any input relation containing `inputRelation`. -/
theorem frontVerifier_rbrKnowledgeSoundnessWith {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (hrel : inputRelation K β multiplier toClaim witnessEquiv (ϑ := ϑ) (h_rate := h_rate) ⊆
      relIn) :
    (frontVerifier K β toClaim (ϑ := ϑ) (h_rate := h_rate)).toVerifier.rbrKnowledgeSoundnessWith
      init impl relIn
      (roundRelation (multpoly := multiplier.polynomial) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0)
      (fun _ => WitIn) (ReduceClaim.extractor (fun _ w => witnessEquiv.symm w.t))
      (ReduceClaim.oracleKnowledgeStateFunction relIn _
        (mem_of_mem_roundRelation_zero K β multiplier toClaim witnessEquiv relIn hrel)) 0 :=
  ReduceClaim.oracleVerifier_rbrKnowledgeSoundnessWith relIn _ _

/-- The opening is round-by-round knowledge sound, with the errors `openingError`, for any input
relation containing `inputRelation`. -/
theorem openingVerifier_rbrKnowledgeSoundness (γ : ℕ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (hrel : inputRelation K β multiplier toClaim witnessEquiv (ϑ := ϑ) (h_rate := h_rate) ⊆
      relIn) :
    Verifier.rbrKnowledgeSoundness init impl relIn acceptRejectOracleRel
      ((openingVerifier K β multiplier toClaim γ (ϑ := ϑ) (h_rate := h_rate)).toVerifier
        (Oₛₒ := fun i : Empty => nomatch i))
      (openingError K β γ (ϑ := ϑ) (h_rate := h_rate)) :=
  OracleVerifier.append_rbrKnowledgeSoundness_of_guarded_first
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (frontGuard K β toClaim)
    ((Verifier.rbrKnowledgeSoundness_iff_exists_with init impl _ _ _ _).mpr
      ⟨_, _, _, frontVerifier_rbrKnowledgeSoundnessWith K β multiplier toClaim witnessEquiv relIn
        init impl hrel⟩)
    (FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness K β multiplier γ
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L))

/-- The opening is knowledge sound at the Binary Basefold bound, with an unbounded extractor, for
any input relation containing `inputRelation`. -/
theorem openingVerifier_knowledgeSoundness (γ : ℕ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (hrel : inputRelation K β multiplier toClaim witnessEquiv (ϑ := ϑ) (h_rate := h_rate) ⊆
      relIn) :
    OracleProof.knowledgeSoundness init impl relIn
      (openingVerifier K β multiplier toClaim γ (ϑ := ϑ) (h_rate := h_rate))
      (FullBinaryBasefold.concreteBinaryBasefoldKnowledgeError L ℓ R γ) := by
  apply Verifier.knowledgeSoundness_error_mono init impl
    (openingError_sum_le_concrete K β γ (ϑ := ϑ) (h_rate := h_rate))
  exact Verifier.GuardedForm.knowledgeSoundness_of_rbrKnowledgeSoundness
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i : Empty => nomatch i)))
    (openingVerifier_rbrKnowledgeSoundness K β multiplier toClaim witnessEquiv relIn γ init impl
      hrel)

/-! ### Perfect completeness -/

omit [SampleableType L] [DecidableEq K] [Fact (β 0 = 1)] in
/-- The front end is perfectly complete for any input relation contained in
`strictInputRelation`. -/
theorem frontReduction_perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (hrel : relIn ⊆
      strictInputRelation K β multiplier toClaim witnessEquiv (ϑ := ϑ) (h_rate := h_rate)) :
    (frontReduction K β multiplier toClaim witnessEquiv (ϑ := ϑ)
      (h_rate := h_rate)).perfectCompleteness init impl relIn
      (strictRoundRelation (multpoly := multiplier.polynomial) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0) :=
  ReduceClaim.oracleReduction_completeness relIn _ fun s ost w hin => by
    obtain ⟨hs, ho⟩ := hrel hin
    exact mem_strictRoundRelation_zero_initialWitness K β multiplier.polynomial
      (toClaim s).1 (toClaim s).2 (witnessEquiv w) ost hs ho

/-- The opening is perfectly complete for any input relation contained in
`strictInputRelation`. -/
theorem openingReduction_perfectCompleteness (γ : ℕ) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (hrel : relIn ⊆
      strictInputRelation K β multiplier toClaim witnessEquiv (ϑ := ϑ) (h_rate := h_rate)) :
    OracleProof.perfectCompleteness
      (oracleProof := openingReduction K β multiplier toClaim witnessEquiv γ (ϑ := ϑ)
        (h_rate := h_rate))
      (relation := relIn) (init := init) (impl := impl) :=
  OracleReduction.append_perfectCompleteness_of_guarded_verifiers
    (Oₛ₃ := fun i : Empty => nomatch i) _ _
    (frontGuard K β toClaim)
    (Verifier.GuardedForm.ofEmpty _ (fun _ => (false, fun i => nomatch i)))
    (fun _ => Or.inl inferInstance)
    (frontReduction_perfectCompleteness K β multiplier toClaim witnessEquiv relIn init impl hrel)
    (fun st => FullBinaryBasefold.fullOracleReduction_perfectCompleteness K β multiplier γ
      (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L)
      (init := pure st) (impl := impl))

end Binius.BinaryBasefold.ProductClaim
