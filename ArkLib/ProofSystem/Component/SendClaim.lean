/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # Simple Oracle Reduction - SendClaim

  The prover sends a claim to the verifier.

    - There is no witness (e.g. `Witness = Unit`), and there is a single `OStatement`.
   - The prover sends a message of the same type as `OStatement` to the verifier.
   - The verifier performs the check for `rel`, which can be expressed as an oracle computation.
   - The output data has no `Statement`, only two `OStatement`s: one from the beginning data,
     and the other is the message from the prover.
   - The output relation checks whether the two `OStatement`s are the same.

   TODO: Generalize
-/

open OracleSpec OracleComp OracleQuery OracleInterface ProtocolSpec

namespace SendClaim

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)
  {ιₛᵢ : Type} [Unique ιₛᵢ] (OStatement : ιₛᵢ → Type) [inst : ∀ i, OracleInterface (OStatement i)]

@[reducible]
def pSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[OStatement default]⟩

/--
The prover takes in the old oracle statement as input, and sends it as the protocol message.
-/
def oracleProver : OracleProver oSpec
    Statement OStatement Unit
    Unit (OStatement ⊕ᵥ OStatement) Unit
    (pSpec OStatement) where
  PrvState := fun _ => OStatement default

  input := fun ⟨⟨_, oStmt⟩, _⟩ => oStmt default

  sendMessage | ⟨0, _⟩ => fun st => pure (st, st)

  receiveChallenge | ⟨0, h⟩ => nomatch h

  output := fun st => pure
    (⟨(), fun x => match x with
      | .inl _ => by simpa [Unique.uniq] using st
      | .inr default => by simpa [Unique.uniq] using st⟩,
     ())

variable (relIn : Set ((Statement × (∀ i, OStatement i)) × Unit))
  (relComp : Statement → OracleComp [OStatement]ₒ Unit)
  -- (rel_eq : ∀ stmt oStmt, rel stmt oStmt ↔
  --   (OracleInterface.simOracle []ₒ (OracleInterface.oracle oStmt)).run = oStmt)

/--
The verifier checks that the relationship `rel oldStmt newStmt` holds.
It has access to the original and new `OStatement` via their oracle indices.
-/
def oracleVerifier : OracleVerifier oSpec Statement OStatement Unit (OStatement ⊕ᵥ OStatement)
    (pSpec OStatement) where

  verify := fun stmt _ => relComp stmt

  embed := {
    toFun := fun
      | .inl i => .inl i
      | .inr _ => .inr ⟨0, by simp⟩
    inj' := by
      intro a b h
      match a, b with
      | .inl _, .inl _ => simpa using h
      | .inl _, .inr _ => simp at h
      | .inr _, .inl _ => simp at h
      | .inr _, .inr _ => congr 1; exact Subsingleton.elim _ _
  }

  hEq := by
    intro i
    match i with
    | .inl _ => rfl
    | .inr j => simp [ProtocolSpec.Message]; exact congrArg OStatement (Unique.uniq _ j)

/--
Combine the prover and verifier into an oracle reduction.
The input has no statement or witness, but one `OStatement`.
The output is also no statement or witness, but two `OStatement`s.
-/
def oracleReduction : OracleReduction oSpec
      Statement OStatement Unit
      Unit (OStatement ⊕ᵥ OStatement) Unit (pSpec OStatement) where
  prover := oracleProver oSpec Statement OStatement
  verifier := oracleVerifier oSpec Statement OStatement relComp

def relOut : Set ((Unit × (∀ i, (Sum.elim OStatement OStatement) i)) × Unit) :=
  setOf (fun ⟨⟨(), oracles⟩, _⟩ => oracles (.inl default) = oracles (.inr default))

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/--
Proof of perfect completeness: if `rel old new` holds in the real setting,
it also holds in the ideal setting, etc.
-/
instance : ProverOnly (pSpec OStatement) where
  prover_first' := by simp

theorem completeness [Nonempty σ] :
    (oracleReduction oSpec Statement OStatement relComp).perfectCompleteness
    init impl relIn (relOut OStatement) := by
  simp only [OracleReduction.perfectCompleteness, oracleReduction, relOut]
  simp only [Reduction.perfectCompleteness_eq_prob_one]
  -- `relIn` membership is unused: SendClaim is a deterministic forwarding component
  -- whose computation succeeds unconditionally, independent of the input relation.
  intro ⟨stmt, oStmt⟩ wit _
  -- 1. Unfold (run_of_prover_first absorbs Verifier.run for P_to_V)
  simp only [OracleReduction.toReduction, Reduction.run_of_prover_first,
    oracleProver, oracleVerifier, OracleVerifier.toVerifier]
  -- 2. Bridge OptionT.pure → OracleComp.pure (some x) so simulateQ_pure fires
  simp_rw [show (pure : _ → OptionT (OracleComp _) _) = fun x => (pure (some x) :
    OracleComp _ _) from rfl]
  -- 3. Peel prover binds (all pure — erw matches through definitional eq)
  erw [simulateQ_bind]; erw [simulateQ_pure]; simp only [pure_bind]
  erw [simulateQ_bind]; erw [simulateQ_pure]; simp only [pure_bind]
  -- 4. Peel verifier bind
  erw [simulateQ_bind]
  -- 5. Probability decomposition via probEvent_eq_one_iff
  rw [probEvent_eq_one_iff]
  simp only [OptionT.probFailure_eq, OptionT.mem_support_iff, OptionT.run_mk]
  simp only [support_bind, Set.mem_iUnion]
  exact ⟨by {
    simp only [HasEvalPMF.probFailure_eq_zero, zero_add, probOutput_eq_zero_iff]
    intro h
    rw [mem_support_bind_iff] at h
    obtain ⟨s, -, hs⟩ := h
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hs
    obtain ⟨⟨_, s'⟩, hs, rfl⟩ := hs
    simp only [StateT.run_bind] at hs
    rw [mem_support_bind_iff] at hs
    obtain ⟨⟨x, s''⟩, hx, hs⟩ := hs
    -- Unfold SubSpec liftM + OptionT in hx
    simp only [MonadLift.monadLift, liftM, monadLift, MonadLiftT.monadLift,
      OptionT.run_mk, OptionT.run_bind, OptionT.run_lift] at hx
    -- simulateQ_map rewrites simulateQ impl (some <$> _) → some <$> simulateQ impl _
    erw [simulateQ_map] at hx
    -- Peel outer simulateQ layer (OptionT.mk is definitionally transparent)
    erw [simulateQ_map] at hx
    -- Bridge: StateT.run_map converts (some <$> m : StateT).run s to map at ProbComp level
    rw [StateT.run_map] at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨⟨val, s₀⟩, hval, heq⟩ := hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    -- x = some val, s'' = s₀; hs depends on val : Option (...)
    dsimp only [] at hs
    rcases val with _ | ⟨a⟩
    · exfalso
      simp only [bind_pure_comp] at hval
      erw [simulateQ_map] at hval
      erw [simulateQ_map] at hval
      erw [simulateQ_map] at hval
      erw [Option.elimM_map] at hval
      simp only [Option.elim_some] at hval
      dsimp only [OptionT.run] at hval
      simp only [bind_pure_comp] at hval
      rw [simulateQ_map, simulateQ_map] at hval
      rw [StateT.run_map] at hval
      simp only [support_map, Set.mem_image] at hval
      obtain ⟨⟨_, _⟩, _, h⟩ := hval
      simp [Prod.mk.injEq] at h
    · simp only [Option.getM, pure_bind] at hs
      erw [simulateQ_pure] at hs
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hs
      exact absurd (congr_arg Prod.fst hs) (by simp)
  }, by {
    -- Part 2: ∀ x ∈ support computation, event x
    intro x hx
    obtain ⟨s, -, hx⟩ := hx
    simp only [StateT.run'_eq, support_map, Set.mem_image] at hx
    obtain ⟨⟨xval, s'⟩, hx, rfl⟩ := hx
    simp only [StateT.run_bind] at hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨⟨y, s''⟩, hy, hx⟩ := hx
    -- Unfold SubSpec liftM + OptionT in hy
    simp only [MonadLift.monadLift, liftM, monadLift, MonadLiftT.monadLift,
      OptionT.run_mk, OptionT.run_bind, OptionT.run_lift] at hy
    -- simulateQ_map: y is always some _
    erw [simulateQ_map] at hy
    -- Peel outer simulateQ layer
    erw [simulateQ_map] at hy
    -- Bridge: StateT.run_map converts to ProbComp level map
    rw [StateT.run_map] at hy
    simp only [support_map, Set.mem_image] at hy
    obtain ⟨⟨val, s₀⟩, hval, heq⟩ := hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    -- y = some val; hx depends on val : Option (...)
    dsimp only [] at hx
    rcases val with _ | ⟨a⟩
    · exfalso
      simp only [bind_pure_comp] at hval
      erw [simulateQ_map] at hval
      erw [simulateQ_map] at hval
      erw [simulateQ_map] at hval
      erw [Option.elimM_map] at hval
      simp only [Option.elim_some] at hval
      dsimp only [OptionT.run] at hval
      simp only [bind_pure_comp] at hval
      rw [simulateQ_map, simulateQ_map] at hval
      rw [StateT.run_map] at hval
      simp only [support_map, Set.mem_image] at hval
      obtain ⟨⟨_, _⟩, _, h⟩ := hval
      simp [Prod.mk.injEq] at h
    · simp only [Option.getM, pure_bind] at hx
      erw [simulateQ_pure] at hx
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        Option.some.injEq] at hx
      obtain ⟨rfl, -⟩ := hx
      simp only [bind_pure_comp] at hval
      erw [simulateQ_map] at hval
      erw [simulateQ_map] at hval
      erw [simulateQ_map] at hval
      erw [Option.elimM_map] at hval
      simp only [Option.elim_some] at hval
      dsimp only [OptionT.run] at hval
      simp only [bind_pure_comp] at hval
      rw [simulateQ_map, simulateQ_map] at hval
      rw [StateT.run_map] at hval
      simp only [support_map, Set.mem_image, Prod.mk.injEq, Option.some.injEq] at hval
      obtain ⟨⟨_, _⟩, _, rfl, rfl⟩ := hval
      simp only [Set.mem_setOf_eq]
      refine ⟨trivial, Prod.ext (Subsingleton.elim _ _) ?_⟩
      funext i
      rcases i with j | j <;> {
        have hj : j = default := Unique.uniq _ j
        subst hj; rfl
      }
  }⟩

end SendClaim
