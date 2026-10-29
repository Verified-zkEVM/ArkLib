/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLibTest.ProofSystem.RingSwitching.Packing.RingSwitch.UnequalRankSuffix

/-!
# Two consecutive sumcheck rounds

A nonconstant four-variable source is packed over F₁₆/F₂, retaining two variables.
The fixture executes both rounds and the terminal check, preserving the two challenges in
order. Adding `X` to the second message makes its Boolean sum incorrect and aborts verification.
The oracle exposes the packed polynomial, as in the unequal-rank specification fixture.
-/

noncomputable section
namespace RingSwitching.Packing.Tests.TwoRounds
open Module MvPolynomial OracleSpec OracleComp ProtocolSpec Polynomial
open UnequalRankSuffix (data F16 codec bat)

/-- Pack two suffix variables and retain the two leading variables. -/
abbrev layout : ClaimLayout data 2 :=
  ClaimLayout.packedSuffixLayout data 2 2 (Equiv.refl _)

/-- A commitment oracle exposing the packed polynomial, with equality as compatibility. -/
def pc : PackedCommitment data.P 2 where
  ιC := Unit
  OStmt _ := data.P⦃≤ 1⦄[X Fin 2]
  Oᵢ _ := OracleInterface.instDefault
  commitsTo ost p := ost () = p

/-- The identity oracle constructor for the packed polynomial. -/
def honest : pc.Honest where
  commit p _ := p
  commitsTo_commit _ := rfl

/-- The multilinear source `X₀ + X₁X₂ + X₃`. -/
def source : layout.Source := ⟨X 0 + X 1 * X 2 + X 3, by
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro i
  apply (degreeOf_add_le i _ _).trans
  apply max_le _ (degreeOf_X_le i 3)
  apply (degreeOf_add_le i _ _).trans
  apply max_le (degreeOf_X_le i 0)
  apply (degreeOf_mul_le i _ _).trans
  fin_cases i <;> norm_num [degreeOf_X]⟩

/-- The retained point `(1, 0)` and suffix point `(0, 1)`. -/
def query : layout.Query := (![1, 0], ![0, 1])
/-- The packed component polynomial of `source`. -/
abbrev packed := data.packedMLE (layout.components source)
/-- The public product-sumcheck multiplier derived from the batching rule. -/
abbrev multiplier := Head.multiplier data 2 layout bat.toBatchingRule

/-- The nonconstant source and its commitment satisfy the original input relation. -/
theorem mem_relIn : (((query, layout.eval query source), honest.commit packed), source) ∈
    Head.relIn data 2 layout pc := Head.mem_relIn_commit data 2 layout pc honest _ _

/-- The state after the head reconstructs the source claim and samples `c`. -/
abbrev initial (c : bat.Challenge) := Head.nextStatement data 2 layout bat.toBatchingRule
  (query, layout.eval query source) (Head.partials data 2 layout query source) c
/-- The honest first-round polynomial at the initial state. -/
abbrev firstMessage (c : bat.Challenge) :=
  ProductSumcheck.Round.honestMessage multiplier (0 : Fin 2) (initial c) packed
/-- The state after the first round samples `z 0`. -/
abbrev middle (c : bat.Challenge) (z : Fin 2 → F16) :=
  ProductSumcheck.Round.nextStatement (0 : Fin 2) (initial c) (firstMessage c) (z 0)
/-- The honest second-round polynomial after sampling `z 0`. -/
abbrev secondMessage (c : bat.Challenge) (z : Fin 2 → F16) :=
  ProductSumcheck.Round.honestMessage multiplier (1 : Fin 2) (middle c z) packed
/-- The state after the two rounds sample `z 0` and `z 1`. -/
abbrev final (c : bat.Challenge) (z : Fin 2 → F16) :=
  ProductSumcheck.Round.nextStatement (1 : Fin 2) (middle c z) (secondMessage c z) (z 1)

/-- The initial, intermediate and final product-sumcheck states. -/
def statements (c : bat.Challenge) (z : Fin 2 → F16) :
    (i : Fin 3) → ProductSumcheck.Statement (layout.Query × bat.Challenge) F16 i
  | ⟨0, _⟩ => initial c
  | ⟨1, _⟩ => middle c z
  | ⟨2, _⟩ => final c z

/-- Both rounds preserve the product-sum relation of the same committed polynomial. -/
theorem mem_rel (c : bat.Challenge) (z : Fin 2 → F16) (i : Fin 3) :
    ((statements c z i, honest.commit packed), packed) ∈ ProductSumcheck.rel multiplier pc i := by
  have h₀ := Head.nextStatement_mem_relOut data 2 layout bat.toBatchingRule pc mem_relIn c
  have h₁ := ProductSumcheck.Round.nextStatement_mem_rel multiplier pc 0 h₀ (z 0)
  have h₂ := ProductSumcheck.Round.nextStatement_mem_rel multiplier pc 1 h₁ (z 1)
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂

/-- The two honest round polynomials paired with their sampled challenges. -/
def componentTranscript (c : bat.Challenge) (z : Fin 2 → F16) :
    Fin 2 → FullTranscript (ProductSumcheck.Round.pSpec F16)
  | ⟨0, _⟩ => FullTranscript.mk2 (firstMessage c) (z 0)
  | ⟨1, _⟩ => FullTranscript.mk2 (secondMessage c z) (z 1)

/-- Verification executes both rounds with the first round's target passed to the second. -/
theorem loop_accepts (c : bat.Challenge) (z : Fin 2 → F16) :
    (ProductSumcheck.loopVerifier (C := F16)
      (Context := layout.Query × bat.Challenge) pc).toVerifier.run
      (initial c, honest.commit packed) (FullTranscript.seqCompose (componentTranscript c z)) =
      pure (final c z, honest.commit packed) := by
  classical
  rw [ProductSumcheck.loopVerifier_toVerifier]
  apply Verifier.seqCompose_run_eq_pure _ _ _
    (fun i => (statements c z i, honest.commit packed))
  intro i
  fin_cases i
  · change (ProductSumcheck.Round.verifier pc 0).toVerifier.verify _ _ = _
    rw [ProductSumcheck.Round.verifier_verify]
    change (if ProductSumcheck.Round.check 0 (initial c) (firstMessage c) then
      pure (middle c z, honest.commit packed) else failure) = _
    have hc : ProductSumcheck.Round.check 0 (initial c) (firstMessage c) :=
      ProductSumcheck.Round.check_honestMessage_of_mem_rel multiplier pc 0 (mem_rel c z 0)
    rw [ite_eq_left hc]
    rfl
  · change (ProductSumcheck.Round.verifier pc 1).toVerifier.verify _ _ = _
    rw [ProductSumcheck.Round.verifier_verify]
    change (if ProductSumcheck.Round.check 1 (middle c z) (secondMessage c z) then
      pure (final c z, honest.commit packed) else failure) = _
    have hc : ProductSumcheck.Round.check 1 (middle c z) (secondMessage c z) :=
      ProductSumcheck.Round.check_honestMessage_of_mem_rel multiplier pc 1 (mem_rel c z 1)
    rw [ite_eq_left hc]
    rfl

/-- The packed polynomial evaluated at the two sampled coordinates. -/
abbrev finalValue (c : bat.Challenge) (z : Fin 2 → F16) :=
  aeval (final c z).challenges packed.val

/-- The head, two sumcheck rounds and terminal message in protocol order. -/
def transcript (c : bat.Challenge) (z : Fin 2 → F16) :
    FullTranscript (RingSwitch.pSpec (M := data.ιP → data.E) data 2 bat.toBatchingRule) :=
  FullTranscript.mk2 (Head.partials data 2 layout query source) c ++ₜ
    (FullTranscript.seqCompose (componentTranscript c z) ++ₜ
      ProductSumcheck.Terminal.transcript (finalValue c z))

/-- The complete verifier accepts and retains the two sampled coordinates in their order. -/
theorem full_accepts (c : bat.Challenge) (z : Fin 2 → F16) :
    (RingSwitch.verifier data 2 layout codec bat.toBatchingRule pc).toVerifier.run
      ((query, layout.eval query source), honest.commit packed) (transcript c z) =
      pure (((query, c), ((final c z).challenges, finalValue c z)), honest.commit packed) := by
  classical
  have hhead : (Head.verifier data 2 layout codec bat.toBatchingRule pc).toVerifier.run
      ((query, layout.eval query source), honest.commit packed)
      (FullTranscript.mk2 (Head.partials data 2 layout query source) c) =
        pure (initial c, honest.commit packed) := by
    change (Head.verifier data 2 layout codec bat.toBatchingRule pc).toVerifier.verify _ _ = _
    rw [(Head.guardedForm data 2 layout codec bat.toBatchingRule pc).verify_eq]
    change (if decide (Head.check data 2 layout (query, layout.eval query source)
      (Head.partials data 2 layout query source)) then _ else _) = _
    rw [decide_eq_true (Head.check_partials_of_mem_relIn data 2 layout pc mem_relIn)]
    rfl
  have hterminal : (ProductSumcheck.Terminal.verifier multiplier pc).toVerifier.run
      (final c z, honest.commit packed)
      (ProductSumcheck.Terminal.transcript (finalValue c z)) =
        pure (((query, c), ((final c z).challenges, finalValue c z)), honest.commit packed) := by
    change (ProductSumcheck.Terminal.verifier multiplier pc).toVerifier.verify _ _ = _
    rw [ProductSumcheck.Terminal.verifier_verify]
    change (if ProductSumcheck.Terminal.check multiplier (final c z) (finalValue c z) then
      _ else _) = _
    have hc : ProductSumcheck.Terminal.check multiplier (final c z) (finalValue c z) :=
      ProductSumcheck.Terminal.check_aeval_of_mem_rel multiplier pc (mem_rel c z 2)
    rw [ite_eq_left hc]
    rfl
  rw [RingSwitch.verifier_toVerifier]
  erw [Verifier.append_run]
  erw [transcript, FullTranscript.append_fst, FullTranscript.append_snd]
  rw [hhead, pure_bind, ProductSumcheck.verifier_toVerifier]
  erw [Verifier.append_run, FullTranscript.append_fst, FullTranscript.append_snd,
    loop_accepts, pure_bind, hterminal]

/-- The second round extends rather than overwrites the first sampled coordinate. -/
example (c : bat.Challenge) (z : Fin 2 → F16) : (final c z).challenges = z := by
  funext i
  fin_cases i <;> simp [final, middle, ProductSumcheck.Round.nextStatement, Fin.snoc]

/-- The two-round fixture has total challenge error `3/8`, strictly below one. -/
example : (∑ i, RingSwitch.rbrError (M := data.ιP → data.E) data 2 bat i) =
      (3 / 8 : NNReal) ∧
    (∑ i, RingSwitch.rbrError (M := data.ιP → data.E) data 2 bat i) < 1 := by
  have hc : Fintype.card F16 = 16 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 4 (by norm_num)]
    norm_num
  have hs : (∑ i, RingSwitch.rbrError (M := data.ιP → data.E) data 2 bat i) =
      (3 / 8 : NNReal) := by
    rw [RingSwitch.rbrError_sum]
    norm_num [bat, BatchingStrategy.gammaPowers, hc]
  exact ⟨hs, by rw [hs]; norm_num⟩

/-- The honest second polynomial corrupted by adding `X`. -/
def badMessage (c : bat.Challenge) (z : Fin 2 → F16) : F16⦃≤ 2⦄[X] :=
  secondMessage c z + ⟨Polynomial.X, Polynomial.mem_degreeLE.mpr (by simp)⟩

/-- Corrupting the second polynomial by `X` aborts the sumcheck round. -/
example (c : bat.Challenge) (z : Fin 2 → F16) :
    (ProductSumcheck.Round.verifier pc 1).toVerifier.verify
      (middle c z, honest.commit packed) (FullTranscript.mk2 (badMessage c z) (z 1)) =
      failure := by
  classical
  have hgood := ProductSumcheck.Round.check_honestMessage_of_mem_rel multiplier pc 1 (mem_rel c z 1)
  have hbad : ¬ ProductSumcheck.Round.check 1 (middle c z) (badMessage c z) := by
    intro h
    have hs : (secondMessage c z).val.eval 0 + (secondMessage c z).val.eval 1 =
        (middle c z).target := hgood
    have hb : (secondMessage c z).val.eval 0 + (secondMessage c z).val.eval 1 + 1 =
        (middle c z).target := by
      simpa only [ProductSumcheck.Round.check, badMessage, AddMemClass.coe_add,
        Polynomial.eval_add, Polynomial.eval_X, add_zero, add_assoc] using h
    rw [hs] at hb
    exact one_ne_zero (add_left_cancel (hb.trans (add_zero _).symm))
  rw [ProductSumcheck.Round.verifier_verify, ite_eq_right hbad]

end RingSwitching.Packing.Tests.TwoRounds
