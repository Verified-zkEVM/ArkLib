/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness
public import ArkLib.OracleReduction.LiftContext.Reduction

/-!
# Purity and guardedness under context lifting

Context lenses map input and output values without oracle effects. Pure prover output and guarded
verifier forms therefore survive lifting without any new assumptions about the oracle state.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

variable {ι : Type} {spec : OracleSpec ι}
  {A B C D WA WB WC WD : Type} {n : ℕ} {p : ProtocolSpec n}

/-- Context lifting preserves pure prover output because the context lift is a pure function. -/
instance Prover.instOutputIsPureLiftContext (lens : Context.Lens A B C D WA WB WC WD)
    (P : Prover spec C WC D WD p) [h : P.OutputIsPure] :
    (P.liftContext lens).OutputIsPure := by
  obtain ⟨f, hf⟩ := h.output_is_pure
  refine ⟨fun st => lens.lift st.2 (f st.1), ?_⟩
  intro st
  simp only [Prover.liftContext, hf, pure_bind]

/-- Context lifting preserves the guard and maps only an accepted verifier verdict. -/
def Verifier.GuardedForm.liftContext (lens : Statement.Lens A B C D)
    (V : Verifier spec C D p) (G : V.GuardedForm) :
    (V.liftContext lens).GuardedForm where
  check := fun stmt tr => G.check (lens.proj stmt) tr
  out := fun stmt tr => lens.lift stmt (G.out (lens.proj stmt) tr)
  verify_eq := by
    intro stmt tr
    change (do
      let out ← V.verify (lens.proj stmt) tr
      pure (lens.lift stmt out)) =
      if G.check (lens.proj stmt) tr then
        pure (lens.lift stmt (G.out (lens.proj stmt) tr)) else failure
    rw [G.verify_eq]
    split <;> simp
