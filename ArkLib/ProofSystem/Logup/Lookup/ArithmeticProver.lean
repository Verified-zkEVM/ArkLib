/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Prover
public import ArkLib.ProofSystem.Logup.Prover.ArithmeticStrategy

/-!
# Default indexed scalar lookup prover

Compute and send the actual natural histogram once before alpha, then delegate to the weighted
strategy that explicitly executes the measured private programs. The supplied indices remain an
ordinary input; validity is a correctness premise rather than a runtime search or extraction.

Histogram natural-number work, casts, signed base weights and embeddings require separate
accounting from extension-field instruction profiles. Equality to the existing honest strategy
transfers correctness, not a resource claim for another implementation.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly
namespace Logup.Lookup.Honest

/-- Send the actual indexed multiplicities, then run the measured weighted default. -/
def prover {B E : Type} [CommRing B] [Field E] [DecidableEq E] {n M P ell : Nat}
    (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell) (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι) :
    Prover.Strategy ambient (Logup.Lookup.protocol f n M P ell).tree
      (Logup.Lookup.protocol f n M P ell).roles (fun _ => Unit) :=
  let mu := Logup.Lookup.multiplicities (B := B) (n := n) (P := P) indices
  pure ⟨mu, Logup.Prover.Honest.prover f cfg.weighted (Logup.Lookup.weightedData data mu) ambient⟩

/-- The default scalar ordinary strategy equals the existing explicit-builder correctness
strategy. -/
theorem prover_eq_proverWith {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n M P ell : Nat} (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι) :
    prover f cfg data indices ambient = proverWith f cfg data indices ambient
      (Logup.Prover.Honest.pureBuilder cfg.weighted.groups cfg.weighted.length_group_le) := by
  simp only [prover, proverWith, Logup.Prover.Honest.prover_eq_honestWith]
  rfl

end Logup.Lookup.Honest
