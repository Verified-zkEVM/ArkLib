/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Protocol
public import ArkLib.ProofSystem.Logup.Prover.Reference

/-!
# Honest scalar lookup with an explicit indexed witness

Compute the natural histogram once, cast it into the base field, and send the actual multiplicity
oracle before alpha. The continuation is the weighted honest strategy on the original
values and these signed weights. No witness is extracted or table membership searched at runtime.

The message builder is explicit. Import `ArkLib.ProofSystem.Logup.Lookup.Prover` for the
selected measured `Honest.prover`; it specializes this reference construction. Completeness
lives in `Lookup/Completeness.lean`, and private arithmetic bounds in `Lookup/ArithmeticResources`.
Correctness of the histogram alone does not establish an execution-cost bound.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly
namespace Logup.Lookup.Honest

/-- Send the actual indexed histogram before alpha, then delegate to the weighted honest prover. -/
def proverWith {B E : Type} [CommRing B] [Field E] {n M P ell : Nat}
    (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (data : Logup.Lookup.Data B n M P)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2)) :
    Prover.Strategy ambient (protocol f n M P ell).tree (protocol f n M P ell).roles
      (fun _ => Unit) :=
  let mu := multiplicities (B := B) (n := n) (P := P) indices
  pure ⟨mu, Logup.Prover.Honest.honestWith f cfg.weighted (weightedData data mu) ambient build⟩

end Logup.Lookup.Honest
