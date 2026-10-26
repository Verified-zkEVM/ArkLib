/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Protocol
public import ArkLib.ProofSystem.Logup.Prover.Strategy

/-!
# Honest tuple lookup with a supplied semantic index witness

The actual sender computes and casts one natural index histogram before the public fingerprint
challenge. Its beta response delegates to the unchanged weighted honest strategy on the compressed
Boolean values and those same retained base multiplicities. Fingerprint collisions cause no retry.

The message implementation remains explicit. A later measured default must select its actual
weighted drivers; this constructor alone makes no arithmetic, storage or machine-cost claim.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly
namespace Logup.Lookup.Tuple.Honest

variable {B E : Type} [CommRing B] [Field E]
variable {b W n M P ell : Nat} {schema : TaggedTuple.Schema B b W}
variable {layout : ProviderLayout b P}

/-- Send the base histogram once, then answer beta with the weighted honest continuation. -/
def proverWith (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    {ι : Type} (ambient : OracleSpec ι)
    (build : (r : Nat) → Logup.Prover.State E (M + P) ((M + P) ⌈/⌉ ell) (r + 1) →
      Sumcheck.Impl.Representation.Message E (ell + 2)) :
    Prover.Strategy ambient (protocol f n M P ell).tree (protocol f n M P ell).roles
      (fun _ => Unit) :=
  let mu := multiplicities (B := B) (n := n) (P := P) indices
  pure ⟨mu, fun beta => pure
    (Logup.Prover.Honest.honestWith (RingHom.id E) cfg.weighted
      (prepared.weightedData f beta mu) ambient build)⟩

end Logup.Lookup.Tuple.Honest
