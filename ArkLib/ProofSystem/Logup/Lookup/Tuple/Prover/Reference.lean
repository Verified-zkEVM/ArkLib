/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Protocol
public import ArkLib.ProofSystem.Logup.Prover.Reference

/-!
# Honest tuple lookup with a supplied semantic index witness

The actual sender computes and casts one natural index histogram before the public fingerprint
challenge. Its beta response delegates to the weighted honest strategy on the compressed
Boolean values and those same retained base multiplicities. Fingerprint collisions cause no retry.

The message builder is explicit. Import `ArkLib.ProofSystem.Logup.Lookup.Tuple.Prover` for the
selected eager-cache `Honest.prover`; it specializes this reference construction. Completeness
lives in `Lookup/Tuple/Completeness.lean`, and cache/private arithmetic bounds in
`Lookup/Tuple/ArithmeticResources.lean`. This reference makes no resource bound itself.
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
