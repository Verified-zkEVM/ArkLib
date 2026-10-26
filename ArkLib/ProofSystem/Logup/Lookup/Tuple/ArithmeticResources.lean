/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.ArithmeticResources
public import ArkLib.ProofSystem.Logup.Lookup.Tuple.ArithmeticProver
-- The resource proof unfolds the exact producer's private prefix, without changing its runtime.
import all ArkLib.ProofSystem.Logup.Lookup.Tuple.ArithmeticProver

/-!
# Resource corollaries for the actual cached tuple default

For N=2^n,T=M+P,D=TN, the actual cache program visits D(W+1) stored base coefficient cells and
PN retained base-multiplicity cells, with those same embedding sites. It has MN challenge-field
one sites, PN zero sites and PN actual subtraction requests, and stores D value and D weight
entries. Its guards/Horner/row sites are D(W+1), DW and D respectively. No E coefficient-row
buffer is built. The preceding histogram/cast dimensions are the shared scalar ones.

Weighted preparation on this cache uses 2D E identity visits, rather than further genuine B-to-E
embeddings. Existing metadata counts the designated cache sites, not opaque embeddings, Nat bit
complexity, getter/backend work, allocations or machine instructions. Provider preparation,
registry validation, public sampling and retained-message/storage work retain separate owners.
The exact cache request total is D(3W+3)+2MN+4PN; weighted terms are the existing actual observer
envelope. No new runtime, cost language, protocol or assumed execution equality is introduced.
-/

@[expose] public section
open Interaction.Oracle OracleComp OracleSpec CompPoly
namespace Logup.Lookup.Tuple.Honest.Accounting.Resources
variable {B E : Type} [CommRing B] [Field E] [DecidableEq E]
variable {b W n M P ell : Nat} {schema : TaggedTuple.Schema B b W}
variable {layout : ProviderLayout b P}

/-- The recorded actual prefix retains its actual histogram and the same materialized cache. -/
theorem observe_recordedProver_eq (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (beta alpha : E)
    (joint : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (choices : Vector (Option E) n) :
    observeProver ambient handler f (recordedProver f cfg prepared indices ambient)
        beta alpha joint choices =
      let mu := multiplicities (B := B) (n := n) (P := P) indices
      let cache := simulateQ arithmeticAnswer (compressedTablesProgram f prepared beta mu)
      (mu, Logup.Prover.Honest.Accounting.observeProver ambient handler
        (Logup.Prover.Honest.Accounting.proverWith
          Logup.Prover.Honest.Accounting.callInterpreter Logup.Prover.Honest.Accounting.call_erases
          (· ++ ·) [] (RingHom.id E) cfg.weighted (compressedData cache) ambient)
        alpha joint choices) := by
  rfl

/-- Every actual request coordinate adds its exact compression prefix to 1012NTell. -/
theorem observed_prover_cost_le (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (beta alpha : E)
    (joint : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (choices : Vector (Option E) n) (kind : ArithmeticCostKind) :
    (observeProver ambient handler f (profiledProver f cfg prepared indices ambient)
      beta alpha joint choices).2.2.2 kind ≤
      compressionCost n M P W kind + 1012 * 2 ^ n * (M + P) * ell := by
  rw [observe_profiledProver_eq_compression_add_charges, observe_recordedProver_eq]
  exact Nat.add_le_add_left
    (Logup.Prover.Honest.Accounting.Resources.observed_prover_charges_le
      (RingHom.id E) cfg.weighted _ ambient handler alpha joint choices kind) _

/-- The exact sum of the cache's nine request coordinates includes all designated markers. -/
theorem compressionCost_total (n M P W : Nat) :
    ([ArithmeticCostKind.add, .sub, .mul, .inv, .eq, .coefficientRead, .nodeRead,
      .valueRead, .metadata].map (compressionCost n M P W)).sum =
      ((M + P) * 2 ^ n) * (3 * W + 3) + 2 * M * 2 ^ n + 4 * P * 2 ^ n := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, compressionCost]
  ring

/-- The actual nine-kind total has the exact cache prefix plus the weighted 9108NTell bound. -/
theorem observed_prover_total_cost_le (f : B →+* E) (cfg : Logup.Lookup.Config B n M P ell)
    (prepared : PreparedProvider schema layout n M)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n)) {ι : Type} (ambient : OracleSpec ι)
    (handler : QueryImpl ambient Id) (beta alpha : E)
    (joint : (Fin n → E) × (Fin ((M + P) ⌈/⌉ ell) → E))
    (choices : Vector (Option E) n) :
    let cost := (observeProver ambient handler f (profiledProver f cfg prepared indices ambient)
      beta alpha joint choices).2.2.2
    ([ArithmeticCostKind.add, .sub, .mul, .inv, .eq, .coefficientRead, .nodeRead,
      .valueRead, .metadata].map cost).sum ≤
      ((M + P) * 2 ^ n) * (3 * W + 3) + 2 * M * 2 ^ n + 4 * P * 2 ^ n +
        9108 * 2 ^ n * (M + P) * ell := by
  dsimp only
  have h := observed_prover_cost_le f cfg prepared indices ambient handler beta alpha joint choices
  have ha := h .add
  have hs := h .sub
  have hm := h .mul
  have hi := h .inv
  have he := h .eq
  have hc := h .coefficientRead
  have hn := h .nodeRead
  have hv := h .valueRead
  have ht := h .metadata
  have hp := compressionCost_total n M P W
  rw [show 9108 * 2 ^ n * (M + P) * ell = 9 * (1012 * 2 ^ n * (M + P) * ell) by ring]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hp ⊢
  omega

end Logup.Lookup.Tuple.Honest.Accounting.Resources
